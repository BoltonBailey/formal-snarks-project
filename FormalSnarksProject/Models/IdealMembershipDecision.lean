module

public import FormalSnarksProject.Models.SymbolicAGMScheme

/-!
# A computable decision procedure for the soundness ideal-membership problems

This file provides the "decides boolean true/false" half of the README goal of reformulating
the soundness-proving tactic as a computable non-meta function (the "outputs the ideal
membership test problem" half is `SymbolicAGMScheme.soundnessProblem` and the per-SNARK
`Symbolic.lean` files).

Given an `IdealMembershipProblem` (a `target` polynomial and a list of `generators`), soundness
reduces to the target lying in the **radical** of the ideal spanned by the generators, i.e. to
`∃ k, target ^ k ∈ span generators`. The pipeline here is *certificate-based*:

* `certifies k cofactors` — a computable `Bool` checking the polynomial identity
  `target ^ k = ∑ᵢ cofactorᵢ · generatorᵢ` (a plain ideal-membership certificate for
  `target ^ k`, hence a radical-membership certificate for `target`).
* `target_mem_radical_of_certifies` — the **verified bridge**: if the check returns `true` the
  target really lies in the radical, which is exactly the hypothesis
  `SymbolicAGMScheme.evalSums_target_eq_zero` consumes.
* `findCertificate` — a certificate *search*: fuelled multivariate division of `target ^ k`
  (for `k = 1, 2, …`) by the generator list, recording the quotients as cofactors. The search
  is unverified code, but any certificate it finds is re-checked by `certifies`, so
* `decideMembership` — the boolean decision — is **sound**: `true` answers carry a proof
  (`target_mem_radical_of_decideMembership`). A `false` answer means no certificate was found
  within the fuel; since plain reduction by a non-Gröbner basis is incomplete, `false` is *not*
  a disproof (completing the search with a Buchberger pass is future work).

The division uses the order already carried by the underlying monomial tree map
(lexicographic on exponent vectors), which is a monomial order, so reduction makes progress;
termination is nevertheless enforced by fuel, since none of this needs to be proven — only the
final certificate check is trusted, and that is verified.
-/

@[expose] public section

open CPoly CPoly.COrdMvPolynomial

namespace AGMProofSystemInstantiation

namespace IdealMembershipProblem

-- Polynomial equality is decided through the canonical (`Lawful`) representation; the
-- `DecidableEq F` this needs comes from the ambient `LawfulBEq F` (same registration as in
-- CompPoly's own files).
set_option allowUnsafeReducibility true in
attribute [local reducible] instDecidableEqOfLawfulBEq
attribute [local instance 5] instDecidableEqOfLawfulBEq

/-! ### The verified certificate check -/

/-- The linear combination `∑ᵢ cofactorᵢ · generatorᵢ` of a certificate (over any commutative
ring). -/
def certValue {R : Type} [CommRing R] (cofactors generators : List R) : R :=
  ((cofactors.zip generators).map fun cg => cg.1 * cg.2).sum

variable {V : Type} [FinEnum V] [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]
  {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- **The certificate check**: does `target ^ k = ∑ᵢ cofactorᵢ · generatorᵢ` hold? This is a
computable `Bool`; `target_mem_radical_of_certifies` is its soundness. -/
def certifies (prob : IdealMembershipProblem V F) (k : ℕ)
    (cofactors : List (COrdMvPolynomial V F)) : Bool :=
  decide (prob.target ^ k = certValue cofactors prob.generators)

/-- A `certValue` linear combination lies in the ideal spanned by the generators. -/
lemma certValue_mem_span {R : Type} [CommRing R] :
    (cofactors generators : List R) →
      certValue cofactors generators ∈ Ideal.span {g | g ∈ generators}
  | [], _ => by simp [certValue]
  | _ :: _, [] => by simp [certValue]
  | c :: cofactors, g :: generators => by
    rw [certValue, List.zip_cons_cons, List.map_cons, List.sum_cons]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · refine Ideal.span_mono (fun x hx => ?_) (certValue_mem_span cofactors generators)
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact List.mem_cons_of_mem _ hx

/-- **Soundness of the certificate check**: a passing certificate puts the target in the
radical of the generator ideal — the exact hypothesis of
`SymbolicAGMScheme.evalSums_target_eq_zero`. -/
theorem target_mem_radical_of_certifies (prob : IdealMembershipProblem V F) (k : ℕ)
    (cofactors : List (COrdMvPolynomial V F)) (h : prob.certifies k cofactors = true) :
    prob.target ∈ (Ideal.span {g | g ∈ prob.generators}).radical := by
  rw [certifies, decide_eq_true_eq] at h
  rw [Ideal.mem_radical_iff]
  exact ⟨k, h ▸ certValue_mem_span cofactors prob.generators⟩

/-! ### The certificate search (unverified, fuelled)

A fuelled Buchberger completion with *cofactor tracking*: every element of the working basis
carries its expression as a linear combination of the **original** generators, so a successful
reduction of `target ^ k` composes into a certificate over the original generators — which
`certifies` then re-checks. Nothing in this section is part of the trusted base. -/

/-- The total degree of a monomial. -/
def totalDegree (m : COrdMvMonomial V) : ℕ :=
  m.totalDegree

/-- Graded-reverse-lexicographic tiebreak on (reversed, i.e. descending-variable) entry lists:
at the largest variable where the exponents differ, the monomial with the *smaller* exponent is
the larger one. Canonical entry lists carry no zero exponents, so a variable present in only one
list is a differing variable with the other exponent `0`. -/
def grevlexTiebreak : List (V × ℕ) → List (V × ℕ) → Ordering
  | [], [] => .eq
  | _ :: _, [] => .lt
  | [], _ :: _ => .gt
  | (v₁, e₁) :: t₁, (v₂, e₂) :: t₂ =>
    match compare v₁ v₂ with
    | .lt => .gt -- largest differing variable is `v₂`, where `m₁` has exponent `0 < e₂`
    | .gt => .lt
    | .eq =>
      match compare e₂ e₁ with
      | .eq => grevlexTiebreak t₁ t₂
      | o => o
  termination_by l₁ l₂ => l₁.length + l₂.length

/-- Graded reverse lexicographic comparison of monomials — the standard order for Gröbner
basis computations (it tends to produce far smaller bases than the lexicographic order the
underlying tree map is keyed by). -/
def monomialCompare (m₁ m₂ : COrdMvMonomial V) : Ordering :=
  match compare (totalDegree m₁) (totalDegree m₂) with
  | .eq =>
    -- Same degree: entry lists are sorted ascending by variable, so walk them reversed.
    grevlexTiebreak m₁.entryList.reverse m₂.entryList.reverse
  | o => o

/-- The largest monomial of `p` in the grevlex order, or `none` for the zero polynomial. -/
def leadingMonomial (p : COrdMvPolynomial V F) : Option (COrdMvMonomial V) :=
  (OrdLawful.monomials p).foldl
    (fun acc m => match acc with
      | none => some m
      | some m' => if monomialCompare m' m = Ordering.lt then some m else some m')
    none

/-- Does the monomial `mg` divide the monomial `m` (componentwise `≤` on exponents)? -/
def monomialDivides (mg m : COrdMvMonomial V) : Bool :=
  COrdMvMonomial.divides mg m

/-- The quotient monomial `m / mg` (componentwise exponent subtraction; meaningful when
`monomialDivides mg m`). -/
def monomialQuot (m mg : COrdMvMonomial V) : COrdMvMonomial V :=
  m / mg

/-- The least common multiple of two monomials (componentwise `max` on exponents):
`e₁ + max (e₂ - e₁) 0 = max e₁ e₂`, using that monomial `/` truncates at zero. -/
def monomialLcm (m₁ m₂ : COrdMvMonomial V) : COrdMvMonomial V :=
  m₁ + m₂ / m₁

/-- Are two monomials coprime (no variable occurs in both)? Buchberger's first criterion:
the S-polynomial of two basis elements with coprime leading monomials reduces to zero.
Canonical entry lists carry no zero exponents, so it suffices that no variable of `m₁` occurs
in `m₂`. -/
def monomialCoprime (m₁ m₂ : COrdMvMonomial V) : Bool :=
  m₁.entryList.all fun ve => decide (m₂.degreeOf ve.1 = 0)

/-- An element of the working basis: a *monic* polynomial, its leading monomial, and its
expression as a linear combination of the original generators (`poly = ∑ᵢ cofᵢ · genᵢ`). -/
structure BasisElem (V F : Type) [Ord V] [Std.TransOrd V] [Zero F] where
  poly : COrdMvPolynomial V F
  lm : COrdMvMonomial V
  cof : List (COrdMvPolynomial V F)

/-- `a + q • b`, componentwise on cofactor vectors. -/
def cofAxpy (q : COrdMvPolynomial V F) (a b : List (COrdMvPolynomial V F)) :
    List (COrdMvPolynomial V F) :=
  List.zipWith (fun x y => x + q * y) a b

/-- Fuelled normal form of `p` modulo the basis, tracking cofactors: returns `(r, cof)` with
(when everything is in range of the fuel) `p = r + ∑ᵢ cofᵢ · genᵢ` and no monomial of `r`
divisible by a basis leading monomial. `cof₀` is the starting accumulator. -/
def normalForm (basis : Array (BasisElem V F)) :
    ℕ → COrdMvPolynomial V F → List (COrdMvPolynomial V F) →
      COrdMvPolynomial V F × List (COrdMvPolynomial V F)
  | 0, p, cof => (p, cof)
  | fuel + 1, p, cof =>
    match leadingMonomial p with
    | none => (p, cof)
    | some m =>
      match basis.findSome? (fun b => if monomialDivides b.lm m then some b else none) with
      | some b =>
        -- Basis elements are monic, so the quotient coefficient is just `p`'s coefficient.
        let q : COrdMvPolynomial V F := COrdMvPolynomial.monomial (monomialQuot m b.lm) (coeff m p)
        normalForm basis fuel (p - q * b.poly) (cofAxpy q cof b.cof)
      | none =>
        -- The leading term is irreducible: set it aside and continue below it.
        let lt : COrdMvPolynomial V F := COrdMvPolynomial.monomial m (coeff m p)
        let (r, cof') := normalForm basis fuel (p - lt) cof
        (r + lt, cof')

/-- Make a polynomial (paired with its cofactor vector) monic, and expose its leading
monomial; `none` for the zero polynomial. -/
def monicize (p : COrdMvPolynomial V F) (cof : List (COrdMvPolynomial V F)) :
    Option (BasisElem V F) :=
  match leadingMonomial p with
  | none => none
  | some m =>
    let c : COrdMvPolynomial V F := COrdMvPolynomial.C (coeff m p)⁻¹
    some ⟨c * p, m, cof.map (c * ·)⟩

/-- The pair queue entries for the S-polynomials of a new basis element against the existing
ones, tagged with the total degree of the lcm of the leading monomials (for the normal
selection strategy). Coprime-leading-monomial pairs are dropped (Buchberger's first
criterion). -/
def newPairs (basis : Array (BasisElem V F)) (b : BasisElem V F) (n : ℕ) :
    List (ℕ × ℕ × ℕ) :=
  basis.toList.zipIdx.filterMap fun bi =>
    if monomialCoprime bi.1.lm b.lm then none
    else some (totalDegree (monomialLcm bi.1.lm b.lm), bi.2, n)

/-- Fuelled Buchberger completion. Processes the pair queue smallest-lcm-degree-first (the
normal selection strategy), adding reduced S-polynomials (with their tracked cofactors) to
the basis; one unit of fuel per pair. -/
def buchberger : ℕ → Array (BasisElem V F) → List (ℕ × ℕ × ℕ) → Array (BasisElem V F)
  | 0, basis, _ => basis
  | _, basis, [] => basis
  | fuel + 1, basis, e :: rest =>
    let best := rest.foldl (fun acc x => if x.1 < acc.1 then x else acc) e
    let pairs := (e :: rest).erase best
    match basis[best.2.1]?, basis[best.2.2]? with
    | some bi, some bj =>
      let γ := monomialLcm bi.lm bj.lm
      let qi : COrdMvPolynomial V F := COrdMvPolynomial.monomial (monomialQuot γ bi.lm) 1
      let qj : COrdMvPolynomial V F := COrdMvPolynomial.monomial (monomialQuot γ bj.lm) 1
      let s := qi * bi.poly - qj * bj.poly
      let scof := cofAxpy (-qj) (cofAxpy qi (List.replicate bi.cof.length 0) bi.cof) bj.cof
      let (r, used) := normalForm basis fuel s (List.replicate bi.cof.length 0)
      -- `s = r + ∑ used·gen` and `s = ∑ scof·gen`, so `r = ∑ (scof − used)·gen`.
      match monicize r (List.zipWith (· - ·) scof used) with
      | none => buchberger fuel basis pairs
      | some b =>
        buchberger fuel (basis.push b) (pairs ++ newPairs basis b basis.size)
    | _, _ => buchberger fuel basis pairs

/-- The initial basis: the original generators, made monic, each carrying its unit cofactor
vector (scaled by the same normalization). -/
def initialBasis (generators : List (COrdMvPolynomial V F)) : Array (BasisElem V F) :=
  let n := generators.length
  (generators.zipIdx.filterMap fun gi =>
    monicize gi.1 ((List.range n).map fun i => if i = gi.2 then 1 else 0)).toArray

/-- Search for a radical-membership certificate: run the fuelled Buchberger completion once,
then try to reduce `target ^ k` to zero for `k = 1, …, maxPow`, composing the tracked
cofactors into a certificate over the original generators. -/
def findCertificate (prob : IdealMembershipProblem V F) (fuel maxPow : ℕ) :
    Option (ℕ × List (COrdMvPolynomial V F)) :=
  let basis₀ := initialBasis prob.generators
  let pairs := (List.range basis₀.size).flatMap fun j =>
    match basis₀[j]? with
    | none => []
    | some bj => newPairs (basis₀.take j) bj j
  let basis := buchberger fuel basis₀ pairs
  let zeros : List (COrdMvPolynomial V F) := List.replicate prob.generators.length 0
  (List.range maxPow).findSome? fun k =>
    let (r, cof) := normalForm basis fuel (prob.target ^ (k + 1)) zeros
    if (leadingMonomial r).isNone then some (k + 1, cof) else none

/-! ### The boolean decision -/

/-- **The soundness decision**: search for a certificate and re-check it. A `true` answer is
sound (`target_mem_radical_of_decideMembership`); a `false` answer means no certificate was
found within the fuel, which is *not* a disproof (the reduction-based search is incomplete
without a Gröbner-basis pass). -/
def decideMembership (prob : IdealMembershipProblem V F) (fuel maxPow : ℕ) : Bool :=
  match prob.findCertificate fuel maxPow with
  | some (k, cofactors) => prob.certifies k cofactors
  | none => false

/-- Soundness of the boolean decision. -/
theorem target_mem_radical_of_decideMembership (prob : IdealMembershipProblem V F)
    (fuel maxPow : ℕ) (h : prob.decideMembership fuel maxPow = true) :
    prob.target ∈ (Ideal.span {g | g ∈ prob.generators}).radical := by
  rw [decideMembership] at h
  split at h
  · exact prob.target_mem_radical_of_certifies _ _ h
  · exact absurd h (by simp)

end IdealMembershipProblem

end AGMProofSystemInstantiation

namespace SymbolicAGMScheme

open AGMProofSystemInstantiation

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- The end-to-end statement for a symbolic scheme: if the boolean decision accepts the
scheme's soundness problem, then (modulo the generic `ChecksImplyGenerators` bridge) the target
polynomial vanishes for every instance, statement and verifying AGM prover. -/
theorem evalSums_target_eq_zero_of_decideMembership (𝓢 : SymbolicAGMScheme F)
    (target : COrdMvPolynomial (SumVar 𝓢) F) (fuel maxPow : ℕ)
    (hdecide : (𝓢.soundnessProblem target).decideMembership fuel maxPow = true)
    (hbridge : 𝓢.ChecksImplyGenerators)
    (inst : 𝓢.Instantiation)
    (stmt : Fin (inst.classLen 𝓢.stmtClass) → F)
    (prover : AGMProofSystemInstantiation.Prover F (𝓢.toAGMProofSystem inst))
    (hverify : (𝓢.toAGMProofSystem inst).verify prover stmt) :
    𝓢.evalSumsHom (𝓢.sumValue inst stmt prover) target = 0 :=
  𝓢.evalSums_target_eq_zero target hbridge
    ((𝓢.soundnessProblem target).target_mem_radical_of_decideMembership fuel maxPow hdecide)
    inst stmt prover hverify

end SymbolicAGMScheme
