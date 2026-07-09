import FormalSnarksProject.Models.SymbolicAGMScheme
import FormalSnarksProject.SNARKs.Lipmaa.Defs

/-!
# Lipmaa, symbolically

This file represents the Lipmaa SNARK as a `SymbolicAGMScheme`, exactly as
`Groth16TypeIII/Symbolic.lean` does for Groth16: a closed term making no reference to any
concrete circuit polynomials, from which we obtain the abstract soundness ideal-membership
problem (`soundnessProblem`).

Lipmaa has the same shape as Type III Groth16 — proof elements `A`, `C` in `G1` and `B` in
`G2`, one verification equation with pairings `ab`, `αβ`, `stmtγ`, `cδ`, and the same
`x_pow`/`x_pow_times_t`/`y`/`q` SRS columns — but all the toxic-waste values are powers of the
single bounded sample `y` (`α = y⁷⁵`, `β = y²⁵`, `γ = y⁵`, `δ = y¹`, multiplied through by
`γδ = y⁶` as in `Lipmaa/Defs.lean`; the values below transcribe that file verbatim).
The target polynomial encodes the QAP relation with the witness extracted from proof element
`C`'s coefficients on the `q` component, matching the extractor of the manual proof in
`Lipmaa/Soundness.lean`.
-/

open scoped BigOperators

open CPoly CPoly.CMvPolynomial
open CompPoly

namespace Lipmaa

namespace Symbolic

/-- The size classes of Lipmaa (same as Groth16): statement size `n_stmt`, witness size `n_wit`,
number of variables `n_var`, and `n_var - 1` (the length of the `xⁱ·t` column). -/
inductive IdxClass : Type where
  | stmt : IdxClass
  | wit : IdxClass
  | var : IdxClass
  | varSub1 : IdxClass
deriving DecidableEq

/-- The abstract polynomial families: the QAP columns `u`, `v`, `w` (split into statement and
witness parts), the powers of `x`, and the powers of `x` times the vanishing polynomial `t`. -/
inductive PolyFam : Type where
  | u_stmt : PolyFam
  | v_stmt : PolyFam
  | w_stmt : PolyFam
  | u_wit : PolyFam
  | v_wit : PolyFam
  | w_wit : PolyFam
  | x_pows : PolyFam
  | x_pows_t : PolyFam
deriving DecidableEq

instance : FinEnum PolyFam :=
  .ofList [.u_stmt, .v_stmt, .w_stmt, .u_wit, .v_wit, .w_wit, .x_pows, .x_pows_t]
    (fun x => by cases x <;> simp)

/-- The size class of each family. -/
def famClass : PolyFam → IdxClass
  | .u_stmt => .stmt
  | .v_stmt => .stmt
  | .w_stmt => .stmt
  | .u_wit => .wit
  | .v_wit => .wit
  | .w_wit => .wit
  | .x_pows => .var
  | .x_pows_t => .varSub1

/-- The singleton `G1` SRS elements. -/
inductive SRSSingle_G1 : Type where
  | α : SRSSingle_G1
  | β : SRSSingle_G1
  | δ : SRSSingle_G1
deriving DecidableEq

instance : FinEnum SRSSingle_G1 := .ofList [.α, .β, .δ] (fun x => by cases x <;> simp)

/-- The singleton `G2` SRS elements. -/
inductive SRSSingle_G2 : Type where
  | β : SRSSingle_G2
  | γ : SRSSingle_G2
  | δ : SRSSingle_G2
deriving DecidableEq

instance : FinEnum SRSSingle_G2 := .ofList [.β, .γ, .δ] (fun x => by cases x <;> simp)

/-- The `Fin`-indexed `G1` SRS components. -/
inductive SRSComp_G1 : Type where
  | x_pow : SRSComp_G1
  | x_pow_times_t : SRSComp_G1
  | y : SRSComp_G1
  | q : SRSComp_G1
deriving DecidableEq

instance : FinEnum SRSComp_G1 :=
  .ofList [.x_pow, .x_pow_times_t, .y, .q] (fun x => by cases x <;> simp)

/-- The size class of each `G1` component. -/
def compClass_G1 : SRSComp_G1 → IdxClass
  | .x_pow => .var
  | .x_pow_times_t => .varSub1
  | .y => .stmt
  | .q => .wit

/-- The `Fin`-indexed `G2` SRS components. -/
inductive SRSComp_G2 : Type where
  | x_pow : SRSComp_G2
deriving DecidableEq

instance : FinEnum SRSComp_G2 := .ofList [.x_pow] (fun x => by cases x <;> simp)

/-- The size class of each `G2` component. -/
def compClass_G2 : SRSComp_G2 → IdxClass
  | .x_pow => .var

/-! ### Short `Repr` instances for readable output

Single-token ASCII names, so that the generic `Repr (SumVar 𝓢)` prints the abstract variables
as e.g. `comp_G1 C q u_wit`, and so that the SMT export's symbol sanitizer has nothing to do.
The proof-element index types live in `Defs.lean` (which only derives `DecidableEq`); we add
their `Repr` here to leave that file untouched. -/

instance : Repr Proof_G1_Idx := ⟨fun p _ => match p with | .A => "A" | .C => "C"⟩
instance : Repr Proof_G2_Idx := ⟨fun _ _ => "B"⟩

instance : Repr PolyFam := ⟨fun f _ => match f with
  | .u_stmt => "u_stmt" | .v_stmt => "v_stmt" | .w_stmt => "w_stmt"
  | .u_wit => "u_wit" | .v_wit => "v_wit" | .w_wit => "w_wit"
  | .x_pows => "x_pows" | .x_pows_t => "x_pows_t"⟩

instance : Repr SRSSingle_G1 := ⟨fun s _ => match s with
  | .α => "alpha" | .β => "beta" | .δ => "delta"⟩
instance : Repr SRSSingle_G2 := ⟨fun s _ => match s with
  | .β => "beta" | .γ => "gamma" | .δ => "delta"⟩

instance : Repr SRSComp_G1 := ⟨fun c _ => match c with
  | .x_pow => "x_pow" | .x_pow_times_t => "x_pow_times_t" | .y => "y" | .q => "q"⟩
instance : Repr SRSComp_G2 := ⟨fun c _ => match c with | .x_pow => "x_pow"⟩

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- Lipmaa as a symbolic scheme: a closed term, with no circuit polynomials in sight. The values
transcribe `Lipmaa/Defs.lean` exactly (they are already multiplied through by `γδ` there), with
every toxic-waste value a power of the single bounded sample `y`. -/
@[reducible] def scheme (F : Type) [Field F] [BEq F] [LawfulBEq F] :
    SymbolicAGMScheme F where
  Vars := Vars
  IdxClass := IdxClass
  stmtClass := .stmt
  PolyFams := PolyFam
  famClass := famClass
  SRSSingles_G1 := SRSSingle_G1
  SRSSingles_G2 := SRSSingle_G2
  SRSSingleValue_G1 := fun s => match s with
    | .α => X Vars.y ^ 81
    | .β => X Vars.y ^ 31
    | .δ => X Vars.y ^ 7
  SRSSingleValue_G2 := fun s => match s with
    | .β => X Vars.y ^ 31
    | .γ => X Vars.y ^ 11
    | .δ => X Vars.y ^ 7
  SRSComponents_G1 := SRSComp_G1
  SRSComponents_G2 := SRSComp_G2
  compClass_G1 := compClass_G1
  compClass_G2 := compClass_G2
  SRSComponentValue_G1 := fun c f => match c, f with
    | .x_pow, .x_pows => X Vars.y ^ 6
    | .x_pow_times_t, .x_pows_t => X Vars.y ^ 5
    | .y, .u_stmt => X Vars.y ^ 26
    | .y, .v_stmt => X Vars.y ^ 76
    | .y, .w_stmt => X Vars.y ^ 1
    | .q, .u_wit => X Vars.y ^ 30
    | .q, .v_wit => X Vars.y ^ 80
    | .q, .w_wit => X Vars.y ^ 5
    | _, _ => 0
  SRSComponentValue_G2 := fun c f => match c, f with
    | .x_pow, .x_pows => X Vars.y ^ 6
    | _, _ => 0
  Proof_G1 := Proof_G1_Idx
  Proof_G2 := Proof_G2_Idx
  EqualityChecks := Unit
  Pairings := fun _ => PairingsIdx
  Pairings_FinEnum := fun _ => inferInstance
  verifCoeffProof_G1 := fun _ i p => match i, p with
    | .ab, .A => 1
    | .cδ, .C => 1
    | _, _ => 0
  verifCoeffProof_G2 := fun _ i p => match i, p with
    | .ab, .B => -1
    | _, _ => 0
  verifCoeffSingle_G1 := fun _ i s => match i, s with
    | .αβ, .α => 1
    | _, _ => 0
  verifCoeffSingle_G2 := fun _ i s => match i, s with
    | .αβ, .β => 1
    | .stmtγ, .γ => 1
    | .cδ, .δ => 1
    | _, _ => 0
  verifCoeffComp_G1 := fun _ i c => match i, c with
    | .stmtγ, .y => some 1
    | _, _ => none
  verifCoeffComp_G2 := fun _ _ _ => none

open SymbolicAGMScheme

/-- The target polynomial of the soundness problem, over the abstract sum variables: the QAP
relation `(∑ aᵢuᵢ)·(∑ aᵢvᵢ) − ∑ aᵢwᵢ − h·t = 0` with the witness read off proof element `C`'s
coefficients on the `q` component and the quotient `h·t` read off `C`'s coefficients on the
`xⁱ·t` column — matching the extractor and the `suffices` step of the manual soundness proof. -/
def target (F : Type) [Field F] [BEq F] [LawfulBEq F] :
    CMvPolynomial (SumVar (scheme F)) F :=
  (X (SumVar.stmtSum PolyFam.u_stmt)
      + X (SumVar.comp_G1 Proof_G1_Idx.C SRSComp_G1.q PolyFam.u_wit))
    * (X (SumVar.stmtSum PolyFam.v_stmt)
      + X (SumVar.comp_G1 Proof_G1_Idx.C SRSComp_G1.q PolyFam.v_wit))
  - (X (SumVar.stmtSum PolyFam.w_stmt)
      + X (SumVar.comp_G1 Proof_G1_Idx.C SRSComp_G1.q PolyFam.w_wit))
  - X (SumVar.comp_G1 Proof_G1_Idx.C SRSComp_G1.x_pow_times_t PolyFam.x_pows_t)

/-- **The abstract soundness problem of Lipmaa**: a polynomial ideal-membership problem over the
sum variables, fully circuit-independent. Its generators are the toxic-waste coefficients of the
symbolic verification equation, its target the extracted QAP relation. Soundness of Lipmaa on
*every* circuit reduces to the target lying in the radical of the ideal spanned by the
generators (see `SymbolicAGMScheme.evalSums_target_eq_zero`). -/
def soundnessProblem (F : Type) [Field F] [BEq F] [LawfulBEq F] :
    AGMProofSystemInstantiation.IdealMembershipProblem (SumVar (scheme F)) F :=
  (scheme F).soundnessProblem (target F)

/-- Concrete circuit data (QAP polynomials and vanishing-polynomial roots) as an instantiation
of the symbolic scheme. `(scheme F).toAGMProofSystem (instantiation …)` is then the concrete
Lipmaa proof system for that circuit, corresponding to `Lipmaa` of `Defs.lean`. -/
def instantiation {n_stmt n_wit n_var : ℕ}
    (u_stmt : Fin n_stmt → CPolynomial F) (v_stmt : Fin n_stmt → CPolynomial F)
    (w_stmt : Fin n_stmt → CPolynomial F)
    (u_wit : Fin n_wit → CPolynomial F) (v_wit : Fin n_wit → CPolynomial F)
    (w_wit : Fin n_wit → CPolynomial F)
    (r : Fin n_wit → F) :
    (scheme F).Instantiation where
  classLen := fun c => match c with
    | .stmt => n_stmt
    | .wit => n_wit
    | .var => n_var
    | .varSub1 => n_var - 1
  famPolys := fun f => match f with
    | .u_stmt => u_stmt
    | .v_stmt => v_stmt
    | .w_stmt => w_stmt
    | .u_wit => u_wit
    | .v_wit => v_wit
    | .w_wit => w_wit
    | .x_pows => fun i => CPolynomial.X ^ (i : ℕ)
    | .x_pows_t => fun i => CPolynomial.X ^ (i : ℕ)
        * ∏ j ∈ (Finset.univ : Finset (Fin n_wit)), (CPolynomial.X - CPolynomial.C (r j))

end Symbolic

end Lipmaa
