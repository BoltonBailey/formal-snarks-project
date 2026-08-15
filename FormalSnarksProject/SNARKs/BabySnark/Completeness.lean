module

public import FormalSnarksProject.SNARKs.BabySnark.Defs
public import FormalSnarksProject.ToMathlib.PolynomialDegreeHelpers

/-!

# BabySNARK Completeness

This file contains the completeness proof for BabySNARK; see `Defs.lean` for the definition and
an overview of the verifier's checks.

Writing `p = ∑ᵢ stmtᵢ · u_stmtᵢ + ∑ᵢ witᵢ · u_witᵢ` for the combined square span polynomial, the
honest prover encodes the witness part `p_wit = ∑ᵢ witᵢ · u_witᵢ` by its coefficients on the
`τ^0, …, τ^(n_var-1)` SRS elements of `V`, places the raw witness values on the `β·u_wit` slots
of `B` (so that `B = β · p_wit` exactly, satisfying check II), and encodes `h - t` on the
τ-power slots of `H`, where `h = (p² - 1) /ₘ t` is the square span quotient (check I reads
`(H + t)·t + 1 - (V + u_io)²`, so the `t²` term forces the `- t` offset). The same coefficients
are used in both groups, satisfying the three Type I identifications.

Completeness requires degree hypotheses making these truncated encodings faithful: all of `t`,
`u_stmt i`, `u_wit i` must have degree `< n_var`, and `n_var ≤ deg t + 1` so that the quotient
`h` (of degree `deg(p²) - deg t ≤ 2·(n_var - 1) - deg t`) also has degree `< n_var`.

-/

@[expose] public section

open scoped BigOperators

section BabySNARK

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace BabySNARK

section completeness

noncomputable def u_stmt_sum {F : Type} [Field F] [BEq F] [LawfulBEq F] {n_stmt : ℕ}
    (u_stmt : Fin n_stmt → CompPoly.CPolynomial F)
    (stmt : Fin n_stmt -> F) : CompPoly.CPolynomial F :=
  List.sum (List.map (fun j => CompPoly.CPolynomial.C (stmt j) * (u_stmt j)) (List.finRange n_stmt))

noncomputable def u_wit_sum {F : Type} [Field F] [BEq F] [LawfulBEq F] {n_wit : ℕ}
    (u_wit : Fin n_wit → CompPoly.CPolynomial F)
    (wit : Fin n_wit -> F) : CompPoly.CPolynomial F :=
  List.sum (List.map (fun j => CompPoly.CPolynomial.C (wit j) * (u_wit j)) (List.finRange n_wit))

noncomputable def wit_prover (F : Type) [Field F] [BEq F] [LawfulBEq F]
    (n_stmt n_wit n_var : ℕ)
    (u_stmt : Fin n_stmt → CompPoly.CPolynomial F)
    (u_wit : Fin n_wit → CompPoly.CPolynomial F)
    (t : CompPoly.CPolynomial F)
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F) :
    (BabySNARK (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
      (u_stmt := u_stmt) (u_wit := u_wit) (t := t)).Prover where
  fst pf_elem srs_elem := match pf_elem with
    | Proof_Idx.H => match srs_elem with
      | SRS_Elements_Idx.τ_pow i =>
        ((((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).divByMonic t) - t).coeff i
      | _ => 0
    | Proof_Idx.V => match srs_elem with
      | SRS_Elements_Idx.τ_pow i => (u_wit_sum u_wit wit).coeff i
      | _ => 0
    | Proof_Idx.B => match srs_elem with
      | SRS_Elements_Idx.βu i => wit i
      | _ => 0
  snd pf_elem srs_elem := match pf_elem with
    | Proof_Idx.H => match srs_elem with
      | SRS_Elements_Idx.τ_pow i =>
        ((((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).divByMonic t) - t).coeff i
      | _ => 0
    | Proof_Idx.V => match srs_elem with
      | SRS_Elements_Idx.τ_pow i => (u_wit_sum u_wit wit).coeff i
      | _ => 0
    | Proof_Idx.B => match srs_elem with
      | SRS_Elements_Idx.βu i => wit i
      | _ => 0

set_option maxHeartbeats 1000000 in
lemma is_complete
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {u_wit : Fin n_wit → CompPoly.CPolynomial F}
    {t : CompPoly.CPolynomial F}
    (tMonic : t.monic)
    -- Degree assumptions making the τ-power encodings faithful (see module docstring)
    (hnt : n_var ≤ t.toPoly.natDegree + 1)
    (hdeg_t : t.toPoly.degree < (n_var : WithBot ℕ))
    (hdeg_u_stmt : ∀ i, (u_stmt i).toPoly.degree < (n_var : WithBot ℕ))
    (hdeg_u_wit : ∀ i, (u_wit i).toPoly.degree < (n_var : WithBot ℕ)) :
    (completeness
      F
      (BabySNARK
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (t := t))
      (Fin n_wit -> F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        (((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * u_wit i) (List.finRange n_wit)))) ^ 2
          - 1
        ).modByMonic t = 0
      )
      (wit_prover F n_stmt n_wit n_var u_stmt u_wit t)
    ) := by
  unfold completeness verify check_poly pairing_poly proof_element_G1_as_poly
    proof_element_G2_as_poly wit_prover
  intros stmt wit hrel

  have hrel' : ((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).modByMonic t = 0 := hrel

  -- Bridge helpers: `CPoly.COrdMvPolynomial.ordPolyRingEquiv` (whose coercion is `CPoly.COrdMvPolynomial.fromCOrdMvPolynomial`) carries
  -- the computable `COrdMvPolynomial` verification equations over to mathlib's `MvPolynomial`.
  have equivC : ∀ c : F,
      (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) (CPoly.COrdMvPolynomial.C c) = C c :=
    fun c => CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_C c
  have equivX : ∀ v : Option Vars,
      (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) (CPoly.COrdMvPolynomial.X v) = X v :=
    fun v => CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_X v
  have equivOpt : ∀ p : CompPoly.CPolynomial F,
      (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) (to_COrdMvPolynomial_Option Vars p) =
        to_MvPolynomial_Option Vars p.toPoly :=
    fun p => fromCOrdMvPolynomial_to_COrdMvPolynomial_Option p

  -- `n_var` must be positive, since `t` is monic (hence nonzero) of degree `< n_var`
  have tP_monic : t.toPoly.Monic := (CompPoly.CPolynomial.monic_toPoly_iff t).mp tMonic
  have hpos : 0 < n_var := by
    by_contra h
    push_neg at h
    rw [Nat.le_zero] at h
    subst h
    rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, Polynomial.degree_eq_bot] at hdeg_t
    exact tP_monic.ne_zero hdeg_t

  -- `toPoly` expansions of the combined polynomials, and their degree bounds
  have stmt_sum_toPoly : (u_stmt_sum u_stmt stmt).toPoly
      = ((List.finRange n_stmt).map (fun j => Polynomial.C (stmt j) * (u_stmt j).toPoly)).sum := by
    unfold u_stmt_sum
    simp only [CompPoly.CPolynomial.toPoly_list_sum, List.map_map, Function.comp_def,
      CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.C_toPoly]
  have wit_sum_toPoly : (u_wit_sum u_wit wit).toPoly
      = ((List.finRange n_wit).map (fun j => Polynomial.C (wit j) * (u_wit j).toPoly)).sum := by
    unfold u_wit_sum
    simp only [CompPoly.CPolynomial.toPoly_list_sum, List.map_map, Function.comp_def,
      CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.C_toPoly]
  have hdeg_stmt_sum : (u_stmt_sum u_stmt stmt).toPoly.degree < (n_var : WithBot ℕ) := by
    rw [stmt_sum_toPoly]
    exact Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_u_stmt
  have hdeg_wit_sum : (u_wit_sum u_wit wit).toPoly.degree < (n_var : WithBot ℕ) := by
    rw [wit_sum_toPoly]
    exact Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_u_wit
  have hdeg_full : ((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit)).toPoly.degree
      < (n_var : WithBot ℕ) := by
    rw [CompPoly.CPolynomial.toPoly_add]
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hdeg_stmt_sum hdeg_wit_sum)

  -- The square span relation, transported to mathlib `Polynomial`
  have hmodP : ((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).toPoly %ₘ t.toPoly = 0 := by
    have h2 := congr_arg CompPoly.CPolynomial.toPoly hrel'
    rw [CompPoly.CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ tMonic,
      CompPoly.CPolynomial.toPoly_zero] at h2
    exact h2
  have hdivP : (((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).divByMonic t).toPoly
      = ((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).toPoly /ₘ t.toPoly := by
    rw [CompPoly.CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ tMonic]

  -- Degree bound for the quotient polynomial
  have hdeg_q : ((((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).divByMonic t).toPoly).degree
      < (n_var : WithBot ℕ) := by
    rw [hdivP]
    apply Polynomial.degree_divByMonic_lt_of_degree_lt tP_monic hmodP
    rw [Polynomial.degree_eq_natDegree tP_monic.ne_zero]
    have hsplit : n_var + t.toPoly.natDegree = (n_var - 1) + (t.toPoly.natDegree + 1) := by omega
    rw [← Nat.cast_add, hsplit, Nat.cast_add]
    rw [CompPoly.CPolynomial.toPoly_sub, CompPoly.CPolynomial.toPoly_pow,
      CompPoly.CPolynomial.toPoly_one, pow_two]
    exact Polynomial.degree_mul_sub_lt_of_degree_lt hdeg_full hdeg_full
      (by rw [Polynomial.degree_one]; exact_mod_cast hpos) hpos hnt

  -- Degree bound for the polynomial encoded on `H`'s τ-power slots
  have hdeg_qt : (((((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).divByMonic t) - t).toPoly).degree
      < (n_var : WithBot ℕ) := by
    rw [CompPoly.CPolynomial.toPoly_sub]
    exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hdeg_q hdeg_t)

  -- Truncation: a low-degree polynomial is recovered from its τ-power coefficients
  have trunc : ∀ (p : CompPoly.CPolynomial F) (n : ℕ), p.toPoly.degree < (n : WithBot ℕ) →
      ((List.finRange n).map (fun b : Fin n =>
          C (p.coeff (b : ℕ)) * X (none : Option Vars) ^ (b : ℕ))).sum
        = to_MvPolynomial_Option Vars p.toPoly := by
    intro p n hp
    have h1 := Polynomial.list_sum_C_coeff_mul_X_pow p.toPoly n hp
    have h2 := congr_arg (to_MvPolynomial_Option (F := F) Vars) h1
    rw [map_list_sum] at h2
    simp only [List.map_map, Function.comp_def, map_mul, map_pow, to_MvPolynomial_Option_C,
      to_MvPolynomial_Option_X, ← CompPoly.CPolynomial.coeff_toPoly] at h2
    exact h2

  -- Faithfulness of the verifier's τ-power encoding of the statement polynomial
  have hrep_uP : ((List.finRange n_var).map (fun x : Fin n_var =>
        ((List.finRange n_stmt).map (fun j =>
          Polynomial.C (stmt j) * Polynomial.C ((u_stmt j).coeff (x : ℕ)))).sum
            * Polynomial.X ^ (x : ℕ))).sum
      = (u_stmt_sum u_stmt stmt).toPoly := by
    rw [stmt_sum_toPoly]
    rw [← Fin.sum_univ_def, ← Fin.sum_univ_def]
    simp_rw [← Fin.sum_univ_def, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp_rw [mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [Fin.sum_univ_def]
    simp_rw [CompPoly.CPolynomial.coeff_toPoly]
    exact Polynomial.list_sum_C_coeff_mul_X_pow _ _ (hdeg_u_stmt j)
  have hrep_u := congr_arg (to_MvPolynomial_Option (F := F) Vars) hrep_uP
  rw [map_list_sum] at hrep_u
  simp only [List.map_map, Function.comp_def, map_mul, map_pow, map_list_sum,
    to_MvPolynomial_Option_C, to_MvPolynomial_Option_X] at hrep_u

  -- The verifier's `τ^0`-selector combination is the constant 1
  have hone : ((List.finRange n_var).map (fun x : Fin n_var =>
      (C (if (x : ℕ) = 0 then (1 : F) else 0) : MvPolynomial (Option Vars) F)
        * X (none : Option Vars) ^ (x : ℕ))).sum = 1 := by
    rw [← Fin.sum_univ_def]
    rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin n_var)]
    · simp
    · intro b _ hb
      have hb' : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [hb']
    · simp

  -- Splitting the `H`-slot polynomial into quotient and `t` parts
  have split_qt : to_MvPolynomial_Option Vars
        (((((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).divByMonic t) - t).toPoly)
      = to_MvPolynomial_Option Vars
          ((((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).divByMonic t).toPoly)
        - to_MvPolynomial_Option Vars t.toPoly := by
    rw [CompPoly.CPolynomial.toPoly_sub, map_sub]

  -- The division identity `h · t = p² - 1`, embedded into `MvPolynomial (Option Vars) F`
  have hkey : to_MvPolynomial_Option Vars
        ((((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).divByMonic t).toPoly)
        * to_MvPolynomial_Option Vars t.toPoly
      = (to_MvPolynomial_Option Vars (u_stmt_sum u_stmt stmt).toPoly
          + to_MvPolynomial_Option Vars (u_wit_sum u_wit wit).toPoly) ^ 2 - 1 := by
    have hdiv_id : t.toPoly *
        (((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).toPoly /ₘ t.toPoly)
        = ((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).toPoly := by
      have h := Polynomial.modByMonic_add_div
        ((u_stmt_sum u_stmt stmt + u_wit_sum u_wit wit) ^ 2 - 1).toPoly t.toPoly
      rwa [hmodP, zero_add] at h
    rw [hdivP, ← map_mul, mul_comm, hdiv_id, CompPoly.CPolynomial.toPoly_sub,
      CompPoly.CPolynomial.toPoly_pow, CompPoly.CPolynomial.toPoly_one,
      CompPoly.CPolynomial.toPoly_add, map_sub, map_pow, map_one, map_add]

  -- Expansion of the embedded witness combination into a per-index sum (for check II)
  have expand_wit : to_MvPolynomial_Option Vars (u_wit_sum u_wit wit).toPoly
      = ((List.finRange n_wit).map
          (fun x => C (wit x) * to_MvPolynomial_Option Vars (u_wit x).toPoly)).sum := by
    rw [wit_sum_toPoly]
    simp only [map_list_sum, List.map_map, Function.comp_def, map_mul, to_MvPolynomial_Option_C]

  -- Pull the negations (from the G2 side of the `vv` pairing) out of the list sums
  have neg_pull : ∀ {α : Type} (l : List α) (f : α → MvPolynomial (Option Vars) F),
      (l.map (fun x => -(f x))).sum = -(l.map f).sum := by
    intro α l f
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

  constructor
  · intro check_idx
    cases check_idx with
    | CheckI =>
      -- Expand the enumerations, transport to mathlib `MvPolynomial`, clean up and distribute
      simp only [toList_PairingsI_Idx, toList_PairingsII_Idx, toList_Proof_Idx,
        toList_SRS_Elements_Idx,
        List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
        List.sum_append_add_monoid, List.sum_cons, List.sum_nil]
      apply (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)).injective
      simp only [map_add, map_mul, map_neg, map_one, map_zero, map_pow, map_list_sum,
        List.map_map, Function.comp_def, equivC, equivX, equivOpt]
      simp only [List.sum_map_zero, mul_add, add_mul, List.sum_map_add,
        map_one, one_mul, map_zero, zero_mul, add_zero, map_neg, neg_mul, neg_add_rev,
        List.map_const', List.length_finRange, List.sum_replicate, smul_zero, mul_zero,
        zero_add]
      simp only [
        mul_assoc,
        mul_left_comm (C _) (X (some _)) _, mul_left_comm (List.sum _) (X (some _)) _,
        mul_comm (C _) (X (some _)), mul_comm (List.sum _) (X (some _)),
        neg_mul, mul_neg,
        List.sum_map_mul_right, List.sum_map_mul_left]
      -- Pull the negations (from the G2 side of the `vv` pairing) out of the list sums
      simp only [neg_pull]
      -- Rewrite the four τ-power encodings into embedded polynomials and close with the
      -- division identity
      rw [hrep_u, trunc t n_var hdeg_t, trunc _ n_var hdeg_qt, trunc _ n_var hdeg_wit_sum,
        split_qt, hone]
      linear_combination hkey
    | CheckII =>
      simp only [toList_PairingsI_Idx, toList_PairingsII_Idx, toList_Proof_Idx,
        toList_SRS_Elements_Idx,
        List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
        List.sum_append_add_monoid, List.sum_cons, List.sum_nil]
      apply (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)).injective
      simp only [map_add, map_mul, map_neg, map_one, map_zero, map_pow, map_list_sum,
        List.map_map, Function.comp_def, equivC, equivX, equivOpt]
      simp only [List.sum_map_zero, mul_add, add_mul, List.sum_map_add,
        map_one, one_mul, map_zero, zero_mul, add_zero, map_neg, neg_mul, neg_add_rev,
        List.map_const', List.length_finRange, List.sum_replicate, smul_zero, mul_zero,
        zero_add]
      simp only [
        mul_assoc,
        mul_left_comm (C _) (X (some _)) _, mul_left_comm (List.sum _) (X (some _)) _,
        mul_comm (C _) (X (some _)), mul_comm (List.sum _) (X (some _)),
        neg_mul, mul_neg,
        List.sum_map_mul_right, List.sum_map_mul_left]
      -- `B = β · p_wit` exactly; the `γβ·V` side is the truncated encoding of the same polynomial
      rw [trunc _ n_var hdeg_wit_sum, expand_wit]
      ring
  · -- The Type I identifications of `H`, `V`, `B`: the honest prover uses the same coefficients
    -- on both sides, and the two groups have identical SRS values
    intro pfs hpfs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpfs
    rcases hpfs with h | h | h <;> subst h <;>
      simp only [toList_SRS_Elements_Idx,
        List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
        List.sum_append_add_monoid, List.sum_cons, List.sum_nil]

end completeness

end BabySNARK

end BabySNARK
