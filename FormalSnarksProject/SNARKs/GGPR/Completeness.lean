/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import FormalSnarksProject.SNARKs.GGPR.Defs
public import FormalSnarksProject.ToMathlib.PolynomialDegreeHelpers

/-!

# GGPR Completeness

This file contains the completeness proof for the GGPR SNARK; see `Defs.lean` for the definition.

The honest prover places the witness coefficients on the `EK_v`/`EK_w` slots of `V_mid` and `W`
(and their α- and β-scaled copies on `V_mid'`, `W'`, `Y`), and the quotient
`h = (v·w) /ₘ t` on the `EK_s_pow` slots of `H` (α-scaled on `H'`). Checks II–V then hold as
exact polynomial identities; check I requires the quotient encoding on `s^0, …, s^(d-1)` to be
faithful, which is where the degree hypotheses enter: if all `v`-polynomials have degree `< a`,
all `w`-polynomials degree `< b`, and `a + b ≤ d + n_wit + 1`, then
`deg h ≤ deg(v·w) - deg t < d`.

-/

public section

open scoped BigOperators

section GGPR

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace GGPR

section completeness

noncomputable def v_sum {F : Type} [Field F] [BEq F] [LawfulBEq F] {n_stmt n_wit : ℕ}
    (v_0 : CompPoly.CPolynomial F)
    (v_stmt : Fin n_stmt → CompPoly.CPolynomial F)
    (v_wit : Fin n_wit → CompPoly.CPolynomial F)
    (stmt : Fin n_stmt -> F)
    (wit1 : Fin n_wit -> F)
    : CompPoly.CPolynomial F :=
  v_0
  + List.sum (List.map (fun j => CompPoly.CPolynomial.C (stmt j) * (v_stmt j)) (List.finRange n_stmt))
  + List.sum (List.map (fun j => CompPoly.CPolynomial.C (wit1 j) * (v_wit j)) (List.finRange n_wit))

noncomputable def w_sum {F : Type} [Field F] [BEq F] [LawfulBEq F] {m : ℕ}
    (w_0 : CompPoly.CPolynomial F)
    (w_wit : Fin m → CompPoly.CPolynomial F)
    (wit2 : Fin m -> F)
    : CompPoly.CPolynomial F :=
  w_0 + List.sum (List.map (fun j => CompPoly.CPolynomial.C (wit2 j) * (w_wit j)) (List.finRange m))

noncomputable def wit_prover (F : Type) [Field F] [BEq F] [LawfulBEq F]
    (n_stmt n_wit m d : ℕ)
    (v_stmt : Fin n_stmt → CompPoly.CPolynomial F)
    (v_wit : Fin n_wit → CompPoly.CPolynomial F)
    (w_wit : Fin m → CompPoly.CPolynomial F)
    (v_0 : CompPoly.CPolynomial F)
    (w_0 : CompPoly.CPolynomial F)
    (r : Fin (n_wit) → F)
    (stmt : Fin n_stmt -> F)
    (wit : (Fin n_wit -> F) × (Fin m → F)) :
    (GGPR
      (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (m := m) (d := d)
      (v_stmt := v_stmt) (v_wit := v_wit) (w_wit := w_wit)
      (v_0 := v_0) (w_0 := w_0) (r := r)).Prover where
  fst pf_elem srs_elem := match pf_elem with
    | Proof_G1_Idx.V_mid => match srs_elem with
      | SRS_Elements_Idx.EK_v i => wit.fst i
      | _ => 0
    | Proof_G1_Idx.V_mid' => match srs_elem with
      | SRS_Elements_Idx.EK_α_v i => wit.fst i
      | _ => 0
    | Proof_G1_Idx.W' => match srs_elem with
      | SRS_Elements_Idx.EK_α_w i => wit.snd i
      | _ => 0
    | Proof_G1_Idx.Y => match srs_elem with
      | SRS_Elements_Idx.EK_β_v i => wit.fst i
      | SRS_Elements_Idx.EK_β_w i => wit.snd i
      | _ => 0
    | Proof_G1_Idx.H' => match srs_elem with
      | SRS_Elements_Idx.EK_α_s_pow i =>
        let t : CompPoly.CPolynomial F := ∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
          (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
        (((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).divByMonic t).coeff i
      | _ => 0
  snd pf_elem srs_elem := match pf_elem with
    | Proof_G2_Idx.W => match srs_elem with
      | SRS_Elements_Idx.EK_w i => wit.snd i
      | _ => 0
    | Proof_G2_Idx.H => match srs_elem with
      | SRS_Elements_Idx.EK_s_pow i =>
        let t : CompPoly.CPolynomial F := ∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
          (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
        (((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).divByMonic t).coeff i
      | _ => 0

set_option maxHeartbeats 1000000 in
lemma is_complete
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit m d : ℕ}
    {v_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {v_wit : Fin n_wit → CompPoly.CPolynomial F}
    {w_wit : Fin m → CompPoly.CPolynomial F}
    {v_0 : CompPoly.CPolynomial F}
    {w_0 : CompPoly.CPolynomial F}
    {r : Fin (n_wit) → F}
    -- Degree assumptions making the quotient encoding on `s^0, …, s^(d-1)` faithful
    {a b : ℕ}
    (ha : 0 < a)
    (hab : a + b ≤ d + n_wit + 1)
    (hdeg_v_0 : v_0.toPoly.degree < (a : WithBot ℕ))
    (hdeg_v_stmt : ∀ i, (v_stmt i).toPoly.degree < (a : WithBot ℕ))
    (hdeg_v_wit : ∀ i, (v_wit i).toPoly.degree < (a : WithBot ℕ))
    (hdeg_w_0 : w_0.toPoly.degree < (b : WithBot ℕ))
    (hdeg_w_wit : ∀ i, (w_wit i).toPoly.degree < (b : WithBot ℕ)) :
    (completeness
      F
      (GGPR (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (m := m) (d := d)
        (v_stmt := v_stmt) (v_wit := v_wit) (w_wit := w_wit)
        (v_0 := v_0) (w_0 := w_0) (r := r))
      ((Fin n_wit → F) × (Fin m → F))
      (fun (stmt : Fin n_stmt → F) (wit : (Fin n_wit -> F) × (Fin m → F)) =>
        let t : CompPoly.CPolynomial F :=
          ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
        ((v_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit.fst i) * v_wit i) (List.finRange n_wit)))
          )
        *
          (w_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit.snd i) * w_wit i) (List.finRange m)))
          )
        ).modByMonic t = 0)
      (wit_prover F n_stmt n_wit m d v_stmt v_wit w_wit v_0 w_0 r)
    ) := by
  unfold completeness verify check_poly pairing_poly proof_element_G1_as_poly
    proof_element_G2_as_poly wit_prover
  intros stmt wit hrel

  -- Abbreviations for the combined polynomials and the vanishing polynomial
  have hrel' : ((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).modByMonic
      (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
        (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i))) = 0 := hrel

  -- Bridge helpers
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

  -- Facts about the vanishing polynomial
  have tC_monic : (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
      (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i))).monic :=
    CompPoly.CPolynomial.monic_prod_X_sub_C _ r
  have tP_eq : (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
      (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i))).toPoly
      = ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i)) := by
    simp only [CompPoly.CPolynomial.toPoly_prod, CompPoly.CPolynomial.toPoly_X_sub_C]
  have tP_monic : (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
      (Polynomial.X - Polynomial.C (r i))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (r i))
  have tP_degree : (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
      (Polynomial.X - Polynomial.C (r i))).degree = (n_wit : WithBot ℕ) := by
    rw [Polynomial.degree_prod]
    simp [Polynomial.degree_X_sub_C]

  -- `toPoly` expansions and degree bounds for the combined polynomials
  have vsum_toPoly : (v_sum v_0 v_stmt v_wit stmt wit.fst).toPoly
      = v_0.toPoly
        + ((List.finRange n_stmt).map (fun j => Polynomial.C (stmt j) * (v_stmt j).toPoly)).sum
        + ((List.finRange n_wit).map (fun j => Polynomial.C (wit.fst j) * (v_wit j).toPoly)).sum := by
    unfold v_sum
    simp only [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_list_sum,
      List.map_map, Function.comp_def, CompPoly.CPolynomial.toPoly_mul,
      CompPoly.CPolynomial.C_toPoly]
  have wsum_toPoly : (w_sum w_0 w_wit wit.snd).toPoly
      = w_0.toPoly
        + ((List.finRange m).map (fun j => Polynomial.C (wit.snd j) * (w_wit j).toPoly)).sum := by
    unfold w_sum
    simp only [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_list_sum,
      List.map_map, Function.comp_def, CompPoly.CPolynomial.toPoly_mul,
      CompPoly.CPolynomial.C_toPoly]
  have hdeg_vS : (v_sum v_0 v_stmt v_wit stmt wit.fst).toPoly.degree < (a : WithBot ℕ) := by
    rw [vsum_toPoly]
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt
        (lt_of_le_of_lt (Polynomial.degree_add_le _ _)
          (max_lt hdeg_v_0 (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_v_stmt)))
        (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_v_wit))
  have hdeg_wS : (w_sum w_0 w_wit wit.snd).toPoly.degree < (b : WithBot ℕ) := by
    rw [wsum_toPoly]
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt hdeg_w_0 (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_w_wit))

  -- The QAP relation, transported to mathlib `Polynomial`
  have hmodP : ((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).toPoly
      %ₘ (∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i))) = 0 := by
    have h2 := congr_arg CompPoly.CPolynomial.toPoly hrel'
    rw [CompPoly.CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ tC_monic, tP_eq,
      CompPoly.CPolynomial.toPoly_zero] at h2
    exact h2
  have hdivP : (((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).divByMonic
      (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
        (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)))).toPoly
      = ((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).toPoly
          /ₘ (∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i))) := by
    rw [CompPoly.CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ tC_monic, tP_eq]

  -- Degree bound for the quotient polynomial
  have hdeg_h : ((((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).divByMonic
      (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
        (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)))).toPoly).degree
        < (d : WithBot ℕ) := by
    rw [hdivP]
    apply Polynomial.degree_divByMonic_lt_of_degree_lt tP_monic hmodP
    rw [tP_degree, CompPoly.CPolynomial.toPoly_mul]
    have : ((d : WithBot ℕ) + (n_wit : WithBot ℕ)) = (((d + n_wit : ℕ)) : WithBot ℕ) :=
      (Nat.cast_add _ _).symm
    rw [this]
    exact Polynomial.degree_mul_lt_of_degree_lt hdeg_vS hdeg_wS ha hab

  -- Truncation: a low-degree polynomial is recovered from its `s`-power coefficients
  have trunc : ∀ (p : CompPoly.CPolynomial F), p.toPoly.degree < (d : WithBot ℕ) →
      ((List.finRange d).map (fun x : Fin d =>
          C (p.coeff (x : ℕ)) * X (none : Option Vars) ^ (x : ℕ))).sum
        = to_MvPolynomial_Option Vars p.toPoly := by
    intro p hp
    have h1 := Polynomial.list_sum_C_coeff_mul_X_pow p.toPoly d hp
    have h2 := congr_arg (to_MvPolynomial_Option (F := F) Vars) h1
    rw [map_list_sum] at h2
    simp only [List.map_map, Function.comp_def, map_mul, map_pow, to_MvPolynomial_Option_C,
      to_MvPolynomial_Option_X, ← CompPoly.CPolynomial.coeff_toPoly] at h2
    exact h2

  -- The division identity `h · t = v·w`, embedded into `MvPolynomial (Option Vars) F`
  have hkey : to_MvPolynomial_Option Vars ((((v_sum v_0 v_stmt v_wit stmt wit.fst)
        * (w_sum w_0 w_wit wit.snd)).divByMonic
        (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
          (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)))).toPoly) *
        to_MvPolynomial_Option Vars (∏ x ∈ (Finset.univ : Finset (Fin n_wit)),
          (Polynomial.X - Polynomial.C (r x)))
      = to_MvPolynomial_Option Vars (v_sum v_0 v_stmt v_wit stmt wit.fst).toPoly
        * to_MvPolynomial_Option Vars (w_sum w_0 w_wit wit.snd).toPoly := by
    have hdiv_id : (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
          (Polynomial.X - Polynomial.C (r i))) *
          (((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).toPoly
            /ₘ (∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i))))
        = ((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).toPoly := by
      have h := Polynomial.modByMonic_add_div
        ((v_sum v_0 v_stmt v_wit stmt wit.fst) * (w_sum w_0 w_wit wit.snd)).toPoly
        (∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i)))
      rwa [hmodP, zero_add] at h
    rw [hdivP, ← map_mul, mul_comm, hdiv_id, CompPoly.CPolynomial.toPoly_mul, map_mul]

  -- Expansions of the embedded combined polynomials into per-index sums
  have expand_v : to_MvPolynomial_Option Vars (v_sum v_0 v_stmt v_wit stmt wit.fst).toPoly
      = to_MvPolynomial_Option Vars v_0.toPoly
        + ((List.finRange n_stmt).map
            (fun x => C (stmt x) * to_MvPolynomial_Option Vars (v_stmt x).toPoly)).sum
        + ((List.finRange n_wit).map
            (fun x => C (wit.fst x) * to_MvPolynomial_Option Vars (v_wit x).toPoly)).sum := by
    rw [vsum_toPoly]
    simp only [map_add, map_list_sum, List.map_map, Function.comp_def, map_mul,
      to_MvPolynomial_Option_C]
  have expand_w : to_MvPolynomial_Option Vars (w_sum w_0 w_wit wit.snd).toPoly
      = to_MvPolynomial_Option Vars w_0.toPoly
        + ((List.finRange m).map
            (fun x => C (wit.snd x) * to_MvPolynomial_Option Vars (w_wit x).toPoly)).sum := by
    rw [wsum_toPoly]
    simp only [map_add, map_list_sum, List.map_map, Function.comp_def, map_mul,
      to_MvPolynomial_Option_C]

  rw [expand_v, expand_w] at hkey

  constructor
  · intro check_idx
    cases check_idx
    all_goals
      -- Expand the enumerations, transport to mathlib `MvPolynomial`, clean up and distribute
      simp only [toList_PairingsI_Idx, toList_PairingsII_Idx, toList_PairingsIII_Idx,
        toList_PairingsIV_Idx, toList_PairingsV_Idx, toList_Proof_G1_Idx, toList_Proof_G2_Idx,
        toList_SRS_Elements_Idx,
        List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
        List.sum_append_add_monoid, List.sum_cons, List.sum_nil]
      apply (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)).injective
      simp only [map_add, map_mul, map_neg, map_one, map_zero, map_pow, map_list_sum,
        List.map_map, Function.comp_def, equivC, equivX, equivOpt,
        CompPoly.CPolynomial.toPoly_prod, CompPoly.CPolynomial.toPoly_X_sub_C]
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
      -- Checks II–V are exact identities
      try ring
    -- Only check I remains: rewrite the quotient encoding and use the division identity
    rw [trunc _ hdeg_h]
    linear_combination -hkey
  · -- No identified proof elements
    intro pfs hpfs
    exact absurd hpfs List.not_mem_nil

end completeness

end GGPR

end GGPR
