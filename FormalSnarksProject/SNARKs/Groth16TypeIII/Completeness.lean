/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import FormalSnarksProject.SNARKs.Groth16TypeIII.Defs
public import FormalSnarksProject.ToMathlib.PolynomialDegreeHelpers

/-!

# Groth16TypeIII Completeness

This file contains the completeness proof for the Type III version of Groth16 presented in
["Another Look at Extraction and Randomization of Groth's zk-SNARK" by Baghery et al.](https://eprint.iacr.org/2020/811).

Unlike soundness, completeness requires degree assumptions on the QAP polynomials: the honest
prover encodes the combined polynomials `u`/`v` by their coefficients on the SRS powers
`x^0, …, x^(n_var - 1)` and the quotient `h = (u·v - w) /ₘ t` on `x^0·t, …, x^(n_var - 2)·t`,
so these encodings are faithful only when `deg(u), deg(v), deg(w) < n_var` and `n_var ≤ n_wit`
(recall `deg t = n_wit`, which gives `deg h ≤ deg(u·v) - deg(t) < n_var - 1`). Without these
hypotheses the statement is false: e.g. with `n_var = 0`, `n_wit = 0` (so `t = 1` and any
statement/witness satisfies the relation) and `u_stmt 0 = X^5`, the pairing check fails.

-/

public section

open scoped BigOperators

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace Groth16TypeIII

section completeness

noncomputable def u_sum {F : Type} [Field F] [BEq F] [LawfulBEq F] {n_stmt n_wit : ℕ}
    (u_stmt : Fin n_stmt → (CompPoly.CPolynomial F))
    (u_wit : Fin n_wit → (CompPoly.CPolynomial F))
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F)
    : CompPoly.CPolynomial F :=
  List.sum (List.map (fun j => CompPoly.CPolynomial.C (stmt j) * (u_stmt j)) (List.finRange n_stmt))
  + List.sum (List.map (fun j => CompPoly.CPolynomial.C (wit j) * (u_wit j)) (List.finRange n_wit))

noncomputable def v_sum {F : Type} [Field F] [BEq F] [LawfulBEq F] {n_stmt n_wit : ℕ}
    (v_stmt : Fin n_stmt → (CompPoly.CPolynomial F))
    (v_wit : Fin n_wit → (CompPoly.CPolynomial F))
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F)
    : CompPoly.CPolynomial F :=
  List.sum (List.map (fun j => CompPoly.CPolynomial.C (stmt j) * (v_stmt j)) (List.finRange n_stmt))
  + List.sum (List.map (fun j => CompPoly.CPolynomial.C (wit j) * (v_wit j)) (List.finRange n_wit))

noncomputable def w_sum {F : Type} [Field F] [BEq F] [LawfulBEq F] {n_stmt n_wit : ℕ}
    (w_stmt : Fin n_stmt → (CompPoly.CPolynomial F))
    (w_wit : Fin n_wit → (CompPoly.CPolynomial F))
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F)
    : CompPoly.CPolynomial F :=
  List.sum (List.map (fun j => CompPoly.CPolynomial.C (stmt j) * (w_stmt j)) (List.finRange n_stmt))
  + List.sum (List.map (fun j => CompPoly.CPolynomial.C (wit j) * (w_wit j)) (List.finRange n_wit))

noncomputable def wit_prover (F : Type) [Field F] [BEq F] [LawfulBEq F]
    (n_stmt n_wit n_var : ℕ)
    (u_stmt : Fin n_stmt → (CompPoly.CPolynomial F)) (u_wit : Fin n_wit → (CompPoly.CPolynomial F))
    (v_stmt : Fin n_stmt → (CompPoly.CPolynomial F)) (v_wit : Fin n_wit → (CompPoly.CPolynomial F))
    (w_stmt : Fin n_stmt → (CompPoly.CPolynomial F)) (w_wit : Fin n_wit → (CompPoly.CPolynomial F))
    (r : Fin n_wit → F)
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F) :
    (Groth16TypeIII
      (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
      (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
      (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r)).Prover where
        fst pf_elem srs_elem := match pf_elem with
          | Proof_G1_Idx.A => match srs_elem with
            | SRS_Elements_G1_Idx.α => 1
            | SRS_Elements_G1_Idx.β => 0
            | SRS_Elements_G1_Idx.δ => 0
            | SRS_Elements_G1_Idx.x_pow i => (u_sum u_stmt u_wit stmt wit).coeff i
            | SRS_Elements_G1_Idx.x_pow_times_t _ => 0
            | SRS_Elements_G1_Idx.y _ => 0
            | SRS_Elements_G1_Idx.q _ => 0
          | Proof_G1_Idx.C =>
            match srs_elem with
            | SRS_Elements_G1_Idx.α => 0
            | SRS_Elements_G1_Idx.β => 0
            | SRS_Elements_G1_Idx.δ => 0
            | SRS_Elements_G1_Idx.x_pow _ => 0
            | SRS_Elements_G1_Idx.x_pow_times_t i =>
              let t : CompPoly.CPolynomial F := ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
              (((u_sum u_stmt u_wit stmt wit) * (v_sum v_stmt v_wit stmt wit) - (w_sum w_stmt w_wit stmt wit)).divByMonic t).coeff i
            | SRS_Elements_G1_Idx.y _ => 0
            | SRS_Elements_G1_Idx.q i => wit i
        snd pf_elem srs_elem := match pf_elem with
          | Proof_G2_Idx.B => match srs_elem with
            | SRS_Elements_G2_Idx.β => 1
            | SRS_Elements_G2_Idx.γ => 0
            | SRS_Elements_G2_Idx.δ => 0
            | SRS_Elements_G2_Idx.x_pow i => (v_sum v_stmt v_wit stmt wit).coeff i


set_option maxHeartbeats 1000000 in
lemma is_complete
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {u_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {v_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {v_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {w_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {w_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {r : Fin n_wit → F}
    -- Degree assumptions making the prover's coefficient encodings faithful (see module docstring)
    (hn_pos : 0 < n_var) (hn_le : n_var ≤ n_wit)
    (hdeg_u_stmt : ∀ i, (u_stmt i).toPoly.degree < (n_var : WithBot ℕ))
    (hdeg_u_wit : ∀ i, (u_wit i).toPoly.degree < (n_var : WithBot ℕ))
    (hdeg_v_stmt : ∀ i, (v_stmt i).toPoly.degree < (n_var : WithBot ℕ))
    (hdeg_v_wit : ∀ i, (v_wit i).toPoly.degree < (n_var : WithBot ℕ))
    (hdeg_w_stmt : ∀ i, (w_stmt i).toPoly.degree < (n_var : WithBot ℕ))
    (hdeg_w_wit : ∀ i, (w_wit i).toPoly.degree < (n_var : WithBot ℕ)) :
    (completeness
      F
      (Groth16TypeIII
        (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
        (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
        (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r))
      (Fin n_wit -> F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        let t : CompPoly.CPolynomial F :=
          ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
        (((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * u_wit i) (List.finRange n_wit))))
            *
          ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * v_wit i) (List.finRange n_wit))))
            -
          ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * w_wit i) (List.finRange n_wit))))).modByMonic t = 0
      )
      (
        wit_prover
          (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (n_var := n_var)
          (u_stmt := u_stmt) (u_wit := u_wit) (v_stmt := v_stmt)
          (v_wit := v_wit) (w_stmt := w_stmt) (w_wit := w_wit) (r := r)
      )
    ) := by
  unfold completeness verify check_poly pairing_poly proof_element_G1_as_poly
    proof_element_G2_as_poly wit_prover
  intros stmt wit hrel

  constructor
  · intro check_idx

    -- Bridge helpers: `CPoly.COrdMvPolynomial.ordPolyRingEquiv` (whose coercion is `CPoly.COrdMvPolynomial.fromCOrdMvPolynomial`) carries
    -- the computable `COrdMvPolynomial` verification equation over to mathlib's `MvPolynomial`.
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

    -- Expand the `FinEnum` index enumerations into their concrete defining lists
    simp only [toList_PairingsIdx, toList_Proof_G1_Idx, toList_Proof_G2_Idx,
      toList_SRS_Elements_G1_Idx, toList_SRS_Elements_G2_Idx,
      List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
      List.sum_append_add_monoid, List.sum_cons, List.sum_nil]

    -- Transport the goal to mathlib's `MvPolynomial`
    apply (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)).injective
    simp only [map_add, map_mul, map_neg, map_one, map_zero, map_pow, map_list_sum,
      List.map_map, Function.comp_def, equivC, equivX, equivOpt,
      CompPoly.CPolynomial.toPoly_prod, CompPoly.CPolynomial.toPoly_X_sub_C]

    -- Clean up zero/one coefficients and distribute products over sums
    simp only [List.sum_map_zero, mul_add, add_mul, List.sum_map_add,
      map_one, one_mul, map_zero, zero_mul, add_zero, map_neg, neg_mul, neg_add_rev,
      List.map_const', List.length_finRange, List.sum_replicate, smul_zero, mul_zero,
      zero_add]

    simp only [
      -- Associativity to obtain a right-leaning tree
      mul_assoc,
      -- Commutativity lemmas to move X (some _) to the left
      mul_left_comm (C _) (X (some _)) _, mul_left_comm (List.sum _) (X (some _)) _,
      mul_comm (C _) (X (some _)), mul_comm (List.sum _) (X (some _)),
      -- Move negations to the bottom
      neg_mul, mul_neg,
      -- Move constant multiplications (which the X (some _) terms should be) out of sums
      List.sum_map_mul_right, List.sum_map_mul_left]

    -- Abbreviations for the combined QAP polynomials and the (computable/mathlib) vanishing polys
    set uS := u_sum u_stmt u_wit stmt wit with huS
    set vS := v_sum v_stmt v_wit stmt wit with hvS
    set wS := w_sum w_stmt w_wit stmt wit with hwS

    -- Basic facts about the vanishing polynomial
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

    -- `toPoly` expansions of the combined QAP polynomials, and their degree bounds
    have expand_u : to_MvPolynomial_Option Vars uS.toPoly
        = ((List.finRange n_stmt).map
            (fun b => C (stmt b) * to_MvPolynomial_Option Vars (u_stmt b).toPoly)).sum
          + ((List.finRange n_wit).map
            (fun b => C (wit b) * to_MvPolynomial_Option Vars (u_wit b).toPoly)).sum := by
      rw [huS]; unfold u_sum
      simp only [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_list_sum,
        List.map_map, Function.comp_def, CompPoly.CPolynomial.toPoly_mul,
        CompPoly.CPolynomial.C_toPoly, map_add, map_list_sum, map_mul, to_MvPolynomial_Option_C]
    have expand_v : to_MvPolynomial_Option Vars vS.toPoly
        = ((List.finRange n_stmt).map
            (fun b => C (stmt b) * to_MvPolynomial_Option Vars (v_stmt b).toPoly)).sum
          + ((List.finRange n_wit).map
            (fun b => C (wit b) * to_MvPolynomial_Option Vars (v_wit b).toPoly)).sum := by
      rw [hvS]; unfold v_sum
      simp only [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_list_sum,
        List.map_map, Function.comp_def, CompPoly.CPolynomial.toPoly_mul,
        CompPoly.CPolynomial.C_toPoly, map_add, map_list_sum, map_mul, to_MvPolynomial_Option_C]
    have expand_w : to_MvPolynomial_Option Vars wS.toPoly
        = ((List.finRange n_stmt).map
            (fun b => C (stmt b) * to_MvPolynomial_Option Vars (w_stmt b).toPoly)).sum
          + ((List.finRange n_wit).map
            (fun b => C (wit b) * to_MvPolynomial_Option Vars (w_wit b).toPoly)).sum := by
      rw [hwS]; unfold w_sum
      simp only [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_list_sum,
        List.map_map, Function.comp_def, CompPoly.CPolynomial.toPoly_mul,
        CompPoly.CPolynomial.C_toPoly, map_add, map_list_sum, map_mul, to_MvPolynomial_Option_C]

    have usum_toPoly : uS.toPoly
        = ((List.finRange n_stmt).map (fun j => Polynomial.C (stmt j) * (u_stmt j).toPoly)).sum
          + ((List.finRange n_wit).map (fun j => Polynomial.C (wit j) * (u_wit j).toPoly)).sum := by
      rw [huS]; unfold u_sum
      simp only [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_list_sum,
        List.map_map, Function.comp_def, CompPoly.CPolynomial.toPoly_mul,
        CompPoly.CPolynomial.C_toPoly]
    have vsum_toPoly : vS.toPoly
        = ((List.finRange n_stmt).map (fun j => Polynomial.C (stmt j) * (v_stmt j).toPoly)).sum
          + ((List.finRange n_wit).map (fun j => Polynomial.C (wit j) * (v_wit j).toPoly)).sum := by
      rw [hvS]; unfold v_sum
      simp only [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_list_sum,
        List.map_map, Function.comp_def, CompPoly.CPolynomial.toPoly_mul,
        CompPoly.CPolynomial.C_toPoly]
    have wsum_toPoly : wS.toPoly
        = ((List.finRange n_stmt).map (fun j => Polynomial.C (stmt j) * (w_stmt j).toPoly)).sum
          + ((List.finRange n_wit).map (fun j => Polynomial.C (wit j) * (w_wit j).toPoly)).sum := by
      rw [hwS]; unfold w_sum
      simp only [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_list_sum,
        List.map_map, Function.comp_def, CompPoly.CPolynomial.toPoly_mul,
        CompPoly.CPolynomial.C_toPoly]

    have hdeg_usum : uS.toPoly.degree < (n_var : WithBot ℕ) := by
      rw [usum_toPoly]
      exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
        (max_lt (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_u_stmt)
          (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_u_wit))
    have hdeg_vsum : vS.toPoly.degree < (n_var : WithBot ℕ) := by
      rw [vsum_toPoly]
      exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
        (max_lt (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_v_stmt)
          (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_v_wit))
    have hdeg_wsum : wS.toPoly.degree < (n_var : WithBot ℕ) := by
      rw [wsum_toPoly]
      exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
        (max_lt (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_w_stmt)
          (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hdeg_w_wit))

    -- The QAP relation, transported to mathlib `Polynomial`
    have hrel' : (uS * vS - wS).modByMonic (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
        (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i))) = 0 := hrel
    have hmodP : (uS * vS - wS).toPoly %ₘ (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
        (Polynomial.X - Polynomial.C (r i))) = 0 := by
      have h2 := congr_arg CompPoly.CPolynomial.toPoly hrel'
      rw [CompPoly.CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ tC_monic, tP_eq,
        CompPoly.CPolynomial.toPoly_zero] at h2
      exact h2
    have hdivP : ((uS * vS - wS).divByMonic (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
        (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)))).toPoly
        = (uS * vS - wS).toPoly /ₘ (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
            (Polynomial.X - Polynomial.C (r i))) := by
      rw [CompPoly.CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ tC_monic, tP_eq]

    -- Degree bound for the quotient polynomial
    have hdeg_h : (((uS * vS - wS).divByMonic (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
        (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)))).toPoly).degree
          < ((n_var - 1 : ℕ) : WithBot ℕ) := by
      rw [hdivP]
      apply Polynomial.degree_divByMonic_lt_of_degree_lt tP_monic hmodP
      rw [tP_degree, CompPoly.CPolynomial.toPoly_sub, CompPoly.CPolynomial.toPoly_mul]
      exact Polynomial.degree_mul_sub_lt_of_degree_lt hdeg_usum hdeg_vsum hdeg_wsum hn_pos hn_le

    -- Truncation: a low-degree polynomial is recovered from its SRS-power coefficients
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

    -- Pull the constant embedded-`t` factor out of the quotient-encoding sum
    have hpull : ((List.finRange (n_var - 1)).map (fun b : Fin (n_var - 1) =>
          C (((uS * vS - wS).divByMonic (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
              (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)))).coeff (b : ℕ)) *
            (X (none : Option Vars) ^ (b : ℕ) *
              to_MvPolynomial_Option Vars (∏ x ∈ (Finset.univ : Finset (Fin n_wit)),
                (Polynomial.X - Polynomial.C (r x)))))).sum
        = ((List.finRange (n_var - 1)).map (fun b : Fin (n_var - 1) =>
            C (((uS * vS - wS).divByMonic (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
                (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)))).coeff (b : ℕ)) *
              X (none : Option Vars) ^ (b : ℕ))).sum *
            to_MvPolynomial_Option Vars (∏ x ∈ (Finset.univ : Finset (Fin n_wit)),
              (Polynomial.X - Polynomial.C (r x))) := by
      rw [← List.sum_map_mul_right]
      simp only [mul_assoc]

    -- The division identity `H · t = u·v - w`, embedded into `MvPolynomial (Option Vars) F`
    have hkey : to_MvPolynomial_Option Vars (((uS * vS - wS).divByMonic
          (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
            (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)))).toPoly) *
          to_MvPolynomial_Option Vars (∏ x ∈ (Finset.univ : Finset (Fin n_wit)),
            (Polynomial.X - Polynomial.C (r x)))
        = to_MvPolynomial_Option Vars uS.toPoly * to_MvPolynomial_Option Vars vS.toPoly
          - to_MvPolynomial_Option Vars wS.toPoly := by
      have hdiv_id : (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
            (Polynomial.X - Polynomial.C (r i))) *
            ((uS * vS - wS).toPoly /ₘ (∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
              (Polynomial.X - Polynomial.C (r i))))
          = (uS * vS - wS).toPoly := by
        have h := Polynomial.modByMonic_add_div (uS * vS - wS).toPoly
          (∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (Polynomial.X - Polynomial.C (r i)))
        rwa [hmodP, zero_add] at h
      rw [hdivP, ← map_mul, mul_comm, hdiv_id, CompPoly.CPolynomial.toPoly_sub,
        CompPoly.CPolynomial.toPoly_mul, map_sub, map_mul]

    -- Rewrite the three coefficient-encoding sums into embedded polynomials, then close by ring
    rw [trunc uS n_var hdeg_usum, trunc vS n_var hdeg_vsum, hpull,
      trunc _ (n_var - 1) hdeg_h, expand_u, expand_v]
    rw [expand_u, expand_v, expand_w] at hkey
    linear_combination (X (some Vars.γ) * X (some Vars.γ) * X (some Vars.δ) * X (some Vars.δ)
      : MvPolynomial (Option Vars) F) * hkey
  · -- No identified proof elements in a Type III SNARK
    intro pfs hpfs
    exact absurd hpfs List.not_mem_nil

end completeness

end Groth16TypeIII
