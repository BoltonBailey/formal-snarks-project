import FormalSnarksProject.SNARKs.Pinocchio.Defs
import FormalSnarksProject.ToMathlib.PolynomialDegreeHelpers

/-!

# Pinocchio Completeness

This file contains the completeness proof for the Pinocchio SNARK; see `Defs.lean` for the
definition.

The honest prover places the witness coefficients on the `EK_v`/`EK_w`/`EK_y` slots of
`V_mid`/`W_mid`/`Y_mid` (α-scaled on the primed copies, β-combined on `Z`), uses the same
`W_mid` coefficients in both groups (satisfying the Type I identification), and places the
quotient `h = (v·w - y) /ₘ t` on the `EK_s_pow` slots of `H`. Checks II–V hold as exact
polynomial identities; check I requires the quotient encoding on `s^0, …, s^(d-1)` to be
faithful, which is where the degree hypotheses enter.

-/

open scoped BigOperators

section Pinocchio

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace Pinocchio

section completeness

noncomputable def v_sum {F : Type} [Field F] [BEq F] [LawfulBEq F] {n_stmt n_wit : ℕ}
    (v_0 : CompPoly.CPolynomial F)
    (v_stmt : Fin n_stmt → CompPoly.CPolynomial F)
    (v_wit : Fin n_wit → CompPoly.CPolynomial F)
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F)
    : CompPoly.CPolynomial F :=
  v_0
  + List.sum (List.map (fun j => CompPoly.CPolynomial.C (stmt j) * (v_stmt j)) (List.finRange n_stmt))
  + List.sum (List.map (fun j => CompPoly.CPolynomial.C (wit j) * (v_wit j)) (List.finRange n_wit))

noncomputable def wit_prover (F : Type) [Field F] [BEq F] [LawfulBEq F]
    (n_stmt n_wit d : ℕ)
    (v_stmt w_stmt y_stmt : Fin n_stmt → CompPoly.CPolynomial F)
    (v_wit w_wit y_wit : Fin n_wit → CompPoly.CPolynomial F)
    (v_0 w_0 y_0 : CompPoly.CPolynomial F)
    (t : CompPoly.CPolynomial F)
    (stmt : Fin n_stmt -> F)
    (wit : Fin n_wit -> F) :
    (Pinocchio (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (d := d)
      (v_stmt := v_stmt) (w_stmt := w_stmt) (y_stmt := y_stmt)
      (v_wit := v_wit) (w_wit := w_wit) (y_wit := y_wit)
      (v_0 := v_0) (w_0 := w_0) (y_0 := y_0) (t := t)).Prover where
  fst pf_elem srs_elem := match pf_elem with
    | Proof_G1_Idx.V_mid => match srs_elem with
      | SRS_Elements_Idx.EK_v i => wit i
      | _ => 0
    | Proof_G1_Idx.V_mid' => match srs_elem with
      | SRS_Elements_Idx.EK_α_v i => wit i
      | _ => 0
    | Proof_G1_Idx.W_mid => match srs_elem with
      | SRS_Elements_Idx.EK_w i => wit i
      | _ => 0
    | Proof_G1_Idx.W_mid' => match srs_elem with
      | SRS_Elements_Idx.EK_α_w i => wit i
      | _ => 0
    | Proof_G1_Idx.Y_mid => match srs_elem with
      | SRS_Elements_Idx.EK_y i => wit i
      | _ => 0
    | Proof_G1_Idx.Y_mid' => match srs_elem with
      | SRS_Elements_Idx.EK_α_y i => wit i
      | _ => 0
    | Proof_G1_Idx.Z => match srs_elem with
      | SRS_Elements_Idx.EK_β_v_w_y i => wit i
      | _ => 0
  snd pf_elem srs_elem := match pf_elem with
    | Proof_G2_Idx.W_mid => match srs_elem with
      | SRS_Elements_Idx.EK_w i => wit i
      | _ => 0
    | Proof_G2_Idx.H => match srs_elem with
      | SRS_Elements_Idx.EK_s_pow i =>
        (((v_sum v_0 v_stmt v_wit stmt wit) * (v_sum w_0 w_stmt w_wit stmt wit)
          - (v_sum y_0 y_stmt y_wit stmt wit)).divByMonic t).coeff i
      | _ => 0

set_option maxHeartbeats 1000000 in
lemma is_complete
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit d : ℕ}
    {v_stmt w_stmt y_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {v_wit w_wit y_wit : Fin n_wit → CompPoly.CPolynomial F}
    {v_0 w_0 y_0 : CompPoly.CPolynomial F}
    {t : CompPoly.CPolynomial F}
    (tMonic : t.monic)
    -- Degree assumptions making the quotient encoding on `s^0, …, s^(d-1)` faithful
    {a b c : ℕ}
    (ha : 0 < a)
    (hab : a + b ≤ d + t.toPoly.natDegree + 1)
    (hc : c ≤ d + t.toPoly.natDegree)
    (hdeg_v_0 : v_0.toPoly.degree < (a : WithBot ℕ))
    (hdeg_v_stmt : ∀ i, (v_stmt i).toPoly.degree < (a : WithBot ℕ))
    (hdeg_v_wit : ∀ i, (v_wit i).toPoly.degree < (a : WithBot ℕ))
    (hdeg_w_0 : w_0.toPoly.degree < (b : WithBot ℕ))
    (hdeg_w_stmt : ∀ i, (w_stmt i).toPoly.degree < (b : WithBot ℕ))
    (hdeg_w_wit : ∀ i, (w_wit i).toPoly.degree < (b : WithBot ℕ))
    (hdeg_y_0 : y_0.toPoly.degree < (c : WithBot ℕ))
    (hdeg_y_stmt : ∀ i, (y_stmt i).toPoly.degree < (c : WithBot ℕ))
    (hdeg_y_wit : ∀ i, (y_wit i).toPoly.degree < (c : WithBot ℕ)) :
    (completeness
      F
      (Pinocchio (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (d := d)
        (v_stmt := v_stmt) (w_stmt := w_stmt) (y_stmt := y_stmt)
        (v_wit := v_wit) (w_wit := w_wit) (y_wit := y_wit)
        (v_0 := v_0) (w_0 := w_0) (y_0 := y_0) (t := t))
      (Fin n_wit → F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        ((v_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * v_wit i) (List.finRange n_wit)))
          )
        *
          (w_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * w_wit i) (List.finRange n_wit)))
          )
        -
          (y_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * y_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit i) * y_wit i) (List.finRange n_wit)))
          )
        ).modByMonic t = 0)
      (wit_prover F n_stmt n_wit d v_stmt w_stmt y_stmt v_wit w_wit y_wit v_0 w_0 y_0 t)
    ) := by
  unfold completeness verify check_poly pairing_poly proof_element_G1_as_poly
    proof_element_G2_as_poly wit_prover
  intros stmt wit hrel

  have hrel' : ((v_sum v_0 v_stmt v_wit stmt wit) * (v_sum w_0 w_stmt w_wit stmt wit)
      - (v_sum y_0 y_stmt y_wit stmt wit)).modByMonic t = 0 := hrel

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

  -- Facts about the target polynomial
  have tP_monic : t.toPoly.Monic := (CompPoly.CPolynomial.monic_toPoly_iff t).mp tMonic
  have tP_degree : t.toPoly.degree = (t.toPoly.natDegree : WithBot ℕ) :=
    Polynomial.degree_eq_natDegree tP_monic.ne_zero

  -- `toPoly` expansions and degree bounds for the combined polynomials
  have sum_toPoly : ∀ (p_0 : CompPoly.CPolynomial F)
      (p_stmt : Fin n_stmt → CompPoly.CPolynomial F)
      (p_wit : Fin n_wit → CompPoly.CPolynomial F),
      (v_sum p_0 p_stmt p_wit stmt wit).toPoly
      = p_0.toPoly
        + ((List.finRange n_stmt).map (fun j => Polynomial.C (stmt j) * (p_stmt j).toPoly)).sum
        + ((List.finRange n_wit).map (fun j => Polynomial.C (wit j) * (p_wit j).toPoly)).sum := by
    intro p_0 p_stmt p_wit
    unfold v_sum
    simp only [CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_list_sum,
      List.map_map, Function.comp_def, CompPoly.CPolynomial.toPoly_mul,
      CompPoly.CPolynomial.C_toPoly]
  have hdeg_sum : ∀ (p_0 : CompPoly.CPolynomial F)
      (p_stmt : Fin n_stmt → CompPoly.CPolynomial F)
      (p_wit : Fin n_wit → CompPoly.CPolynomial F) (n : ℕ),
      p_0.toPoly.degree < (n : WithBot ℕ) →
      (∀ i, (p_stmt i).toPoly.degree < (n : WithBot ℕ)) →
      (∀ i, (p_wit i).toPoly.degree < (n : WithBot ℕ)) →
      (v_sum p_0 p_stmt p_wit stmt wit).toPoly.degree < (n : WithBot ℕ) := by
    intro p_0 p_stmt p_wit n h0 hs hw
    rw [sum_toPoly]
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt
        (lt_of_le_of_lt (Polynomial.degree_add_le _ _)
          (max_lt h0 (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hs)))
        (Polynomial.degree_list_sum_C_mul_lt _ _ _ _ hw))

  -- The QAP relation, transported to mathlib `Polynomial`
  have hmodP : ((v_sum v_0 v_stmt v_wit stmt wit) * (v_sum w_0 w_stmt w_wit stmt wit)
      - (v_sum y_0 y_stmt y_wit stmt wit)).toPoly %ₘ t.toPoly = 0 := by
    have h2 := congr_arg CompPoly.CPolynomial.toPoly hrel'
    rw [CompPoly.CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ tMonic,
      CompPoly.CPolynomial.toPoly_zero] at h2
    exact h2
  have hdivP : (((v_sum v_0 v_stmt v_wit stmt wit) * (v_sum w_0 w_stmt w_wit stmt wit)
      - (v_sum y_0 y_stmt y_wit stmt wit)).divByMonic t).toPoly
      = ((v_sum v_0 v_stmt v_wit stmt wit) * (v_sum w_0 w_stmt w_wit stmt wit)
          - (v_sum y_0 y_stmt y_wit stmt wit)).toPoly /ₘ t.toPoly :=
    CompPoly.CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ tMonic

  -- Degree bound for the quotient polynomial
  have hdeg_h : ((((v_sum v_0 v_stmt v_wit stmt wit) * (v_sum w_0 w_stmt w_wit stmt wit)
      - (v_sum y_0 y_stmt y_wit stmt wit)).divByMonic t).toPoly).degree < (d : WithBot ℕ) := by
    rw [hdivP]
    apply Polynomial.degree_divByMonic_lt_of_degree_lt tP_monic hmodP
    rw [tP_degree, CompPoly.CPolynomial.toPoly_sub, CompPoly.CPolynomial.toPoly_mul]
    have hcast : ((d : WithBot ℕ) + (t.toPoly.natDegree : WithBot ℕ))
        = (((d + t.toPoly.natDegree : ℕ)) : WithBot ℕ) := (Nat.cast_add _ _).symm
    rw [hcast]
    apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    apply max_lt
    · exact Polynomial.degree_mul_lt_of_degree_lt
        (hdeg_sum _ _ _ a hdeg_v_0 hdeg_v_stmt hdeg_v_wit)
        (hdeg_sum _ _ _ b hdeg_w_0 hdeg_w_stmt hdeg_w_wit) ha hab
    · exact lt_of_lt_of_le (hdeg_sum _ _ _ c hdeg_y_0 hdeg_y_stmt hdeg_y_wit)
        (by exact_mod_cast hc)

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

  -- The division identity `h · t = v·w - y`, embedded into `MvPolynomial (Option Vars) F`
  have hkey : to_MvPolynomial_Option Vars ((((v_sum v_0 v_stmt v_wit stmt wit)
        * (v_sum w_0 w_stmt w_wit stmt wit)
        - (v_sum y_0 y_stmt y_wit stmt wit)).divByMonic t).toPoly) *
        to_MvPolynomial_Option Vars t.toPoly
      = to_MvPolynomial_Option Vars (v_sum v_0 v_stmt v_wit stmt wit).toPoly
        * to_MvPolynomial_Option Vars (v_sum w_0 w_stmt w_wit stmt wit).toPoly
        - to_MvPolynomial_Option Vars (v_sum y_0 y_stmt y_wit stmt wit).toPoly := by
    have hdiv_id : t.toPoly *
        (((v_sum v_0 v_stmt v_wit stmt wit) * (v_sum w_0 w_stmt w_wit stmt wit)
          - (v_sum y_0 y_stmt y_wit stmt wit)).toPoly /ₘ t.toPoly)
        = ((v_sum v_0 v_stmt v_wit stmt wit) * (v_sum w_0 w_stmt w_wit stmt wit)
          - (v_sum y_0 y_stmt y_wit stmt wit)).toPoly := by
      have h := Polynomial.modByMonic_add_div
        ((v_sum v_0 v_stmt v_wit stmt wit) * (v_sum w_0 w_stmt w_wit stmt wit)
          - (v_sum y_0 y_stmt y_wit stmt wit)).toPoly t.toPoly
      rwa [hmodP, zero_add] at h
    rw [hdivP, ← map_mul, mul_comm, hdiv_id, CompPoly.CPolynomial.toPoly_sub,
      CompPoly.CPolynomial.toPoly_mul, map_sub, map_mul]

  -- Expansions of the embedded combined polynomials into per-index sums
  have expand : ∀ (p_0 : CompPoly.CPolynomial F)
      (p_stmt : Fin n_stmt → CompPoly.CPolynomial F)
      (p_wit : Fin n_wit → CompPoly.CPolynomial F),
      to_MvPolynomial_Option Vars (v_sum p_0 p_stmt p_wit stmt wit).toPoly
      = to_MvPolynomial_Option Vars p_0.toPoly
        + ((List.finRange n_stmt).map
            (fun x => C (stmt x) * to_MvPolynomial_Option Vars (p_stmt x).toPoly)).sum
        + ((List.finRange n_wit).map
            (fun x => C (wit x) * to_MvPolynomial_Option Vars (p_wit x).toPoly)).sum := by
    intro p_0 p_stmt p_wit
    rw [sum_toPoly]
    simp only [map_add, map_list_sum, List.map_map, Function.comp_def, map_mul,
      to_MvPolynomial_Option_C]

  rw [expand v_0 v_stmt v_wit, expand w_0 w_stmt w_wit, expand y_0 y_stmt y_wit] at hkey

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
      -- Checks II–V are exact identities
      try ring
    -- Only check I remains: rewrite the quotient encoding and use the division identity
    rw [trunc _ hdeg_h]
    linear_combination -(X (some Vars.r_v) * X (some Vars.r_w)
      : MvPolynomial (Option Vars) F) * hkey
  · -- The Type I identification of the two copies of `W_mid`: the honest prover uses the same
    -- coefficients on both sides, and the two groups have identical SRS values
    intro pfs hpfs
    simp only [List.mem_singleton] at hpfs
    subst hpfs
    simp only [toList_SRS_Elements_Idx,
      List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
      List.sum_append_add_monoid, List.sum_cons, List.sum_nil]

end completeness

end Pinocchio

end Pinocchio
