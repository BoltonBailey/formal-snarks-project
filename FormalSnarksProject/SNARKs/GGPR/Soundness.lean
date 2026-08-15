module

public import FormalSnarksProject.SNARKs.GGPR.Defs

/-!

# GGPR Soundness

This file contains the soundness proof for the GGPR SNARK; see `Defs.lean` for the definition
and an overview of the verifier's checks (only checks I and V are needed for this proof).

-/

public section

open scoped BigOperators

section GGPR

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace GGPR

set_option maxHeartbeats 0 in -- Disable heartbeats to prevent timeouts
set_option maxRecDepth 10000 in
lemma soundness
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit m d : ℕ}
    {v_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {v_wit : Fin n_wit → CompPoly.CPolynomial F}
    {w_wit : Fin m → CompPoly.CPolynomial F}
    {v_0 : CompPoly.CPolynomial F}
    {w_0 : CompPoly.CPolynomial F}
    {r : Fin (n_wit) → F} :
    (AGMProofSystemInstantiation.soundness
      F
      (GGPR (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (m := m) (d := d)
        (v_stmt := v_stmt) (v_wit := v_wit) (w_wit := w_wit)
        (v_0 := v_0) (w_0 := w_0) (r := r))
      ((Fin n_wit → F) × (Fin m → F))
      (fun (stmt : Fin n_stmt → F) (wit : (Fin n_wit -> F) × (Fin m → F)) =>
        let t : CompPoly.CPolynomial F :=
          ∏ i ∈ (Finset.univ : Finset (Fin n_wit)), (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i));
        (-- Definition 2 from GGPR
          (v_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit.fst i) * v_wit i) (List.finRange n_wit)))
          )
        *
          (w_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (wit.snd i) * w_wit i) (List.finRange m)))
          )
        ).modByMonic t = 0)
        -- The extractor reads the witness off the β-slots of `Y` (see the module docstring;
        -- an earlier draft read it off `H`, which makes the statement false).
        ( fun prover =>
           ⟨fun i => prover.fst Proof_G1_Idx.Y (SRS_Elements_Idx.EK_β_v i) ,
            fun i => prover.fst Proof_G1_Idx.Y (SRS_Elements_Idx.EK_β_w i) ⟩ )
    ) := by
  unfold AGMProofSystemInstantiation.soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, null⟩
  intro t
  -- Only checks I and V are needed for this soundness statement: check I gives the QAP product
  -- identity (on the toxic-waste-free monomial), and check V pins the witness in Y's β-slots.
  have eqnI := eqns ChecksIdx.CheckI
  have eqnV := eqns ChecksIdx.CheckV
  clear eqns null

  -- Simplify the equation
  suffices
      (
          (v_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Y (SRS_Elements_Idx.EK_β_v i)) * v_wit i) (List.finRange n_wit)))
          )
        *
          (w_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Y (SRS_Elements_Idx.EK_β_w i)) * w_wit i) (List.finRange m)))
          )
      )
      =
      -- The quotient extracted from the prover's H element: since every toxic-waste-free SRS
      -- element can contribute, this is H's full combination over those elements.
      (List.sum (List.map (fun x : Fin d => CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.EK_s_pow x)) * (CompPoly.CPolynomial.X ^ (x : ℕ))) (List.finRange d))
        + List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.EK_v i)) * v_wit i) (List.finRange n_wit))
        + List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.EK_w i)) * w_wit i) (List.finRange m))
        + CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.VK_1))
        + CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.VK_v_0)) * v_0
        + CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.VK_w_0)) * w_0
        + CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.VK_t)) * t
        + List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.VK_v_stmt i)) * v_stmt i) (List.finRange n_stmt))) * t by

    -- Restate the goal's relation polynomial with the extractor substituted (defeq), so it
    -- matches `this` syntactically.
    show (
        (v_0
          + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
          + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Y (SRS_Elements_Idx.EK_β_v i)) * v_wit i) (List.finRange n_wit))))
      *
        (w_0
          + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Y (SRS_Elements_Idx.EK_β_w i)) * w_wit i) (List.finRange m))))
      ).modByMonic t = 0
    rw [this, mul_comm]
    exact CompPoly.CPolynomial.mul_self_modByMonic _ _
      (CompPoly.CPolynomial.monic_prod_X_sub_C _ r)

  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  --
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

  -- Expand the `FinEnum` index enumerations into their concrete defining lists
  simp only [toList_PairingsI_Idx, toList_PairingsV_Idx, toList_Proof_G1_Idx, toList_Proof_G2_Idx,
    toList_SRS_Elements_Idx,
    List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
    List.sum_append_add_monoid, List.sum_cons, List.sum_nil] at eqnI eqnV

  -- Transport the verification equations to mathlib's `MvPolynomial`, converting the computable
  -- vanishing polynomial to its mathlib counterpart along the way
  replace eqnI := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnI
  replace eqnV := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnV
  simp only [map_add, map_mul, map_neg, map_one, map_zero, map_pow, map_list_sum,
    List.map_map, Function.comp_def, equivC, equivX, equivOpt,
    CompPoly.CPolynomial.toPoly_prod, CompPoly.CPolynomial.toPoly_X_sub_C] at eqnI eqnV

  -- Clean up zero/one coefficients and distribute products over sums
  simp only [List.sum_map_zero, mul_add, add_mul, List.sum_map_add,
    map_one, one_mul, map_zero, zero_mul, add_zero, map_neg, neg_mul, neg_add_rev,
    List.map_const', List.length_finRange, List.sum_replicate, smul_zero, mul_zero,
    zero_add] at eqnI eqnV

  simp only [
    -- Associativity to obtain a right-leaning tree
    mul_assoc,
    -- Commutativity lemmas to move X (some _) to the left
    mul_left_comm (C _) (X (some _)) _, mul_left_comm (List.sum _) (X (some _)) _,
    mul_comm (C _) (X (some _)), mul_comm (List.sum _) (X (some _)),
    -- Move negations to the bottom
    neg_mul, mul_neg,
    -- Move constant multiplications (which the X (some _) terms should be) out of sums
    List.sum_map_mul_right, List.sum_map_mul_left] at eqnI eqnV

  -- Apply MvPolynomial.optionEquivRight *here*, so that we can treat polynomials in the
  -- evaluation point as constants
  replace eqnI := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnI
  replace eqnV := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnV
  simp only [map_add, map_zero, map_mul, map_one,
    map_neg, AlgEquiv.list_map_sum, map_pow] at eqnI eqnV
  simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some,
    optionEquivRight_to_MvPolynomial_Option] at eqnI eqnV

  -- Move Cs back out so we can recognize the monomials
  simp only [← C_mul, ← C_pow, ← C_add, MvPolynomial.sum_map_C] at eqnI eqnV

  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add,
    add_mul] at eqnI eqnV

  -- Extract the three needed coefficient equations: the toxic-waste-free monomial of check I
  -- (the QAP product identity), and the β_v·γ / β_w·γ monomials of check V (pinning the
  -- witness in Y's β-slots).
  have h1eqnI := congr_arg (coeff (0 : Vars →₀ ℕ)) eqnI
  have h2eqnV := congr_arg (coeff (Finsupp.single Vars.β_v 1 + Finsupp.single Vars.γ 1)) eqnV
  have h3eqnV := congr_arg (coeff (Finsupp.single Vars.β_w 1 + Finsupp.single Vars.γ 1)) eqnV

  clear eqnI eqnV

  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h1eqnI h2eqnV h3eqnV

  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply,
    Finsupp.coe_zero, Pi.zero_apply] at h1eqnI h2eqnV h3eqnV

  simp (config := {decide := true}) only [ite_false, ite_true] at h1eqnI h2eqnV h3eqnV
  simp only [neg_zero, add_zero, zero_add, neg_eq_zero] at h1eqnI h2eqnV h3eqnV

  -- Reduce the computable-polynomial goal to the corresponding mathlib `Polynomial` identity
  have ht : t = ∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
      (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)) := rfl
  rw [ht]
  apply CompPoly.CPolynomial.toPoly_injective
  simp only [CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.toPoly_add,
    CompPoly.CPolynomial.toPoly_list_sum,
    List.map_map, Function.comp_def, CompPoly.CPolynomial.C_toPoly,
    CompPoly.CPolynomial.X_toPoly, CompPoly.CPolynomial.toPoly_pow,
    CompPoly.CPolynomial.toPoly_prod, CompPoly.CPolynomial.toPoly_X_sub_C]

  -- The final ideal-membership certificate: substituting check V's two β-slot identities
  -- (`Y`'s β_v-slots = V_mid's toxic-free part, β_w-slots = W's toxic-free part) into check I's
  -- toxic-free coefficient equation yields exactly the QAP product identity.
  linear_combination
    h1eqnI
    + (w_0.toPoly
        + (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y (SRS_Elements_Idx.EK_β_w x)) * (w_wit x).toPoly) (List.finRange m)).sum) * h2eqnV
    + (v_0.toPoly
        + (List.map (fun x => Polynomial.C (stmt x) * (v_stmt x).toPoly) (List.finRange n_stmt)).sum
        + (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_s_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange d)).sum
        + (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_v x)) * (v_wit x).toPoly) (List.finRange n_wit)).sum
        + (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_w x)) * (w_wit x).toPoly) (List.finRange m)).sum
        + Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_1)
        + Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_v_0) * v_0.toPoly
        + Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_w_0) * w_0.toPoly
        + Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_t)
            * (∏ x, (Polynomial.X - Polynomial.C (r x)))
        + (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.VK_v_stmt x)) * (v_stmt x).toPoly) (List.finRange n_stmt)).sum) * h3eqnV

end GGPR

end GGPR
