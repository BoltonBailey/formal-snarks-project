module

public import FormalSnarksProject.SNARKs.Pinocchio.Defs

/-!

# Pinocchio Soundness

This file contains the soundness proof for the Pinocchio SNARK; see `Defs.lean` for the
definition and an overview of the verifier's checks.

-/

public section

open scoped BigOperators

section Pinocchio

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace Pinocchio

set_option maxHeartbeats 0 in -- Disable heartbeats to prevent timeouts
set_option maxRecDepth 10000 in
lemma soundness
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit d : ℕ}
    {v_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {w_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {y_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {v_wit : Fin n_wit → CompPoly.CPolynomial F}
    {w_wit : Fin n_wit → CompPoly.CPolynomial F}
    {y_wit : Fin n_wit → CompPoly.CPolynomial F}
    {v_0 : CompPoly.CPolynomial F}
    {w_0 : CompPoly.CPolynomial F}
    {y_0 : CompPoly.CPolynomial F}
    /- t is the polynomial divisibility by which is used to verify satisfaction of the QAP -/
    {t : CompPoly.CPolynomial F}
    (tMonic : t.monic) :
    (AGMProofSystemInstantiation.soundness
      F
      (Pinocchio (F := F) (n_stmt := n_stmt) (n_wit := n_wit) (d := d)
        (v_stmt := v_stmt) (w_stmt := w_stmt) (y_stmt := y_stmt)
        (v_wit := v_wit) (w_wit := w_wit) (y_wit := y_wit)
        (v_0 := v_0) (w_0 := w_0) (y_0 := y_0) (t := t))
      (Fin n_wit → F)
      (fun (stmt : Fin n_stmt → F) (wit : Fin n_wit -> F) =>
        (-- Definition 2 from Pinocchio
          (v_0
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
        ( fun prover i => prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i) )
    ) := by
  unfold AGMProofSystemInstantiation.soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, eqnsId⟩
  have eqnI := eqns ChecksIdx.CheckI
  have eqnII := eqns ChecksIdx.CheckII
  have eqnIII := eqns ChecksIdx.CheckIII
  have eqnIV := eqns ChecksIdx.CheckIV
  have eqnV := eqns ChecksIdx.CheckV
  -- The Type I identification of the two W_mid proof elements: unlike the discarded version of
  -- this proof, we USE this equation — CheckI constrains the G2 copy of W_mid while CheckIII and
  -- CheckV constrain the G1 copy, so soundness genuinely needs them identified.
  have eqnVI := eqnsId (Proof_G1_Idx.W_mid, Proof_G2_Idx.W_mid) (by simp)
  clear eqns eqnsId

  -- Simplify the equation
  suffices
      (
          (v_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i)) * v_wit i) (List.finRange n_wit)))
          )
        *
          (w_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i)) * w_wit i) (List.finRange n_wit)))
          )
        -
          (y_0
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * y_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i)) * y_wit i) (List.finRange n_wit)))
          )
      )
      =
      -- The quotient extracted from the prover's H element. Note that beyond the `EK_s_pow`
      -- powers-of-s, the prover can also contribute a constant via the `VK_1` slot — the old
      -- (never-completed) version of this proof omitted that term, making its intermediate
      -- claim unprovable ("polyrith: not in ideal").
      (CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.VK_1))
        + List.sum (List.map (fun x : Fin d => CompPoly.CPolynomial.C (prover.snd Proof_G2_Idx.H (SRS_Elements_Idx.EK_s_pow x)) * (CompPoly.CPolynomial.X ^ (x : ℕ))) (List.finRange (d)))) * t by

    -- Restate the goal's relation polynomial with the extractor substituted (defeq), so it
    -- matches `this` syntactically.
    show (
        (v_0
          + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
          + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i)) * v_wit i) (List.finRange n_wit))))
      *
        (w_0
          + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
          + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i)) * w_wit i) (List.finRange n_wit))))
      -
        (y_0
          + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * y_stmt i) (List.finRange n_stmt)))
          + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y i)) * y_wit i) (List.finRange n_wit))))
      ).modByMonic t = 0
    rw [this, mul_comm]
    exact CompPoly.CPolynomial.mul_self_modByMonic _ _ tMonic

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

  -- Expand the `FinEnum` index enumerations into their concrete defining lists (still in the
  -- computable `COrdMvPolynomial` world), splitting the sums along the way.
  simp only [toList_PairingsI_Idx, toList_PairingsII_Idx, toList_PairingsIII_Idx,
    toList_PairingsIV_Idx, toList_PairingsV_Idx, toList_Proof_G1_Idx, toList_Proof_G2_Idx,
    toList_SRS_Elements_Idx,
    List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
    List.sum_append_add_monoid, List.sum_cons, List.sum_nil] at eqnI eqnII eqnIII eqnIV eqnV eqnVI

  -- Transport the verification equations to mathlib's `MvPolynomial`
  replace eqnI := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnI
  replace eqnII := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnII
  replace eqnIII := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnIII
  replace eqnIV := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnIV
  replace eqnV := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnV
  replace eqnVI := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnVI
  simp only [map_add, map_mul, map_neg, map_one, map_zero, map_pow, map_list_sum,
    List.map_map, Function.comp_def, equivC, equivX,
    equivOpt] at eqnI eqnII eqnIII eqnIV eqnV eqnVI

  -- Clean up zero/one coefficients and distribute products over sums
  simp only [List.sum_map_zero, mul_add, add_mul, List.sum_map_add,
    map_one, one_mul, map_zero, zero_mul, add_zero, map_neg, neg_mul, neg_add_rev,
    List.map_const', List.length_finRange, List.sum_replicate, smul_zero, mul_zero,
    zero_add] at eqnI eqnII eqnIII eqnIV eqnV eqnVI

  simp only [
    -- Associativity to obtain a right-leaning tree
    mul_assoc,
    -- Commutativity lemmas to move X (some _) to the left
    mul_left_comm (C _) (X (some _)) _, mul_left_comm (List.sum _) (X (some _)) _,
    mul_comm (C _) (X (some _)), mul_comm (List.sum _) (X (some _)),
    -- Move negations to the bottom
    neg_mul, mul_neg,
    -- Move constant multiplications (which the X (some _) terms should be) out of sums
    List.sum_map_mul_right, List.sum_map_mul_left] at eqnI eqnII eqnIII eqnIV eqnV eqnVI

  -- Apply MvPolynomial.optionEquivRight *here*, so that we can treat polynomials in the
  -- evaluation point as constants
  replace eqnI := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnI
  replace eqnII := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnII
  replace eqnIII := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnIII
  replace eqnIV := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnIV
  replace eqnV := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnV
  replace eqnVI := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnVI
  simp only [map_add, map_zero, map_mul, map_one,
    map_neg, AlgEquiv.list_map_sum, map_pow] at eqnI eqnII eqnIII eqnIV eqnV eqnVI
  simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some,
    optionEquivRight_to_MvPolynomial_Option] at eqnI eqnII eqnIII eqnIV eqnV eqnVI

  -- Move Cs back out so we can recognize the monomials
  simp only [← C_mul, ← C_pow, ← C_add, MvPolynomial.sum_map_C] at eqnI eqnII eqnIII eqnIV eqnV eqnVI

  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add,
    add_mul] at eqnI eqnII eqnIII eqnIV eqnV eqnVI

  -- Extract the coefficient equations needed for the soundness argument (13 in total).
  --
  -- Writing each proof element P as a combination over the toxic-waste monomial classes
  -- (P = A_P + r_v·V_P + r_w·W_P + r_v r_w·Y_P + β(r_v·Vβ_P + r_w·Wβ_P + r_v r_w·Yβ_P) + …),
  -- the argument is:
  -- * eqnI  at r_v r_w        : (v_io + V_V)(w_io + W_{W₂}) − t(a_H + S_H) − (y_io + Y_Y) = 0
  --                             (+ cross terms Y_V·A, A·Y_{W₂}, W_V·V_{W₂}, killed below)
  -- * eqnII at r_w α_v / r_v r_w α_v   : kills W_V and Y_V (the w-/y-parts of V_mid)
  -- * eqnIII at r_v α_w / r_v r_w α_w  : kills V_{W₁} and Y_{W₁} (the v-/y-parts of W_mid^G1)
  -- * eqnIV at r_v α_y / r_w α_y       : kills V_Y and W_Y (the v-/w-parts of Y_mid)
  -- * eqnV  at βγ·{r_v, r_w, r_v r_w}  : Vβ_Z = V_V + V_{W₁} + V_Y, and w-/y-analogues
  -- * eqnVI at {r_v, r_w, r_v r_w}     : V/W/Y-parts of W_mid^G1 = those of W_mid^G2
  have h1eqnI := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1)) eqnI
  have h71eqnII := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.r_w 1)) eqnII
  have h93eqnII := congr_arg (coeff (Finsupp.single Vars.α_v 1 + Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1)) eqnII
  have h81eqnIII := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.α_w 1)) eqnIII
  have h27eqnIII := congr_arg (coeff (Finsupp.single Vars.α_w 1 + Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1)) eqnIII
  have h102eqnIV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.α_y 1)) eqnIV
  have h55eqnIV := congr_arg (coeff (Finsupp.single Vars.r_w 1 + Finsupp.single Vars.α_y 1)) eqnIV
  have h2eqnV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnV
  have h3eqnV := congr_arg (coeff (Finsupp.single Vars.r_w 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnV
  have h4eqnV := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnV
  have h1eqnVI := congr_arg (coeff (Finsupp.single Vars.r_v 1)) eqnVI
  have h2eqnVI := congr_arg (coeff (Finsupp.single Vars.r_w 1)) eqnVI
  have h3eqnVI := congr_arg (coeff (Finsupp.single Vars.r_v 1 + Finsupp.single Vars.r_w 1)) eqnVI

  clear eqnI eqnII eqnIII eqnIV eqnV eqnVI

  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h1eqnI h71eqnII h93eqnII h81eqnIII h27eqnIII h102eqnIV h55eqnIV h2eqnV h3eqnV h4eqnV h1eqnVI h2eqnVI h3eqnVI

  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at h1eqnI h71eqnII h93eqnII h81eqnIII h27eqnIII h102eqnIV h55eqnIV h2eqnV h3eqnV h4eqnV h1eqnVI h2eqnVI h3eqnVI

  simp (config := {decide := true}) only [ite_false, ite_true] at h1eqnI h71eqnII h93eqnII h81eqnIII h27eqnIII h102eqnIV h55eqnIV h2eqnV h3eqnV h4eqnV h1eqnVI h2eqnVI h3eqnVI
  simp only [neg_zero, add_zero, zero_add, neg_eq_zero] at h1eqnI h71eqnII h93eqnII h81eqnIII h27eqnIII h102eqnIV h55eqnIV h2eqnV h3eqnV h4eqnV h1eqnVI h2eqnVI h3eqnVI

  -- Reduce the computable-polynomial goal to the corresponding mathlib `Polynomial` identity
  apply CompPoly.CPolynomial.toPoly_injective
  simp only [CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.toPoly_add,
    CompPoly.CPolynomial.toPoly_sub, CompPoly.CPolynomial.toPoly_list_sum,
    List.map_map, Function.comp_def, CompPoly.CPolynomial.C_toPoly,
    CompPoly.CPolynomial.X_toPoly, CompPoly.CPolynomial.toPoly_pow]

  -- Name the linear-combination atoms: for each proof element P and SRS component class, the
  -- polynomial contributed by P's coefficients on that class.
  generalize List.sum (List.map (fun i => Polynomial.C (stmt i) * (v_stmt i).toPoly) (List.finRange n_stmt)) = S_v at *
  generalize List.sum (List.map (fun i => Polynomial.C (stmt i) * (w_stmt i).toPoly) (List.finRange n_stmt)) = S_w at *
  generalize List.sum (List.map (fun i => Polynomial.C (stmt i) * (y_stmt i).toPoly) (List.finRange n_stmt)) = S_y at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_v x)) * (v_wit x).toPoly) (List.finRange n_wit)) = V_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_w x)) * (w_wit x).toPoly) (List.finRange n_wit)) = V_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_y x)) * (y_wit x).toPoly) (List.finRange n_wit)) = V_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.VK_v_stmt x)) * (v_stmt x).toPoly) (List.finRange n_stmt)) = V_vs at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.VK_w_stmt x)) * (w_stmt x).toPoly) (List.finRange n_stmt)) = V_ws at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.VK_y_stmt x)) * (y_stmt x).toPoly) (List.finRange n_stmt)) = V_ys at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.V_mid (SRS_Elements_Idx.EK_s_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange d)) = V_s at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_v x)) * (v_wit x).toPoly) (List.finRange n_wit)) = W1_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_w x)) * (w_wit x).toPoly) (List.finRange n_wit)) = W1_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.EK_y x)) * (y_wit x).toPoly) (List.finRange n_wit)) = W1_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.VK_v_stmt x)) * (v_stmt x).toPoly) (List.finRange n_stmt)) = W1_vs at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.VK_w_stmt x)) * (w_stmt x).toPoly) (List.finRange n_stmt)) = W1_ws at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.W_mid (SRS_Elements_Idx.VK_y_stmt x)) * (y_stmt x).toPoly) (List.finRange n_stmt)) = W1_ys at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_v x)) * (v_wit x).toPoly) (List.finRange n_wit)) = Y_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_w x)) * (w_wit x).toPoly) (List.finRange n_wit)) = Y_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.EK_y x)) * (y_wit x).toPoly) (List.finRange n_wit)) = Y_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.VK_v_stmt x)) * (v_stmt x).toPoly) (List.finRange n_stmt)) = Y_vs at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.VK_w_stmt x)) * (w_stmt x).toPoly) (List.finRange n_stmt)) = Y_ws at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Y_mid (SRS_Elements_Idx.VK_y_stmt x)) * (y_stmt x).toPoly) (List.finRange n_stmt)) = Y_ys at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.EK_v x)) * (v_wit x).toPoly) (List.finRange n_wit)) = W2_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.EK_w x)) * (w_wit x).toPoly) (List.finRange n_wit)) = W2_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.EK_y x)) * (y_wit x).toPoly) (List.finRange n_wit)) = W2_y at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.VK_v_stmt x)) * (v_stmt x).toPoly) (List.finRange n_stmt)) = W2_vs at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.VK_w_stmt x)) * (w_stmt x).toPoly) (List.finRange n_stmt)) = W2_ws at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.VK_y_stmt x)) * (y_stmt x).toPoly) (List.finRange n_stmt)) = W2_ys at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.W_mid (SRS_Elements_Idx.EK_s_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange d)) = W2_s at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y x)) * (v_wit x).toPoly) (List.finRange n_wit)) = Z_v at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y x)) * (w_wit x).toPoly) (List.finRange n_wit)) = Z_w at *
  generalize List.sum (List.map (fun x => Polynomial.C (prover.1 Proof_G1_Idx.Z (SRS_Elements_Idx.EK_β_v_w_y x)) * (y_wit x).toPoly) (List.finRange n_wit)) = Z_y at *

  generalize List.sum (List.map (fun x => Polynomial.C (prover.2 Proof_G2_Idx.H (SRS_Elements_Idx.EK_s_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange d)) = H_s at *

  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_1) = V_1 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_t) = V_t at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_v_0) = V_v0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_w_0) = V_w0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.V_mid SRS_Elements_Idx.VK_y_0) = V_y0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_t) = W1_t at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_v_0) = W1_v0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_w_0) = W1_w0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.W_mid SRS_Elements_Idx.VK_y_0) = W1_y0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_t) = Y_t at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_v_0) = Y_v0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_w_0) = Y_w0 at *
  generalize Polynomial.C (prover.1 Proof_G1_Idx.Y_mid SRS_Elements_Idx.VK_y_0) = Y_y0 at *
  generalize Polynomial.C (prover.2 Proof_G2_Idx.W_mid SRS_Elements_Idx.VK_1) = W2_1 at *
  generalize Polynomial.C (prover.2 Proof_G2_Idx.W_mid SRS_Elements_Idx.VK_t) = W2_t at *
  generalize Polynomial.C (prover.2 Proof_G2_Idx.W_mid SRS_Elements_Idx.VK_v_0) = W2_v0 at *
  generalize Polynomial.C (prover.2 Proof_G2_Idx.W_mid SRS_Elements_Idx.VK_w_0) = W2_w0 at *
  generalize Polynomial.C (prover.2 Proof_G2_Idx.W_mid SRS_Elements_Idx.VK_y_0) = W2_y0 at *
  generalize Polynomial.C (prover.2 Proof_G2_Idx.H SRS_Elements_Idx.VK_1) = H_1 at *

  -- The final ideal-membership certificate (derived by hand; see the class-decomposition
  -- comment above the coefficient extraction). Notation: the r_v-class of V_mid is
  -- `V_v + V_v0·v_0 + V_vs`, the io-polynomials are `v_0 + S_v` etc.
  linear_combination
    h1eqnI
    + (W2_v + W2_v0 * v_0.toPoly + W2_vs
        - (v_0.toPoly + S_v + V_v + V_v0 * v_0.toPoly + V_vs)) * h71eqnII
    + (W2_1 + W2_s + 1) * h93eqnII
    - (w_0.toPoly + S_w + Z_w) * h81eqnIII
    + (V_1 + V_s + 1) * h27eqnIII
    - (w_0.toPoly + S_w + Z_w) * h102eqnIV
    - (v_0.toPoly + S_v + V_v + V_v0 * v_0.toPoly + V_vs) * h55eqnIV
    + (w_0.toPoly + S_w + Z_w) * h2eqnV
    + (v_0.toPoly + S_v + V_v + V_v0 * v_0.toPoly + V_vs) * h3eqnV
    - h4eqnV
    + (v_0.toPoly + S_v + V_v + V_v0 * v_0.toPoly + V_vs) * h2eqnVI
    + (V_1 + V_s) * h3eqnVI

end Pinocchio

end Pinocchio
