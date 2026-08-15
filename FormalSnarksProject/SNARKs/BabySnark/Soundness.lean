/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import FormalSnarksProject.SNARKs.BabySnark.Defs
public import FormalSnarksProject.ToMathlib.PolynomialDegreeHelpers

/-!

# BabySNARK Soundness

This file contains the soundness proof for BabySNARK; see `Defs.lean` for the definition and an
overview of the verifier's checks.

-/

public section

open scoped BigOperators

section BabySNARK

open MvPolynomial Option AGMProofSystemInstantiation
open CompPoly

namespace BabySNARK

section soundness

-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 in -- 0 means no limit
set_option maxRecDepth 10000 in
lemma is_sound
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → CompPoly.CPolynomial F}
    {u_wit : Fin n_wit → CompPoly.CPolynomial F}
    {t : CompPoly.CPolynomial F}
    -- The verifier assembles `t` and the statement polynomial from the `τ^0, …, τ^(n_var-1)`
    -- SRS elements, so both must have degree < n_var for that encoding to be faithful
    (hdeg_t : t.toPoly.degree < (n_var : WithBot ℕ))
    (hdeg_u_stmt : ∀ j, (u_stmt j).toPoly.degree < (n_var : WithBot ℕ))
    (ht0 : t.monic) :
    (soundness
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
      (fun prover i => prover.fst Proof_Idx.B (SRS_Elements_Idx.βu i))
    ) := by
  -- Unfold the soundness definition fully
  unfold soundness verify check_poly pairing_poly proof_element_G1_as_poly proof_element_G2_as_poly
  -- Introduce the arguments to the soundness definition
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, typeI_identification⟩
  have eqnI := eqns ChecksIdx.CheckI
  have eqnII := eqns ChecksIdx.CheckII
  clear eqns

  -- Unpack the Type I identification fact for `V` (checks I and II use the two copies of `V`
  -- interchangeably; the identifications of `H` and `B` turn out not to be needed)
  have eqnV := typeI_identification (Proof_Idx.V, Proof_Idx.V) (by simp)
  clear typeI_identification

  -- Simplify the equation
  suffices
      (((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
            + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover.fst Proof_Idx.B (SRS_Elements_Idx.βu i)) * u_wit i) (List.finRange n_wit)))) ^ 2
          - 1
        )
      =
      -- The quotient: check I's toxic-free coefficient produces `(H's τ-power part + t) * t`,
      -- so the quotient is `t` plus H's combination of the `τ^i` elements. (An earlier version
      -- of this proof claimed the quotient was H's `β·u_wit`-part, which is not in the ideal.)
      (t + List.sum (List.map (fun x : Fin n_var => CompPoly.CPolynomial.C (prover.fst Proof_Idx.H (SRS_Elements_Idx.τ_pow x)) * CompPoly.CPolynomial.X ^ (x : ℕ)) (List.finRange n_var))) * t by

    rw [this, mul_comm]
    exact CompPoly.CPolynomial.mul_self_modByMonic _ _ ht0

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
  simp only [toList_PairingsI_Idx, toList_PairingsII_Idx, toList_Proof_Idx,
    toList_SRS_Elements_Idx,
    List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
    List.sum_append_add_monoid, List.sum_cons, List.sum_nil] at eqnI eqnII eqnV

  -- Transport the verification equations to mathlib's `MvPolynomial`
  replace eqnI := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnI
  replace eqnII := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnII
  replace eqnV := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqnV
  simp only [map_add, map_mul, map_neg, map_one, map_zero, map_pow, map_list_sum,
    List.map_map, Function.comp_def, equivC, equivX, equivOpt] at eqnI eqnII eqnV

  -- Clean up zero/one coefficients and distribute products over sums
  simp only [List.sum_map_zero, mul_add, add_mul, List.sum_map_add,
    map_one, one_mul, map_zero, zero_mul, add_zero, map_neg, neg_mul, neg_add_rev,
    List.map_const', List.length_finRange, List.sum_replicate, smul_zero, mul_zero,
    zero_add] at eqnI eqnII eqnV

  simp only [
    -- Associativity to obtain a right-leaning tree
    mul_assoc,
    -- Commutativity lemmas to move X (some _) to the left
    mul_left_comm (C _) (X (some _)) _, mul_left_comm (List.sum _) (X (some _)) _,
    mul_comm (C _) (X (some _)), mul_comm (List.sum _) (X (some _)),
    -- Move negations to the bottom
    neg_mul, mul_neg,
    -- Move constant multiplications (which the X (some _) terms should be) out of sums
    List.sum_map_mul_right, List.sum_map_mul_left] at eqnI eqnII eqnV

  -- Apply MvPolynomial.optionEquivRight *here*, so that we can treat polynomials in Vars_τ as
  -- constants
  replace eqnI := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnI
  replace eqnII := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnII
  replace eqnV := congr_arg (MvPolynomial.optionEquivRight F Vars) eqnV
  simp only [map_add, map_zero, map_mul, map_one,
    map_neg, AlgEquiv.list_map_sum, map_pow] at eqnI eqnII eqnV
  simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some,
    optionEquivRight_to_MvPolynomial_Option] at eqnI eqnII eqnV

  -- Move Cs back out so we can recognize the monomials
  simp only [← C_mul, ← C_pow, ← C_add, ← C_neg, MvPolynomial.sum_map_C] at eqnI eqnII eqnV

  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add,
    add_mul] at eqnI eqnII eqnV

  -- Extract the needed coefficient equations: the toxic-free monomial of check I (the square
  -- span identity), the βγ monomial of check II (pinning B's βu-slots to V's τ-power part),
  -- and the toxic-free monomial of the V identification.
  have h1eqnI := congr_arg (coeff (0 : Vars →₀ ℕ)) eqnI
  have h2eqnII := congr_arg (coeff (Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1)) eqnII
  have h3eqnV := congr_arg (coeff (0 : Vars →₀ ℕ)) eqnV

  clear eqnI eqnII eqnV

  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h1eqnI h2eqnII h3eqnV

  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply,
    Finsupp.coe_zero, Pi.zero_apply] at h1eqnI h2eqnII h3eqnV

  simp (config := {decide := true}) only [ite_false, ite_true] at h1eqnI h2eqnII h3eqnV
  simp only [neg_zero, add_zero, zero_add, neg_eq_zero] at h1eqnI h2eqnII h3eqnV

  -- Faithfulness of the verifier's τ-power encodings of `t` and the statement polynomial
  have hrep_t : ((List.finRange n_var).map (fun x : Fin n_var =>
        Polynomial.C (t.coeff (x : ℕ)) * Polynomial.X ^ (x : ℕ))).sum = t.toPoly := by
    simp_rw [CompPoly.CPolynomial.coeff_toPoly]
    exact Polynomial.list_sum_C_coeff_mul_X_pow _ _ hdeg_t
  have hrep_u : ((List.finRange n_var).map (fun x : Fin n_var =>
        ((List.finRange n_stmt).map (fun j =>
          Polynomial.C (stmt j) * Polynomial.C ((u_stmt j).coeff (x : ℕ)))).sum
            * Polynomial.X ^ (x : ℕ))).sum
      = ((List.finRange n_stmt).map
          (fun j => Polynomial.C (stmt j) * (u_stmt j).toPoly)).sum := by
    rw [← Fin.sum_univ_def, ← Fin.sum_univ_def]
    simp_rw [← Fin.sum_univ_def, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp_rw [mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [Fin.sum_univ_def]
    simp_rw [CompPoly.CPolynomial.coeff_toPoly]
    exact Polynomial.list_sum_C_coeff_mul_X_pow _ _ (hdeg_u_stmt j)

  -- `n_var` must be positive, since `t` is monic (hence nonzero) of degree `< n_var`
  have hpos : 0 < n_var := by
    by_contra h
    push_neg at h
    rw [Nat.le_zero] at h
    subst h
    have hm : t.toPoly.Monic := (CompPoly.CPolynomial.monic_toPoly_iff t).mp ht0
    rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, Polynomial.degree_eq_bot] at hdeg_t
    exact hm.ne_zero hdeg_t

  -- The verifier's `τ^0`-selector combination is the constant 1
  have hone : ((List.finRange n_var).map (fun x : Fin n_var =>
      Polynomial.C (if (x : ℕ) = 0 then (1 : F) else 0) * Polynomial.X ^ (x : ℕ))).sum = 1 := by
    rw [← Fin.sum_univ_def]
    rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin n_var)]
    · simp
    · intro b _ hb
      have hb' : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [hb']
    · simp

  -- Pull the negations (from the G2 side of the `vv` pairing) out of the list sums so that
  -- `linear_combination`'s ring-normalizer can see through them
  have neg_pull : ∀ {α : Type} (l : List α) (f : α → Polynomial F),
      (l.map (fun x => -(f x))).sum = -(l.map f).sum := by
    intro α l f
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring
  simp only [neg_pull] at h1eqnI

  -- Reduce the computable-polynomial goal to the corresponding mathlib `Polynomial` identity
  apply CompPoly.CPolynomial.toPoly_injective
  simp only [CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.toPoly_add,
    CompPoly.CPolynomial.toPoly_sub, CompPoly.CPolynomial.toPoly_pow,
    CompPoly.CPolynomial.toPoly_one, CompPoly.CPolynomial.toPoly_list_sum,
    List.map_map, Function.comp_def, CompPoly.CPolynomial.C_toPoly,
    CompPoly.CPolynomial.X_toPoly]

  -- The final ideal-membership certificate: substitute check II's β-slot identity and the V
  -- identification into check I's toxic-free coefficient, and replace the verifier's τ-power
  -- encodings of `t`, the statement polynomial and the constant 1 by their true values.
  linear_combination
    -h1eqnI
    + ((List.map (fun x => Polynomial.C (stmt x) * (u_stmt x).toPoly) (List.finRange n_stmt)).sum
        + (List.map (fun x => Polynomial.C (prover.1 Proof_Idx.B (SRS_Elements_Idx.βu x)) * (u_wit x).toPoly) (List.finRange n_wit)).sum
        + (List.map (fun x => Polynomial.C (prover.2 Proof_Idx.V (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)).sum
        + (List.map (fun x => Polynomial.C (stmt x) * (u_stmt x).toPoly) (List.finRange n_stmt)).sum) * h2eqnII
    - ((List.map (fun x => Polynomial.C (prover.2 Proof_Idx.V (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)).sum
        + (List.map (fun x => Polynomial.C (stmt x) * (u_stmt x).toPoly) (List.finRange n_stmt)).sum) * h3eqnV
    - ((List.map (fun x => Polynomial.C (prover.1 Proof_Idx.V (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)).sum
        + (List.map (fun x => Polynomial.C (prover.2 Proof_Idx.V (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)).sum
        + (List.map (fun x => Polynomial.C (stmt x) * (u_stmt x).toPoly) (List.finRange n_stmt)).sum
        + (List.map (fun x : Fin n_var => ((List.finRange n_stmt).map (fun j => Polynomial.C (stmt j) * Polynomial.C ((u_stmt j).coeff (x : ℕ)))).sum * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)).sum) * hrep_u
    + ((List.map (fun x : Fin n_var => Polynomial.C (t.coeff (x : ℕ)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)).sum
        + t.toPoly
        + (List.map (fun x => Polynomial.C (prover.1 Proof_Idx.H (SRS_Elements_Idx.τ_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)).sum) * hrep_t
    + ((List.map (fun x : Fin n_var => Polynomial.C (if (x : ℕ) = 0 then (1 : F) else 0) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var)).sum + 1) * hone

end soundness

end BabySNARK

end BabySNARK
