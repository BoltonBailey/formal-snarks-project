import FormalSnarksProject.SNARKs.Groth16TypeI.Defs

/-!

# Groth16TypeI Soundness

This file contains the soundness proof for the Type I (symmetric pairing) version of Groth16;
see `Defs.lean` for the definition.

Unlike the Type III proof, the prover here can use *every* SRS element in *every* proof
element, so each of `A`, `B`, `C` decomposes over all eight kinds of SRS elements. The
coefficient analysis begins with the α²γ²δ² coefficient of the verification equation, which
forces `A_α · B_α = 0`; the two resulting cases correspond to the two ways `A` and `B` can
split the roles of the asymmetric proof elements (`e(A,B) = e(B,A)` in a symmetric pairing, so
they are interchangeable). In each case, all "junk" components of `A` and `B` are forced to
vanish, and the extractor reads the witness off `C`'s coefficients on the `q` elements, exactly
as in the Type III proof.

The `linear_combination` certificates below were derived and verified symbolically; each `have`
eliminates one junk component. Products that are only forced to be *squares* of zero
(`(B_β · A_v_wit)² = 0` and its analogues) are resolved with `mul_self_eq_zero`, using that
`F[X]` is an integral domain.

-/

open scoped BigOperators

section Groth16TypeI

open MvPolynomial Option AGMProofSystemInstantiationTypeI
open CompPoly

namespace Groth16TypeI

section soundness

-- Remove heartbeat limit for upcoming long-running proof
set_option maxHeartbeats 0 in -- 0 means no limit
-- The final `linear_combination`/`ring` steps recurse deeply on the large polynomial expressions
set_option maxRecDepth 10000 in
lemma is_sound
    {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {n_stmt n_wit n_var : ℕ}
    {u_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {u_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {v_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {v_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {w_stmt : Fin n_stmt → (CompPoly.CPolynomial F)}
    {w_wit : Fin n_wit → (CompPoly.CPolynomial F)}
    {r : Fin n_wit → F} :
    (soundness
      F
      (Groth16TypeI
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
      (fun prover i => prover Proof_Idx.C (SRS_Elements_Idx.q i))
    ) := by


  -- Unfold the soundness definition fully
  unfold soundness verify check_poly pairing_poly proof_element_as_poly
  -- Introduce the arguments to the soundness definition
  intros stmt prover eqns
  intro t
  have eqn := eqns ()


  -- Simplify the equation
  suffices
      ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.q i)) * u_wit i) (List.finRange n_wit))))
      *
      ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.q i)) * v_wit i) (List.finRange n_wit))))
      =
      ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
      + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.q i)) * w_wit i) (List.finRange n_wit))))
      +
      List.sum (List.map (fun x : Fin (n_var - 1) => CompPoly.CPolynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.x_pow_times_t x)) * (CompPoly.CPolynomial.X ^ (x : ℕ) * t)) (List.finRange (n_var - 1))) by

    rw [<-sub_eq_iff_eq_add'] at this
    -- Restate the goal's relation polynomial in the explicit `A * B - C` form (defeq to the
    -- extractor-substituted relation), so it matches `this` syntactically.
    show (((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * u_stmt i) (List.finRange n_stmt)))
        + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.q i)) * u_wit i) (List.finRange n_wit))))
        * ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * v_stmt i) (List.finRange n_stmt)))
        + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.q i)) * v_wit i) (List.finRange n_wit))))
        - ((List.sum (List.map (fun i => CompPoly.CPolynomial.C (stmt i) * w_stmt i) (List.finRange n_stmt)))
        + (List.sum (List.map (fun i => CompPoly.CPolynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.q i)) * w_wit i) (List.finRange n_wit))))).modByMonic t = 0
    rw [this]
    clear this

    simp only [mul_comm _ (t), <-mul_assoc]
    simp only [mul_assoc, List.sum_map_mul_right, List.sum_map_mul_left]

    apply CompPoly.CPolynomial.mul_self_modByMonic
    exact CompPoly.CPolynomial.monic_prod_X_sub_C _ r


  -- Step 1: Obtain the coefficient equations of the mv_polynomials
  --
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

  -- Expand the `FinEnum` index enumerations into their concrete defining lists (still in the
  -- computable `COrdMvPolynomial` world), splitting the sums along the way.
  simp only [toList_PairingsIdx, toList_Proof_Idx, toList_SRS_Elements_Idx,
    List.map_append, List.map_cons, List.map_nil, List.map_map, Function.comp_def,
    List.sum_append_add_monoid, List.sum_cons, List.sum_nil] at eqn

  -- Transport the verification equation to mathlib's `MvPolynomial`, and convert the computable
  -- vanishing polynomial `∏ (X - C (r i))` into the corresponding mathlib `Polynomial`.
  replace eqn := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqn
  simp only [map_add, map_mul, map_neg, map_one, map_zero, map_pow, map_list_sum,
    List.map_map, Function.comp_def, equivC, equivX, equivOpt,
    CompPoly.CPolynomial.toPoly_prod, CompPoly.CPolynomial.toPoly_X_sub_C] at eqn

  -- Clean up zero/one coefficients and distribute products over sums
  simp only [List.sum_map_zero, mul_add, add_mul, List.sum_map_add,
    map_one, one_mul, map_zero, zero_mul, add_zero, map_neg, neg_mul, neg_add_rev,
    List.map_const', List.length_finRange, List.sum_replicate, smul_zero, mul_zero,
    zero_add] at eqn

  simp only [
    -- Associativity to obtain a right-leaning tree
    mul_assoc,
    -- Commutativity lemmas to move X (some _) to the left
    mul_left_comm (C _) (X (some _)) _, mul_left_comm (List.sum _) (X (some _)) _,
    mul_comm (C _) (X (some _)), mul_comm (List.sum _) (X (some _)),
    -- Move negations to the bottom
    neg_mul, mul_neg,
    -- Move constant multiplications (which the X (some _) terms should be) out of sums
    List.sum_map_mul_right, List.sum_map_mul_left] at eqn

  -- Apply MvPolynomial.optionEquivRight *here*, so that we can treat polynomials in Vars_X as constants
  replace eqn := congr_arg (MvPolynomial.optionEquivRight F Vars) eqn
  simp only [map_add, map_zero, map_mul, map_one,
    map_neg, AlgEquiv.list_map_sum, map_pow] at eqn
  simp only [optionEquivRight_C, optionEquivRight_X_none, optionEquivRight_X_some,
    optionEquivRight_to_MvPolynomial_Option] at eqn

  -- Move Cs back out so we can recognize the monomials
  simp only [← C_mul, ← C_pow, ← C_add, MvPolynomial.sum_map_C] at eqn

  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqn

  -- Extract the coefficients of the relevant toxic-waste monomials.
  -- Naming: h<a><b><c><d> is the coefficient of α^a β^b γ^c δ^d.
  have h2022 := congr_arg (coeff (Finsupp.single Vars.α 2 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h0222 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h1122 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h1022 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h0122 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h0022 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 2)) eqn
  have h1032 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 3 + Finsupp.single Vars.δ 2)) eqn
  have h2012 := congr_arg (coeff (Finsupp.single Vars.α 2 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
  have h0212 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
  have h1112 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
  have h1012 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
  have h0112 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 1 + Finsupp.single Vars.δ 2)) eqn
  have h2021 := congr_arg (coeff (Finsupp.single Vars.α 2 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
  have h0221 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
  have h1121 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
  have h1021 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 0 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
  have h0121 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 1)) eqn
  have h1120 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 2 + Finsupp.single Vars.δ 0)) eqn
  have h1102 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1 + Finsupp.single Vars.γ 0 + Finsupp.single Vars.δ 2)) eqn

  clear eqn

  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h2022 h0222 h1122 h1022 h0122 h0022 h1032 h2012 h0212 h1112 h1012 h0112 h2021 h0221 h1121 h1021 h0121 h1120 h1102

  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at h2022 h0222 h1122 h1022 h0122 h0022 h1032 h2012 h0212 h1112 h1012 h0112 h2021 h0221 h1121 h1021 h0121 h1120 h1102

  simp (config := {decide := true}) only [ite_false, ite_true] at h2022 h0222 h1122 h1022 h0122 h0022 h1032 h2012 h0212 h1112 h1012 h0112 h2021 h0221 h1121 h1021 h0121 h1120 h1102
  simp only [neg_zero, add_zero, zero_add] at h2022 h0222 h1122 h1022 h0122 h0022 h1032 h2012 h0212 h1112 h1012 h0112 h2021 h0221 h1121 h1021 h0121 h1120 h1102

  -- Step 2: Reduce the computable-polynomial goal to the corresponding mathlib `Polynomial`
  -- identity, so that goal and coefficient equations speak about the same atoms
  have ht : t = ∏ i ∈ (Finset.univ : Finset (Fin n_wit)),
      (CompPoly.CPolynomial.X - CompPoly.CPolynomial.C (r i)) := rfl
  rw [ht]
  apply CompPoly.CPolynomial.toPoly_injective
  simp only [CompPoly.CPolynomial.toPoly_mul, CompPoly.CPolynomial.toPoly_add,
    CompPoly.CPolynomial.toPoly_list_sum,
    List.map_map, Function.comp_def, CompPoly.CPolynomial.C_toPoly,
    CompPoly.CPolynomial.X_toPoly, CompPoly.CPolynomial.toPoly_pow,
    CompPoly.CPolynomial.toPoly_prod, CompPoly.CPolynomial.toPoly_X_sub_C]

  -- Step 3: Name the atoms of the coefficient system.
  --
  -- Statement-side QAP combinations

  generalize (List.sum (List.map (fun i => Polynomial.C (stmt i) * (u_stmt i).toPoly) (List.finRange n_stmt))) = u_io at *

  generalize (List.sum (List.map (fun i => Polynomial.C (stmt i) * (v_stmt i).toPoly) (List.finRange n_stmt))) = v_io at *

  generalize (List.sum (List.map (fun i => Polynomial.C (stmt i) * (w_stmt i).toPoly) (List.finRange n_stmt))) = w_io at *

  -- Components of A

  generalize (Polynomial.C (prover Proof_Idx.A SRS_Elements_Idx.α)) = A_alpha at *

  generalize (Polynomial.C (prover Proof_Idx.A SRS_Elements_Idx.β)) = A_beta at *

  generalize (Polynomial.C (prover Proof_Idx.A SRS_Elements_Idx.γ)) = A_gamma at *

  generalize (Polynomial.C (prover Proof_Idx.A SRS_Elements_Idx.δ)) = A_delta at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.A (SRS_Elements_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var))) = A_x at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.A (SRS_Elements_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i)))) (List.finRange (n_var - 1)))) = A_h at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.A (SRS_Elements_Idx.y x)) * (u_stmt x).toPoly) (List.finRange n_stmt))) = A_u_stmt at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.A (SRS_Elements_Idx.y x)) * (v_stmt x).toPoly) (List.finRange n_stmt))) = A_v_stmt at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.A (SRS_Elements_Idx.y x)) * (w_stmt x).toPoly) (List.finRange n_stmt))) = A_w_stmt at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.A (SRS_Elements_Idx.q x)) * (u_wit x).toPoly) (List.finRange n_wit))) = A_u_wit at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.A (SRS_Elements_Idx.q x)) * (v_wit x).toPoly) (List.finRange n_wit))) = A_v_wit at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.A (SRS_Elements_Idx.q x)) * (w_wit x).toPoly) (List.finRange n_wit))) = A_w_wit at *

  -- Components of B

  generalize (Polynomial.C (prover Proof_Idx.B SRS_Elements_Idx.α)) = B_alpha at *

  generalize (Polynomial.C (prover Proof_Idx.B SRS_Elements_Idx.β)) = B_beta at *

  generalize (Polynomial.C (prover Proof_Idx.B SRS_Elements_Idx.γ)) = B_gamma at *

  generalize (Polynomial.C (prover Proof_Idx.B SRS_Elements_Idx.δ)) = B_delta at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.B (SRS_Elements_Idx.x_pow x)) * Polynomial.X ^ (x : ℕ)) (List.finRange n_var))) = B_x at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.B (SRS_Elements_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i)))) (List.finRange (n_var - 1)))) = B_h at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.B (SRS_Elements_Idx.y x)) * (u_stmt x).toPoly) (List.finRange n_stmt))) = B_u_stmt at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.B (SRS_Elements_Idx.y x)) * (v_stmt x).toPoly) (List.finRange n_stmt))) = B_v_stmt at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.B (SRS_Elements_Idx.y x)) * (w_stmt x).toPoly) (List.finRange n_stmt))) = B_w_stmt at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.B (SRS_Elements_Idx.q x)) * (u_wit x).toPoly) (List.finRange n_wit))) = B_u_wit at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.B (SRS_Elements_Idx.q x)) * (v_wit x).toPoly) (List.finRange n_wit))) = B_v_wit at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.B (SRS_Elements_Idx.q x)) * (w_wit x).toPoly) (List.finRange n_wit))) = B_w_wit at *

  -- Components of C appearing in the extracted equations and the goal

  generalize (List.sum (List.map (fun x : Fin (n_var - 1) => Polynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.x_pow_times_t x)) * (Polynomial.X ^ (x : ℕ) * ∏ i : Fin n_wit, (Polynomial.X - Polynomial.C (r i)))) (List.finRange (n_var - 1)))) = C_h at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.q x)) * (u_wit x).toPoly) (List.finRange n_wit))) = C_u_wit at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.q x)) * (v_wit x).toPoly) (List.finRange n_wit))) = C_v_wit at *

  generalize (List.sum (List.map (fun x => Polynomial.C (prover Proof_Idx.C (SRS_Elements_Idx.q x)) * (w_wit x).toPoly) (List.finRange n_wit))) = C_w_wit at *

  -- Step 4: The case analysis. The α²γ²δ² coefficient forces A_α · B_α = 0; in the symmetric
  -- setting `A` and `B` are interchangeable, and the two cases correspond to the two possible
  -- role assignments. In each case every junk component is forced to vanish; the certificates
  -- below were derived and checked symbolically.
  have key : A_alpha * B_alpha = 0 := by linear_combination -h2022
  rcases mul_eq_zero.mp key with hAa0 | hBa0
  · -- Case A_α = 0: B carries the α-role and A carries the β-role.
    have hBb : B_beta = 0 := by
      linear_combination (B_beta) * h1122 + (-B_alpha) * h0222 + (B_beta^2) * hAa0
    have hAg : A_gamma = 0 := by
      linear_combination (A_gamma) * h1122 + (-A_beta) * h1032 + (-A_beta*B_gamma + A_gamma*B_beta) * hAa0
    have hQuB : B_u_wit = 0 := by
      linear_combination (B_u_wit) * h1122 + (-B_alpha) * h0221 + (B_beta*B_u_wit) * hAa0 + (-A_u_wit*B_alpha) * hBb
    have hYuB : B_u_stmt = 0 := by
      linear_combination (B_u_stmt) * h1122 + (-B_alpha) * h0212 + (B_beta*B_u_stmt) * hAa0 + (-A_u_stmt*B_alpha) * hBb
    have hQvA : A_v_wit = 0 := by
      linear_combination (A_v_wit) * h1122 + (-A_beta) * h2021 + (-A_beta*B_v_wit + A_v_wit*B_beta) * hAa0
    have hYvA : A_v_stmt = 0 := by
      linear_combination (A_v_stmt) * h1122 + (-A_beta) * h2012 + (-A_beta*B_v_stmt + A_v_stmt*B_beta) * hAa0
    have hMQ : A_beta*B_v_wit + A_u_wit*B_alpha = 0 := by
      linear_combination (-1) * h1121 + (-B_u_wit) * hAa0 + (-A_v_wit) * hBb
    have hMY : A_beta*B_v_stmt + A_u_stmt*B_alpha = 0 := by
      linear_combination (-1) * h1112 + (-B_u_stmt) * hAa0 + (-A_v_stmt) * hBb
    have hAbQvB : A_beta*B_v_wit = 0 := mul_self_eq_zero.mp (by
      linear_combination (A_beta*B_v_wit) * hMQ + (A_beta*B_alpha) * h1120 + (A_beta*A_v_wit*B_alpha) * hQuB)
    have hQvB : B_v_wit = 0 := by
      linear_combination (B_v_wit) * h1122 + (B_alpha) * hAbQvB + (B_beta*B_v_wit) * hAa0
    have hQuA : A_u_wit = 0 := by
      linear_combination (A_u_wit) * h1122 + (A_beta) * hMQ + (-A_beta^2) * hQvB + (A_u_wit*B_beta) * hAa0
    have hAbYvB : A_beta*B_v_stmt = 0 := mul_self_eq_zero.mp (by
      linear_combination (A_beta*B_v_stmt) * hMY + (A_beta*B_alpha) * h1102 + (A_beta*A_v_stmt*B_alpha) * hYuB)
    have hYvB : B_v_stmt = 0 := by
      linear_combination (B_v_stmt) * h1122 + (B_alpha) * hAbYvB + (B_beta*B_v_stmt) * hAa0
    have hYuA : A_u_stmt = 0 := by
      linear_combination (A_u_stmt) * h1122 + (A_beta) * hMY + (-A_beta^2) * hYvB + (A_u_stmt*B_beta) * hAa0
    have hWA : A_h + A_w_wit = 0 := by
      linear_combination (A_h + A_w_wit) * h1122 + (-A_beta) * h1021 + (-A_beta*B_h - A_beta*B_w_wit + A_h*B_beta + A_w_wit*B_beta) * hAa0 + (-A_beta*A_x) * hQvB + (-A_beta*B_x) * hQvA
    have hWB : B_h + B_w_wit = 0 := by
      linear_combination (B_h + B_w_wit) * h1122 + (-B_alpha) * h0121 + (B_beta*B_h + B_beta*B_w_wit) * hAa0 + (-A_h*B_alpha - A_w_wit*B_alpha) * hBb + (-A_x*B_alpha) * hQuB + (-B_alpha*B_x) * hQuA
    have hYwA : A_w_stmt = 0 := by
      linear_combination (A_w_stmt) * h1122 + (-A_beta) * h1012 + (-A_beta*B_w_stmt + A_w_stmt*B_beta) * hAa0 + (-A_beta*A_x) * hYvB + (-A_beta*B_x) * hYvA
    have hYwB : B_w_stmt = 0 := by
      linear_combination (B_w_stmt) * h1122 + (-B_alpha) * h0112 + (B_beta*B_w_stmt) * hAa0 + (-A_w_stmt*B_alpha) * hBb + (-A_x*B_alpha) * hYuB + (-B_alpha*B_x) * hYuA
    linear_combination (C_v_wit + v_io) * h0122 + (A_beta*B_x) * h1022 + (-1) * h0022 + (-A_x*B_x) * h1122 + (A_beta*B_x^2 - A_x*B_beta*B_x) * hAa0 + (A_x*C_v_wit + A_x*v_io) * hBb + (A_beta*B_v_stmt*B_x + B_u_stmt*C_v_wit + B_u_stmt*v_io - B_w_stmt) * hAg + (A_delta*C_v_wit + A_delta*v_io) * hQuB + (A_beta*B_delta*B_x) * hQvA + (A_beta*B_gamma*B_x) * hYvA + (A_beta*A_delta*B_x) * hQvB + (B_delta*C_v_wit + B_delta*v_io) * hQuA + (B_gamma*C_v_wit + B_gamma*v_io) * hYuA + (-B_delta) * hWA + (-A_delta) * hWB + (-B_gamma) * hYwA
  · -- Case B_α = 0: A carries the α-role and B carries the β-role (the honest assignment).
    have hAb : A_beta = 0 := by
      linear_combination (A_beta) * h1122 + (-A_alpha) * h0222 + (A_beta^2) * hBa0
    have hBg : B_gamma = 0 := by
      linear_combination (B_gamma) * h1122 + (-B_beta) * h1032 + (A_beta*B_gamma - A_gamma*B_beta) * hBa0
    have hQuA : A_u_wit = 0 := by
      linear_combination (A_u_wit) * h1122 + (-A_alpha) * h0221 + (A_beta*A_u_wit) * hBa0 + (-A_alpha*B_u_wit) * hAb
    have hYuA : A_u_stmt = 0 := by
      linear_combination (A_u_stmt) * h1122 + (-A_alpha) * h0212 + (A_beta*A_u_stmt) * hBa0 + (-A_alpha*B_u_stmt) * hAb
    have hQvB : B_v_wit = 0 := by
      linear_combination (B_v_wit) * h1122 + (-B_beta) * h2021 + (A_beta*B_v_wit - A_v_wit*B_beta) * hBa0
    have hYvB : B_v_stmt = 0 := by
      linear_combination (B_v_stmt) * h1122 + (-B_beta) * h2012 + (A_beta*B_v_stmt - A_v_stmt*B_beta) * hBa0
    have hMQ : A_alpha*B_u_wit + A_v_wit*B_beta = 0 := by
      linear_combination (-1) * h1121 + (-A_u_wit) * hBa0 + (-B_v_wit) * hAb
    have hMY : A_alpha*B_u_stmt + A_v_stmt*B_beta = 0 := by
      linear_combination (-1) * h1112 + (-A_u_stmt) * hBa0 + (-B_v_stmt) * hAb
    have hBbQvA : A_v_wit*B_beta = 0 := mul_self_eq_zero.mp (by
      linear_combination (A_v_wit*B_beta) * hMQ + (A_alpha*B_beta) * h1120 + (A_alpha*B_beta*B_v_wit) * hQuA)
    have hQvA : A_v_wit = 0 := by
      linear_combination (A_v_wit) * h1122 + (A_alpha) * hBbQvA + (A_beta*A_v_wit) * hBa0
    have hQuB : B_u_wit = 0 := by
      linear_combination (B_u_wit) * h1122 + (B_beta) * hMQ + (-B_beta^2) * hQvA + (A_beta*B_u_wit) * hBa0
    have hBbYvA : A_v_stmt*B_beta = 0 := mul_self_eq_zero.mp (by
      linear_combination (A_v_stmt*B_beta) * hMY + (A_alpha*B_beta) * h1102 + (A_alpha*B_beta*B_v_stmt) * hYuA)
    have hYvA : A_v_stmt = 0 := by
      linear_combination (A_v_stmt) * h1122 + (A_alpha) * hBbYvA + (A_beta*A_v_stmt) * hBa0
    have hYuB : B_u_stmt = 0 := by
      linear_combination (B_u_stmt) * h1122 + (B_beta) * hMY + (-B_beta^2) * hYvA + (A_beta*B_u_stmt) * hBa0
    have hWB : B_h + B_w_wit = 0 := by
      linear_combination (B_h + B_w_wit) * h1122 + (-B_beta) * h1021 + (A_beta*B_h + A_beta*B_w_wit - A_h*B_beta - A_w_wit*B_beta) * hBa0 + (-B_beta*B_x) * hQvA + (-A_x*B_beta) * hQvB
    have hWA : A_h + A_w_wit = 0 := by
      linear_combination (A_h + A_w_wit) * h1122 + (-A_alpha) * h0121 + (A_beta*A_h + A_beta*A_w_wit) * hBa0 + (-A_alpha*B_h - A_alpha*B_w_wit) * hAb + (-A_alpha*B_x) * hQuA + (-A_alpha*A_x) * hQuB
    have hYwB : B_w_stmt = 0 := by
      linear_combination (B_w_stmt) * h1122 + (-B_beta) * h1012 + (A_beta*B_w_stmt - A_w_stmt*B_beta) * hBa0 + (-B_beta*B_x) * hYvA + (-A_x*B_beta) * hYvB
    have hYwA : A_w_stmt = 0 := by
      linear_combination (A_w_stmt) * h1122 + (-A_alpha) * h0112 + (A_beta*A_w_stmt) * hBa0 + (-A_alpha*B_w_stmt) * hAb + (-A_alpha*B_x) * hYuA + (-A_alpha*A_x) * hYuB
    linear_combination (C_v_wit + v_io) * h0122 + (A_x*B_beta) * h1022 + (-1) * h0022 + (-A_x*B_x) * h1122 + (-A_beta*A_x*B_x + A_x^2*B_beta) * hBa0 + (B_x*C_v_wit + B_x*v_io) * hAb + (A_u_stmt*C_v_wit + A_u_stmt*v_io + A_v_stmt*A_x*B_beta - A_w_stmt) * hBg + (B_delta*C_v_wit + B_delta*v_io) * hQuA + (A_delta*A_x*B_beta) * hQvB + (A_gamma*A_x*B_beta) * hYvB + (A_x*B_beta*B_delta) * hQvA + (A_delta*C_v_wit + A_delta*v_io) * hQuB + (A_gamma*C_v_wit + A_gamma*v_io) * hYuB + (-A_delta) * hWB + (-B_delta) * hWA + (-A_gamma) * hYwB

end soundness

end Groth16TypeI

end Groth16TypeI
