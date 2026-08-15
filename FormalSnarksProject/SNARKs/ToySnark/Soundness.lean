module

public import FormalSnarksProject.SNARKs.ToySnark.Defs

/-!

# ToySnark Soundness

This file contains the soundness proof for the toy SNARK defined in `Defs.lean`.

-/

@[expose] public section

open scoped BigOperators

section ToySnark

open MvPolynomial Option List
open CPoly

namespace ToySnark

section soundness



-- Remove time-out
set_option maxHeartbeats 0 in -- 0 means no limit
lemma soundness
    {F : Type} [Field F] [BEq F] [LawfulBEq F] :
    (AGMProofSystemInstantiation.soundness
      F
      (ToySnark
        (F := F))
      (WitEntries -> F)
      (fun (stmt : StmtEntries → F) (wit : WitEntries -> F) =>
        wit WitEntries.A * stmt StmtEntries.y = stmt StmtEntries.z -- - wit WitEntries.I
        ∨
        wit WitEntries.B * stmt StmtEntries.x = stmt StmtEntries.z -- - wit WitEntries.I
      )
      (fun prover i => prover.fst Proof_G1_Idx.Pf (if i = WitEntries.A then .α else .β))

    ) := by
  unfold AGMProofSystemInstantiation.soundness AGMProofSystemInstantiation.verify AGMProofSystemInstantiation.check_poly AGMProofSystemInstantiation.pairing_poly AGMProofSystemInstantiation.proof_element_G1_as_poly AGMProofSystemInstantiation.proof_element_G2_as_poly
  intros stmt prover eqns'
  rcases eqns' with ⟨eqns, null⟩
  have eqn := eqns ()
  clear eqns null

  -- Step 1: Obtain the coefficient equations of the polynomials.
  --
  -- Bridge helpers: `CPoly.COrdMvPolynomial.ordPolyRingEquiv` (whose coercion is `CPoly.COrdMvPolynomial.fromCOrdMvPolynomial`) carries
  -- the computable `COrdMvPolynomial` verification equation over to mathlib's `MvPolynomial`.
  have equivC : ∀ c : F,
      (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) (CPoly.COrdMvPolynomial.C c) = C c :=
    fun c => CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_C c
  have equivX : ∀ v : Option Vars,
      (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) (CPoly.COrdMvPolynomial.X v) = X v :=
    fun v => CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_X v

  -- Expand the `FinEnum` index enumerations into their concrete defining lists
  simp only [toList_PairingsIdx, toList_Proof_G1_Idx, toList_Proof_G2_Idx,
    toList_SRS_Elements_G1_Idx, toList_SRS_Elements_G2_Idx,
    List.map_cons, List.map_nil, List.map_map, Function.comp_def,
    List.sum_cons, List.sum_nil] at eqn

  -- Transport the verification equation to mathlib's `MvPolynomial`
  replace eqn := congr_arg (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) eqn
  simp only [_root_.map_add, _root_.map_mul, _root_.map_neg, _root_.map_one, _root_.map_zero,
    map_pow, map_list_sum, List.map_map, Function.comp_def, equivC, equivX] at eqn

  -- Clean up zero/one coefficients and distribute products over sums
  simp only [mul_add, add_mul, List.sum_map_add,
    _root_.map_one, one_mul, _root_.map_zero, zero_mul, add_zero, _root_.map_neg, neg_mul,
    neg_add_rev, mul_zero, zero_add] at eqn

  -- Move all the X (some _) terms to the left, and out of sums
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

  -- Apply MvPolynomial.optionEquivRight *here*,
  -- so that we can treat polynomials in Vars_X as constants
  replace eqn := congr_arg (MvPolynomial.optionEquivRight F Vars) eqn
  simp only [_root_.map_add, _root_.map_zero, _root_.map_mul, _root_.map_one,
    _root_.map_neg, AlgEquiv.list_map_sum, map_pow] at eqn
  simp only [MvPolynomial.optionEquivRight_C, MvPolynomial.optionEquivRight_X_none,
    MvPolynomial.optionEquivRight_X_some] at eqn

  simp only [MvPolynomial.X, C_apply, MvPolynomial.monomial_mul, one_mul, mul_one, add_zero,
    zero_add, mul_add, add_mul] at eqn

  have h20 := congr_arg (coeff (Finsupp.single Vars.α 2 + Finsupp.single Vars.β 0)) eqn
  have h11 := congr_arg (coeff (Finsupp.single Vars.α 1 + Finsupp.single Vars.β 1)) eqn
  have h02 := congr_arg (coeff (Finsupp.single Vars.α 0 + Finsupp.single Vars.β 2)) eqn

  clear eqn

  simp only [coeff_monomial, coeff_add, coeff_neg, coeff_zero] at h20 h11 h02

  simp only [Vars.finsupp_eq_ext, Finsupp.single_apply, Finsupp.add_apply] at h20 h11 h02

  simp [ite_true, ite_self, add_zero, ite_false, and_self, zero_add,
    one_ne_zero, and_false, false_and, add_eq_zero, mul_eq_zero,
    add_eq_left, zero_ne_one, and_true, true_and, neg_zero] at h20 h11 h02 ⊢

  -- Completely remove references to Polynomial
  simp only [add_neg_eq_zero, Polynomial.C_inj, ← Polynomial.C_add, ← Polynomial.C_mul] at h20 h11 h02

  integral_domain_tactic

end soundness


-- TODO I'm using lists rather than finsets now, so I think I can get rid of all the finset lemmas

end ToySnark

end ToySnark
