/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import FormalSnarksProject.SNARKs.ToySnark.Defs

/-!

# ToySnark Completeness

This file contains the completeness proof for the toy SNARK defined in `Defs.lean`.

The verifier's single check is `Pf · (x·α + y·β) - z·α·β = 0`, where the proof element
`Pf = A·α + B·β` is a combination of the two SRS elements. Comparing coefficients on `α²`, `β²`
and `α·β`, a proof is accepted iff `A·x = 0`, `B·y = 0` and `A·y + B·x = z`. Completeness is
therefore stated for exactly this "designed" relation, with the honest prover placing the
witness values `A`, `B` on the two slots of `Pf`.

Note that this relation is strictly stronger than the disjunction `A·y = z ∨ B·x = z` used in
`Soundness.lean` (which is what an extractor can guarantee): completeness for the disjunction
itself is false, e.g. `x = y = z = 1`, `A = 1` satisfies `A·y = z`, but the checks force
`A = B = 0` and hence `z = 0` whenever `x` and `y` are both nonzero.

-/

public section

open scoped BigOperators

section ToySnark

open MvPolynomial Option AGMProofSystemInstantiation

namespace ToySnark

section completeness

noncomputable def wit_prover (F : Type) [Field F] [BEq F] [LawfulBEq F]
    (_stmt : StmtEntries → F) (wit : WitEntries → F) :
    (ToySnark (F := F)).Prover where
  fst pf_elem srs_elem := match pf_elem with
    | Proof_G1_Idx.Pf => match srs_elem with
      | SRS_Elements_G1_Idx.α => wit WitEntries.A
      | SRS_Elements_G1_Idx.β => wit WitEntries.B
  -- There are no proof elements in the second group
  snd _ _ := 0

lemma is_complete
    {F : Type} [Field F] [BEq F] [LawfulBEq F] :
    (completeness
      F
      (ToySnark (F := F))
      (WitEntries -> F)
      (fun (stmt : StmtEntries → F) (wit : WitEntries -> F) =>
        wit WitEntries.A * stmt StmtEntries.x = 0
        ∧ wit WitEntries.B * stmt StmtEntries.y = 0
        ∧ wit WitEntries.A * stmt StmtEntries.y + wit WitEntries.B * stmt StmtEntries.x
            = stmt StmtEntries.z)
      (wit_prover F)
    ) := by
  unfold completeness verify check_poly pairing_poly proof_element_G1_as_poly
    proof_element_G2_as_poly wit_prover
  intros stmt wit hrel
  obtain ⟨h1, h2, h3⟩ := hrel

  -- Bridge helpers: `CPoly.COrdMvPolynomial.ordPolyRingEquiv` (whose coercion is `CPoly.COrdMvPolynomial.fromCOrdMvPolynomial`) carries
  -- the computable `COrdMvPolynomial` verification equation over to mathlib's `MvPolynomial`.
  have equivC : ∀ c : F,
      (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) (CPoly.COrdMvPolynomial.C c) = C c :=
    fun c => CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_C c
  have equivX : ∀ v : Option Vars,
      (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)) (CPoly.COrdMvPolynomial.X v) = X v :=
    fun v => CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_X v

  constructor
  · intro check_idx
    -- Expand the enumerations into their concrete defining lists
    simp only [toList_PairingsIdx, toList_Proof_G1_Idx, toList_Proof_G2_Idx,
      toList_SRS_Elements_G1_Idx, toList_SRS_Elements_G2_Idx,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    -- Transport the goal to mathlib's `MvPolynomial`
    apply (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := Option Vars) (R := F)).injective
    simp only [_root_.map_add, _root_.map_mul, _root_.map_neg, _root_.map_one, _root_.map_zero,
      _root_.map_pow, equivC, equivX]
    -- Clean up zero/one coefficients
    simp only [one_mul, zero_mul, mul_zero, add_zero, zero_add, neg_mul]
    -- The relation, pushed into constant polynomials
    have hC1 := congrArg (MvPolynomial.C : F → MvPolynomial (Option Vars) F) h1
    have hC2 := congrArg (MvPolynomial.C : F → MvPolynomial (Option Vars) F) h2
    have hC3 := congrArg (MvPolynomial.C : F → MvPolynomial (Option Vars) F) h3
    simp only [_root_.map_mul, _root_.map_add, _root_.map_zero] at hC1 hC2 hC3
    linear_combination
      ((X (some Vars.α) : MvPolynomial (Option Vars) F) * X (some Vars.α)) * hC1
      + (X (some Vars.β) * X (some Vars.β)) * hC2
      + (X (some Vars.α) * X (some Vars.β)) * hC3
  · -- No identified proof elements
    intro pfs hpfs
    exact absurd hpfs List.not_mem_nil

end completeness

end ToySnark

end ToySnark
