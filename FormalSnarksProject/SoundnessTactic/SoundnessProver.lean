
import Lean.Elab.Tactic
import Mathlib
import FormalSnarksProject.SoundnessTactic.CasesOr

@[simp] lemma eq_zero_of_zero_eq (R : Type u) [Zero R] (r : R) : 0 = r ↔ r = 0 := by
  exact eq_comm

@[simp] lemma zero_sub_eq_iff (R : Type u) [AddCommGroup R] (a b : R) : 0 - a = b ↔ a + b = 0 := by
  constructor
  · aesop?
  · intro h
    rw [← add_right_inj a]
    simp [h]


syntax "simplify_mvpoly_option_eqn" : tactic

-- TODO instead of eqn, it should allow arbitrary location
macro_rules
| `(tactic| simplify_mvpoly_option_eqn) =>
  `(tactic|
    simp only [monomial_zero', List.singleton_append, List.cons_append, List.append_assoc,
      List.map_cons, Sum.elim_inl, Sum.elim_inr, List.map_append, List.map_map, List.sum_cons,
      List.sum_append, List.map_nil, List.sum_nil, add_zero, Sum.elim_lam_const_lam_const, map_one,
      one_mul, map_zero, zero_mul, map_neg, neg_mul, neg_add_rev, zero_add, mul_zero,
      -- Note: everything above is @simp tagged
      Function.comp, List.sum_map_zero] at eqn;
    simp only [mul_add, add_mul, List.sum_map_add] at eqn;
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
      List.sum_map_mul_right, List.sum_map_mul_left] at eqn;

    -- Apply MvPolynomial.optionEquivRight *here*, so that we can treat polynomials in Vars_X as constants
    trace "Converting to MvPolynomial over Polynomials";
    replace eqn := congr_arg (MvPolynomial.optionEquivRight F Vars) eqn;
    simp only [AlgEquiv.map_add, AlgEquiv.map_zero, AlgEquiv.map_mul, AlgEquiv.map_one,
      AlgEquiv.map_neg, AlgEquiv.list_map_sum, AlgEquiv.map_pow] at eqn;
    simp only [MvPolynomial.optionEquivRight_C, MvPolynomial.optionEquivRight_X_none, MvPolynomial.optionEquivRight_X_some, optionEquivRight_to_MvPolynomial_Option] at eqn;

    -- Move Cs back out so we can recognize the monomials
    simp only [←MvPolynomial.C_mul, ←MvPolynomial.C_pow, ←MvPolynomial.C_add,
      MvPolynomial.sum_map_C] at eqn;

    simp only [MvPolynomial.X, C_apply, MvPolynomial.monomial_mul, one_mul, mul_one, add_zero, zero_add, mul_add, add_mul] at eqn
  )

syntax "polynomial_ext" : tactic

macro_rules
| `(tactic| polynomial_ext) =>
  `(tactic| sorry) -- TODO


syntax "integral_domain_tactic" : tactic

macro_rules
| `(tactic| integral_domain_tactic) =>
  `(tactic|
      trace "Call to integral_domain_tactic";
      -- trace_state;
      -- Factor statements of the form a * b = 0 into a = 0 ∨ b = 0
      -- Note that this also eliminates True and False hypotheses
      simp_all (config := {decide := false, failIfUnchanged := false}) only [
            -- Simplifications for true and false
            false_or, or_false, true_or, or_true, not_true, not_false_iff,
            -- Basic arithmetic simplifications
            add_zero, zero_add, mul_zero, zero_mul, mul_one, one_mul, neg_zero,
            -- Further arithmetic simplifications
            neg_eq_zero, add_eq_zero_iff_eq_neg,
            eq_self_iff_true, eq_zero_of_zero_eq, one_ne_zero, mul_ne_zero_iff, zero_sub_eq_iff,
            -- Key arithmetic simplification for integral domains: a * b = 0 ↔ a = 0 ∨ b = 0
            mul_eq_zero];
      first
        -- If we are done, halt
        | done
        -- If we have a hypothesis of the form a * b = 0, split into a = 0 ∨ b = 0, and recurse
        | cases_or _ ∨ _
          all_goals integral_domain_tactic
        -- If we cannot split, we skip, leaving the goal unsolved for the user to resolve
        | skip
   )

-- TODO it might be nice to have a cases tactic that chooses some new name and leaves it accessible
-- This might be done be using vanilla cases with a specific name, and then renaming that name to another random name
