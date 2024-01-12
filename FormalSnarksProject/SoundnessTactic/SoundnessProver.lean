
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
            eq_self_iff_true, Ne.def, eq_zero_of_zero_eq, one_ne_zero, mul_ne_zero_iff, zero_sub_eq_iff,
            -- Key arithmetic simplification for integral domains: a * b = 0 ↔ a = 0 ∨ b = 0
            mul_eq_zero];
      first
        -- If we are done, halt
        | done
        -- If we have a hypothesis of the form a * b = 0, split into a = 0 ∨ b = 0, and recurse
        | --try clear found_zero
          cases_or _ ∨ _
          all_goals integral_domain_tactic
          -- 2
          -- cases' ‹_ ∨ _› with found_zero found_zero
          -- all_goals integral_domain_tactic
          -- 3
          -- cases ‹_ ∨ _› with -- this will fail if we can't split, passing us to the skip case below
          -- | inl _ => integral_domain_tactic; skip
          -- | inr _ => integral_domain_tactic; skip
        -- If we cannot split, we skip, leaving the goal unsolved for the user to resolve
        | skip
   )

-- TODO it might be nice to have a cases tactic that chooses some new name and leaves it accessible
-- This might be done be using vanilla cases with a specific name, and then renaming that name to another random name

section test

-- Per the docs: "To obtain an integral domain use [CommRing α] [IsDomain α]"
variable {F R : Type} [Field F] [CommRing R] [IsDomain R]

-- This test case reflects a integral domain puzzle similar to ToySNARK
example (a b c d e : F)
    (h1 : a * c = 0) (h2 : b * d = 0) (h3 : a * d + b * c = e) :
    a * d = e ∨ b * c = e := by
  integral_domain_tactic

-- If the tactic can't solve the goal, it should leave the cases it found
example (a b c d e : F)
    (h1 : a * c = 0) (h2 : b * d = 0) (h3 : a * d + b * c = e) (foo : True ∧ True) :
    a * d = e + 1 ∨ b * c = e + 1 := by
  integral_domain_tactic
  repeat {sorry}

/-- This test case asks the tactic to unfurl a chain of 4 multiplications, with each next
multiplication becoming accessible when it is the the added value is zero. -/
example (a b c d e f g h : F)
    (h1 : a * b = 0) (h2 : b + c * d = 0) (h3 : d + e * f = 0) (h4 : f + g * h = 0) :
    a = 0 ∨ c = 0 ∨ e = 0 ∨ g = 0 ∨ h = 0 := by
  integral_domain_tactic -- TODO Should this really be 7 calls?

/-- This test case asks the tactic to unfurl a chain of 5 multiplications.
The addition is now in a variety of configurations
-/
example (a b c d e f g h i j : F)
    (h1 : a * b = 0) (h2 : c * d + b = 0) (h3 : (d + e) * f = 0) (h4 : g * (f + h) = 0)
    (h5 : h + i * j = 0) :
    a = 0 ∨ c = 0 ∨ e = 0 ∨ g = 0 ∨ i = 0 ∨ j = 0  := by
  integral_domain_tactic -- TODO Should this really be 10 calls?


/-- This test case starts with negated premises
-/
example (a b c d e f g h i : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) (h4 : h * i = 0): c * e + f * d = h * i := by
  integral_domain_tactic


-- Turn off autoimplicit so that misused variables are caught
set_option autoImplicit false

/-- This test case solves the TypeIII Groth16 integral domain puzzle,
as presented on pages 9-10 of Baghery et al. All sums are condensed to atoms
-/
example
    (sum_a_u sum_a_v sum_a_w : F)
    (A_1 A_2 sum_A_4_x sum_A_5_u sum_A_5_v sum_A_5_w sum_A_6_u sum_A_6_v sum_A_6_w sum_A_7_x_t : F)
    (B_1 B_2 B_3 sum_B_4_x : F)
    (sum_C_6_u sum_C_6_v sum_C_6_w sum_C_7_x_t : F)
    (hαβ : A_1 * B_1 = 1)
    (hββ : A_2 * B_1 = 0)
    (hββ_δ : sum_A_6_u * B_1 = 0)
    (hβα_δ : sum_A_6_v * B_1 = 0)
    (hβ_δ : (sum_A_6_w + sum_A_7_x_t) * B_1 + sum_A_6_u * sum_B_4_x = 0)
    (h_δ : (sum_A_6_w + sum_A_7_x_t) * sum_B_4_x = 0)
    (hββ_γ : sum_A_5_u * B_1 = 0)
    (hαβ_γ : sum_A_5_v * B_1 = 0)
    (hβ_γ : (sum_A_5_w) * B_1 + sum_A_5_u * sum_B_4_x = 0)
    (h_γ : (sum_A_5_w) * sum_B_4_x = 0)
    (hβ : sum_A_4_x * B_1 + sum_B_4_x * A_2 + sum_A_5_u * B_2 + sum_A_6_u * B_3 = sum_a_u + sum_C_6_u)
    (hα : sum_B_4_x * A_1 + sum_A_5_v * B_2 + sum_A_6_v * B_3 = sum_a_v + sum_C_6_v)
    (h1 : sum_A_4_x * sum_B_4_x + sum_A_5_w * B_2 + (sum_A_6_w + sum_A_7_x_t) * B_3 = sum_a_w + sum_C_6_w + sum_C_7_x_t) :
    (sum_a_u + sum_C_6_u) * (sum_a_v + sum_C_6_v) = sum_a_w + sum_C_6_w + sum_C_7_x_t := by
  integral_domain_tactic
  -- polyrith gives:
  linear_combination
    sum_A_4_x * sum_B_4_x * hαβ - 1 * A_1 * sum_B_4_x * hβ + (-(1 * sum_a_u) - 1 * sum_C_6_u) * hα +
      h1


-- example (a b c d e f g h i : R) (h11 : ¬a = 0) (h12 : ¬b = 0) (h4 : h = 0 ∨ i = 0): f * 0 = h := -- TODO uncomment this and turn it into a test
-- begin
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   cases ‹_ ∨ _› with found_zero found_zero,
--   -- tactic.context_name_getter,
--   rw found_zero at *,
--   rw found_zero at *,
--   sorry,
-- end

-- example (a b c d e f : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = 0 :=
-- begin
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   tactic.integral_domain_tactic_v3,
--   -- tactic.integral_domain_tactic,
-- end

-- example (a b c d e f g : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = g :=
-- begin
--   tactic.integral_domain_tactic,
--   sorry,
-- end

-- example (a b c d e f : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = 0 :=
-- begin
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   cases ‹_ ∨ _› with found_zero found_zero,
--   context_prop_name_getter,
--   simplify_everywhere,
--   simplify_at_name `h11,
--   simplify_at_name `h12,
--   simplify_at_name `found_zero,
--   sorry,
--   sorry,

-- end



end test
