
import FormalSnarksProject.SoundnessTactic.SoundnessProver


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

example (a b c d e f g h i j : F)
    (h1 : a * b = 0) (h2 : c * d + b = 0) (h3 : (d + e) * f = 0) (h4 : g * (f + h) = 0)
    (h5 : h + i * j = 0) :
    a * c * e * g * i * j = 0  := by

  polyrith

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
