section test

universes u


/-- The finite field parameter of our SNARK -/
parameters {R vars : Type u}
-- parameter [ring R]


-- lemma zero_eq_zero [integral_domain R] : (0 : R) = 0 ↔ true := 
-- begin
--   simp only [eq_self_iff_true],
-- end

-- example [integral_domain R] (a b c d e f g h i : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) (h4 : h * i = 0): c * e + f * d = h :=
-- begin
--   -- integral_domain_tactic,
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   -- integral_domain_tactic',
--   sorry,
-- end

-- example [integral_domain R] (a b c d e f g h i : R) (h11 : ¬a = 0) (h12 : ¬b = 0) (h4 : h = 0 ∨ i = 0): f * 0 = h :=
-- begin
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   cases ‹_ ∨ _› with found_zero found_zero,
--   -- tactic.context_name_getter,
--   rw found_zero at *,
--   rw found_zero at *,
--   sorry,
-- end

-- example [integral_domain R] (a b c d e f : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = 0 :=
-- begin
--   simp only [] with integral_domain_simp
--     at * {fail_if_unchanged := ff},
--   tactic.integral_domain_tactic_v3,
--   -- tactic.integral_domain_tactic,
-- end

-- example [integral_domain R] (a b c d e f g : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = g :=
-- begin
--   tactic.integral_domain_tactic,
--   sorry, 
-- end

-- example [integral_domain R] (a b c d e f : R) (h11 : ¬a = 0) (h12 : ¬b = 0)  (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = 0 :=
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
