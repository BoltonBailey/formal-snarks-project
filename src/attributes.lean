
import data.mv_polynomial.basic
import .general_lemmas.mv_X_mul
import .general_lemmas.single_antidiagonal

section

open mv_polynomial

universes u

@[simp] lemma eq_zero_of_zero_eq (R : Type u) [has_zero R] (r : R) : 0 = r ↔ r = 0 :=
begin
  exact eq_comm,
end

@[simp] lemma zero_sub_eq_iff (R : Type u) [add_comm_group R] (a b : R) : 0 - a = b ↔ a + b = 0 :=
begin
  split,
  { intro h, rw <-h, abel, },
  { intro h, rw <-h, abel, },
end

run_cmd mk_simp_attr `integral_domain_simp
run_cmd tactic.add_doc_string `simp_attr.integral_domain_simp "Attribute for lemmas that are useful in simplifying systems of equations in an integral domain"

attribute [integral_domain_simp] add_zero zero_add mul_zero zero_mul mul_one one_mul false_or or_false true_or or_true polynomial.C_eq_zero ring_hom.map_zero true_or eq_self_iff_true ne.def mul_eq_zero eq_zero_of_zero_eq one_ne_zero mul_ne_zero_iff zero_sub_eq_iff
-- attribute [integral_domain] polynomial.sum
-- attribute [integral_domain] finsupp.sum
-- attribute [integral_domain] mul_add
-- attribute [integral_domain] add_mul
-- attribute [integral_domain] finset.sum_mul
-- attribute [integral_domain] finset.mul_sum
-- attribute [integral_domain] finset.sum_add_distrib
-- attribute [integral_domain] mul_assoc
-- attribute [integral_domain] finsupp.smul_sum
-- attribute [integral_domain] mul_smul_comm
-- attribute [integral_domain] smul_add
-- attribute [integral_domain] mul_smul
-- attribute [integral_domain] smul_mul_assoc

end