
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


-- attribute [integral_domain_simp] add_zero zero_add mul_zero zero_mul mul_one one_mul false_or or_false true_or or_true polynomial.C_eq_zero ring_hom.map_zero eq_self_iff_true ne.def mul_eq_zero eq_zero_of_zero_eq one_ne_zero mul_ne_zero_iff zero_sub_eq_iff not_true not_false

-- Verison without polynomial manipulation
attribute [integral_domain_simp] add_zero zero_add mul_zero zero_mul mul_one one_mul false_or or_false true_or or_true eq_self_iff_true ne.def mul_eq_zero eq_zero_of_zero_eq one_ne_zero mul_ne_zero_iff zero_sub_eq_iff not_true not_false


run_cmd mk_simp_attr `finsupp_simp
run_cmd tactic.add_doc_string `simp_attr.finsupp_simp "Attribute for lemmas that are useful in finsupp statements"


-- Verison without polynomial manipulation
attribute [finsupp_simp] nat.one_ne_zero finsupp.single_eq_of_ne finsupp.single_eq_same add_zero if_true if_false  pi.add_apply pi.zero_apply
  eq_self_iff_true not_true eq_zero_of_zero_eq if_false ne.def nat.sub_zero zero_add not_false_iff bit0_eq_zero
  and_self finsupp.coe_nat_sub and_false finsupp.coe_add false_and pi.sub_apply finsupp.coe_zero
    nat.succ_ne_zero     
  

end