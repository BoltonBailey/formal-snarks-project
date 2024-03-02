
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.Data.Polynomial.Eval
import FormalSnarksProject.SoundnessTactic.DeclareAttributes
-- import .general_lemmas.mv_X_mul
-- import .general_lemmas.single_antidiagonal
-- import .general_lemmas.mul_sum_symm

section

open MvPolynomial Lean.Meta

-- universes u

-- @[simp] lemma eq_zero_of_zero_eq (R : Type u) [has_zero R] (r : R) : 0 = r ↔ r = 0 :=
-- begin
--   exact eq_comm,
-- end

-- @[simp] lemma zero_sub_eq_iff (R : Type u) [add_comm_group R] (a b : R) : 0 - a = b ↔ a + b = 0 :=
-- begin
--   split,
--   { intro h, rw <-h, abel, },
--   { intro h, rw <-h, abel, },
-- end

-- /-- Attribute for lemmas that are useful in simplifying systems of equations in an integral domain -/
-- initialize integralDomainSimpExt : SimpExtension ←
--   registerSimpAttr `integral_domain_simp
--     "lemmas that are useful in simplifying systems of equations in an integral domain"


-- /-- Attribute for lemmas that are used in the conversion of mvPolynomial expressions to a normal
-- form consisting of adds of sums of muls of mv_polynomials -/
-- initialize polynomialNfExt : SimpExtension ←
--   registerSimpAttr `polynomial_nf
--     "lemmas that are used in the conversion of mv_polynomial expressions to a normal form consisting of adds of sums of muls of mv_polynomials"


attribute [polynomial_nf] Polynomial.eval₂
attribute [polynomial_nf] polynomial.sum
attribute [polynomial_nf] finsupp.sum
attribute [polynomial_nf] mul_add
attribute [polynomial_nf] add_mul
attribute [polynomial_nf] finset.sum_mul
attribute [polynomial_nf] finset.mul_sum
attribute [polynomial_nf] finset.sum_add_distrib

attribute [polynomial_nf] mul_assoc

attribute [polynomial_nf] finsupp.smul_sum
attribute [polynomial_nf] mul_smul_comm
attribute [polynomial_nf] smul_add
attribute [polynomial_nf] mul_smul
attribute [polynomial_nf] smul_mul_assoc

run_cmd mk_simp_attr `polynomial_nf_2
run_cmd tactic.add_doc_string `simp_attr.polynomial_nf_2 "Attribute for lemmas that are used in the conversion of mv_polynomial expressions to a normal form consisting of adds of sums of muls of mv_polynomials"

attribute [polynomial_nf_2] mul_add
attribute [polynomial_nf_2] add_mul
attribute [polynomial_nf_2] finset.sum_add_distrib
attribute [polynomial_nf_2] sum_X_mul
attribute [polynomial_nf_2] sum_C_mul
attribute [polynomial_nf_2] rearrange_constants_G2
attribute [polynomial_nf_2] rearrange_constants_G2_with_extra
attribute [polynomial_nf_2] rearrange_sums_G2
attribute [polynomial_nf_2] rearrange_sums_G2_with_extra
attribute [polynomial_nf_2] C_mul_C
-- attribute [polynomial_nf_2] finset.sum_hom
attribute [polynomial_nf_2] mv_polynomial.smul_eq_C_mul
attribute [polynomial_nf_2] mul_assoc
attribute [polynomial_nf_2] finsupp.smul_sum
attribute [polynomial_nf_2] mul_smul_comm
attribute [polynomial_nf_2] smul_add
attribute [polynomial_nf_2] mul_smul
attribute [polynomial_nf_2] smul_mul_assoc


run_cmd mk_simp_attr `polynomial_nf_3
run_cmd tactic.add_doc_string `simp_attr.polynomial_nf_3 "Attribute for lemmas that are used in the conversion of mv_polynomial expressions to a normal form consisting of adds of sums of muls of mv_polynomials"


attribute [polynomial_nf_3] mul_add
attribute [polynomial_nf_3] add_mul
attribute [polynomial_nf_3] finset.sum_add_distrib
-- attribute [polynomial_nf_3] sum_X_mul
-- attribute [polynomial_nf_3] sum_C_mul
attribute [polynomial_nf_3] mul_sum_symm
attribute [polynomial_nf_3] rearrange_constants_G2
attribute [polynomial_nf_3] rearrange_constants_G2_with_extra
attribute [polynomial_nf_3] rearrange_sums_G2
attribute [polynomial_nf_3] rearrange_sums_G2_with_extra
attribute [polynomial_nf_3] C_mul_C
-- attribute [polynomial_nf_3] finset.sum_hom
attribute [polynomial_nf_3] mv_polynomial.smul_eq_C_mul
attribute [polynomial_nf_3] mul_assoc
-- attribute [polynomial_nf_3] finsupp.smul_sum
-- attribute [polynomial_nf_3] mul_smul_comm
-- attribute [polynomial_nf_3] smul_add
-- attribute [polynomial_nf_3] mul_smul
-- attribute [polynomial_nf_3] smul_mul_assoc


run_cmd mk_simp_attr `rearrange
run_cmd tactic.add_doc_string `simp_attr.rearrange "TODO a few rearrangement lemmas"

-- attribute [rearrange] rearrange1
-- attribute [rearrange] rearrange2
-- attribute [rearrange] rearrange_constants_G2
-- attribute [rearrange] rearrange_smul_right



-- attribute [polynomial_nf] mv_polynomial.smul_eq_C_mul



run_cmd mk_simp_attr `coeff_simp
run_cmd tactic.add_doc_string `simp_attr.coeff_simp "Attribute for lemmas that are used in the simplification of statements about coefficients of mv_polynomials"


-- attribute [coeff_simp] mv_polynomial.coeff_mul
-- attribute [coeff_simp] single_1_antidiagonal
-- attribute [coeff_simp] single_2_antidiagonal
-- attribute [coeff_simp] finset.range
-- attribute [coeff_simp] finset.image




-- attribute [coeff_simp] mv_polynomial.X_pow_eq_single
attribute [coeff_simp] mv_polynomial.coeff_sum
attribute [coeff_simp] mv_polynomial.coeff_add
attribute [coeff_simp] mv_polynomial.coeff_smul

attribute [coeff_simp] mv_polynomial.coeff_C_mul
attribute [coeff_simp] mv_polynomial.coeff_monomial
attribute [coeff_simp] mv_polynomial.coeff_mul_X'
attribute [coeff_simp] mv_polynomial.coeff_X'
attribute [coeff_simp] coeff_X_mul'
attribute [coeff_simp] coeff_X_pow_mul'
attribute [coeff_simp] mv_polynomial.coeff_C
attribute [coeff_simp] mv_polynomial.coeff_X_pow


run_cmd mk_simp_attr `finsupp_eq
run_cmd tactic.add_doc_string `simp_attr.finsupp_eq "Attribute for lemmas that are used in the simplification of equality statements between finsupps"

attribute [finsupp_eq] finsupp.mem_support_iff
attribute [finsupp_eq] finsupp.single_apply
attribute [finsupp_eq] finsupp.add_apply
attribute [finsupp_eq] finsupp.sub_apply


-- Verison without polynomial manipulation
attribute [integral_domain_simp] add_zero zero_add mul_zero zero_mul mul_one one_mul false_or or_false true_or or_true eq_self_iff_true ne.def mul_eq_zero eq_zero_of_zero_eq one_ne_zero mul_ne_zero_iff zero_sub_eq_iff not_true not_false_iff


run_cmd mk_simp_attr `finsupp_simp
run_cmd tactic.add_doc_string `simp_attr.finsupp_simp "Attribute for lemmas that are useful in finsupp statements"

lemma zero_ne_succ (n : ℕ) : 0 ≠ nat.succ n := (nat.succ_ne_zero n).symm

-- Verison without polynomial manipulation
attribute [finsupp_simp] nat.one_ne_zero finsupp.single_eq_of_ne finsupp.single_eq_same add_zero if_true if_false  pi.add_apply pi.zero_apply
  eq_self_iff_true not_true eq_zero_of_zero_eq if_false ne.def nat.sub_zero zero_add not_false_iff bit0_eq_zero
  and_self finsupp.coe_tsub and_false finsupp.coe_add false_and pi.sub_apply finsupp.coe_zero
    nat.succ_ne_zero zero_ne_succ nat.succ_inj' -- To simplify nat equalities
  and_true true_and

end
