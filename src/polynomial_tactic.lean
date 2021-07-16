
import data.mv_polynomial.basic
import .general_lemmas.mv_X_mul
import .general_lemmas.single_antidiagonal

section

open mv_polynomial

universes u


/-- The finite field parameter of our SNARK -/
parameters {F vars : Type u}
parameter [field F]

-- TODO remove these practice tactics
meta def my_first_tactic : tactic unit := 
do
  tactic.trace "Hello,",
  tactic.trace "World."


meta def my_fail_tactic : tactic unit := 
tactic.fail "This tactic failed, we apologize for the inconvenience."

run_cmd add_interactive [`my_first_tactic, `my_fail_tactic]


meta def my_orelse_tactic : tactic unit :=
my_fail_tactic <|> my_first_tactic

meta def my_tactic : tactic unit :=
do
  goal ← tactic.target,
  tactic.trace goal

example : true :=
begin
  my_tactic,
  trivial
end

-- @[user_attribute] meta def my_attribute : user_attribute :=
-- { name := `coeff_simp,
--   descr := "Attribute for lemmas that are used in the simplification of coeff statements" }


run_cmd mk_simp_attr `polynomial_nf
run_cmd tactic.add_doc_string `simp_attr.polynomial_nf "Attribute for lemmas that are used in the conversion of mv_polynomial expressions to a normal form consisting of adds of sums of muls of mv_polynomials"

attribute [polynomial_nf] polynomial.eval₂
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

-- attribute [polynomial_nf_2] polynomial.eval₂
-- attribute [polynomial_nf_2] polynomial.sum
-- attribute [polynomial_nf_2] finsupp.sum
attribute [polynomial_nf_2] mul_add
attribute [polynomial_nf_2] add_mul
-- attribute [polynomial_nf_2] finset.sum_mul
-- attribute [polynomial_nf_2] finset.mul_sum
attribute [polynomial_nf_2] finset.sum_add_distrib

attribute [polynomial_nf_2] sum_X_mul
attribute [polynomial_nf_2] sum_C_mul
attribute [polynomial_nf_2] rearrange_constants_right
attribute [polynomial_nf_2] rearrange_constants_right_with_extra
attribute [polynomial_nf_2] rearrange_sums_right
attribute [polynomial_nf_2] rearrange_sums_right_with_extra
attribute [polynomial_nf_2] C_mul_C
attribute [polynomial_nf_2] finset.sum_hom
attribute [polynomial_nf_2] mv_polynomial.smul_eq_C_mul




attribute [polynomial_nf_2] mul_assoc

attribute [polynomial_nf_2] finsupp.smul_sum
attribute [polynomial_nf_2] mul_smul_comm
attribute [polynomial_nf_2] smul_add
attribute [polynomial_nf_2] mul_smul
attribute [polynomial_nf_2] smul_mul_assoc

run_cmd mk_simp_attr `rearrange
run_cmd tactic.add_doc_string `simp_attr.rearrange "TODO a few rearrangement lemmas"

-- attribute [rearrange] rearrange1
-- attribute [rearrange] rearrange2
-- attribute [rearrange] rearrange_constants_right
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



lemma zero_ne_two : ¬(0 = 2) := 
  by exact dec_trivial

lemma one_ne_two : ¬(1 = 2) := 
  by exact dec_trivial
-- TODO be more clean than just naming these random lemmas 


meta def ite_finsupp_simplify : tactic unit :=
do
  `[simp [←finsupp.single_add, ←finsupp.single_sub]] <|> tactic.skip,
  `[simp [finsupp.single_eq_single_iff]] <|> tactic.skip,
  `[simp [finsupp.eq_single_iff]] <|> tactic.skip, 
  `[simp [two_ne_zero, zero_ne_two, one_ne_two]] <|> tactic.skip


meta def ite_finsupp_simplify2 : tactic unit :=
do
  `[simp [finsupp.ext_iff']] <|> tactic.skip,
  `[simp [finsupp.eq_single_iff]] <|> tactic.skip, 
  `[simp [two_ne_zero, zero_ne_two, one_ne_two]] <|> tactic.skip

  -- `[finish] <|> tactic.trace "no finish needed"
  --  <|> tactic.trace "Goal is not a coeff"

-- meta def single_add_simplify : tactic unit :=
-- do
--   `[simp [←finsupp.single_add, ←finsupp.single_sub]]

-- meta def single_simplify : tactic unit :=
-- do
--   `[simp [finsupp.single_eq_single_iff]] <|> tactic.trace "no single_eq_single",
--   `[simp [finsupp.eq_single_iff, two_ne_zero, zero_ne_two, one_ne_two]] <|> tactic.trace "no eq_single"

-- do tactic.simp [mv_polynomial.smul_eq_C_mul, mv_polynomial.X_pow_eq_single, mv_polynomial.coeff_monomial, finsupp.single_eq_single_iff, foo]

end