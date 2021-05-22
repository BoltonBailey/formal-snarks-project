
import data.mv_polynomial.basic
import .general_lemmas.mv_X_mul
-- import tactic.basic

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

run_cmd mk_simp_attr `coeff_simp
run_cmd tactic.add_doc_string `simp_attr.coeff_simp "Attribute for lemmas that are used in the simplification of coeff statements"

@[user_attribute] meta def finsupp_simp_attribute : user_attribute :=
{ name := `finsupp_simp,
  descr := "Attribute for lemmas that are used in the simplification of TODO" }


@[finsupp_simp]
lemma zero_ne_two : ¬(0 = 2) := 
  by exact dec_trivial

lemma one_ne_two : ¬(1 = 2) := 
  by exact dec_trivial
-- TODO be more clean than just naming these random lemmas 



attribute [coeff_simp] polynomial.eval₂
attribute [coeff_simp] polynomial.sum
attribute [coeff_simp] finsupp.sum
attribute [coeff_simp] finsupp.smul_sum
attribute [coeff_simp] mv_polynomial.smul_eq_C_mul
attribute [coeff_simp] mv_polynomial.X_pow_eq_single
attribute [coeff_simp] mv_polynomial.coeff_sum
attribute [coeff_simp] mv_polynomial.coeff_add
-- attribute [coeff_simp] mv_polynomial.coeff_mul
attribute [coeff_simp] mv_polynomial.coeff_C_mul
attribute [coeff_simp] mv_polynomial.coeff_monomial
attribute [coeff_simp] mv_polynomial.coeff_mul_X'
attribute [coeff_simp] mv_polynomial.coeff_X'
attribute [coeff_simp] coeff_X_mul'
attribute [coeff_simp] mv_polynomial.coeff_C


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
