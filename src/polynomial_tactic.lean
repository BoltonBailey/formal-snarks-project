
import data.mv_polynomial.basic
import .general_lemmas.mv_X_mul
-- import tactic.basic

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

lemma zero_ne_two : ¬(0 = 2) := 
  by exact dec_trivial

lemma one_ne_two : ¬(1 = 2) := 
  by exact dec_trivial
-- TODO be more clean than just naming these random lemmas 

/--
A tactic to simplify expressions including a coeff of a polynomial
-/
meta def coeff_simplify : tactic unit :=
do
  `[simp [polynomial.eval₂, 
          finsupp.sum, finsupp.smul_sum, 
          mv_polynomial.coeff_sum, mv_polynomial.smul_eq_C_mul, mv_polynomial.X_pow_eq_single, mv_polynomial.coeff_monomial, mv_polynomial.coeff_mul_X', mv_polynomial.coeff_X', coeff_X_mul']]

meta def ite_finsupp_simplify : tactic unit :=
do
  `[simp [←finsupp.single_add, ←finsupp.single_sub]] <|> tactic.trace "no add/sub manipulation",
  `[simp [finsupp.single_eq_single_iff]] <|> tactic.trace "no single_eq_single",
  `[simp [finsupp.eq_single_iff, two_ne_zero, zero_ne_two, one_ne_two]] <|> tactic.trace "no eq_single"
  --  <|> tactic.trace "Goal is not a coeff"


-- do tactic.simp [mv_polynomial.smul_eq_C_mul, mv_polynomial.X_pow_eq_single, mv_polynomial.coeff_monomial, finsupp.single_eq_single_iff, foo]
