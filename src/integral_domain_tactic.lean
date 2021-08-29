

-- TODO a tactic for resolving statements in integral domain rings

-- This tactic should work as follows:
-- 1. Find all equality statements in the Euclidean ring in the statements (and goal)
-- 2. Break down either side of these equalities into a tree of add and mul operations (do not break down sums or prods)
-- 3. Identify all atoms of R from these, and put these equations in ring normal form
-- 4. Mutually simplify the equations by gaussian elimination. That is - check if subtracting off any statement equation from any other, or any statement from the goal,  "simplifies it" in terms of leaving less added terms. If so, perform this subtraction and resimplify. Repeat until we get through all pairs without a simplification.
-- 5. Check if any atom can be factored out of an equation, with zero on the other side. If so, simplify this to the disjunction of this atom being zero or the other factor being zero. Split on this disjunction, and repeat from step 4 on both sides of the split.

-- This is related to the Nullstellensatz. Specifically [Buchberger's Algorithm](https://en.wikipedia.org/wiki/Buchberger%27s_algorithm) is one way of doing what I do here. Not sure yet what the relation is - probably Buchberger is more general, but more time complex? See also the coq tactic [nsatz](https://coq.inria.fr/refman/addendum/nsatz.html).

-- What is the ["effective nullstellensatz"](https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz#Effective_Nullstellensatz) of these problems



import data.mv_polynomial.basic
import .general_lemmas.mv_X_mul
import .general_lemmas.single_antidiagonal
import tactic.abel

open tactic

section

universes u


/-- The finite field parameter of our SNARK -/
parameters {R vars : Type u}
parameter [ring R]

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

meta def mytrace_goal_tactic : tactic unit :=
do
  goal ← tactic.target,
  tactic.trace goal

/-- A tactic for solving systems of equationd in an integral domain -/
meta def integral_domain_tactic : tactic unit :=
do
  goal ← tactic.target,
  goal_type ← infer_type goal,
  -- TODO Check goal is equality expression
  -- goal_lhs
  tactic.trace (goal),
  tactic.trace (goal_type)

/-- A tactic for solving systems of equationd in an integral domain -/
meta def integral_domain_tactic' : tactic unit :=
do
  -- Call simp * at *, (perhaps TODO restrict the lemmas used, does simp * with my_tag at * work?)
  -- Is there a disjunction in the current context?
    -- If so, 
      -- Find a disjunction and split it using cases_type or
      -- Recursively call integral domain tactic twice
    -- If not,
    
  -- locate

example (a b c d e f : R) (h1 : a + b = c + d) (h2 : c + d = e + f) : a + b = e + f :=
begin
  integral_domain_tactic,
end

example (a b c d e f : R) (h1 : a * b = 1) (h2 : a * c = 0) (h3 : b * d = 0) : c * e + f * d = 0 :=
begin
  -- Since a b nonzero, c, d zero and this holds.
  integral_domain_tactic,
end

example (a b c d e f : R) (h1 : 0 = a + 0) (h2 : a + b = 0) : b = c :=
begin
  simp only [*, add_zero, zero_add] at *,
end


end