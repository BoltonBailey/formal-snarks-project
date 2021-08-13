

-- TODO a tactic for resolving statements in integral domain rings

-- This tactic should work as follows:
-- 1. Find all equality statements in the Euclidean ring in the statements (and goal)
-- 2. Break down either side of these equalities into a tree of add and mul operations (do not break down sums or prods)
-- 3. Identify all atoms of R from these, and put these equations in ring normal form
-- 4. Mutually simplify the equations by gaussian elimination. That is - check if subtracting off any statement equation from any other, or any statement from the goal,  "simplifies it" in terms of leaving less added terms. If so, perform this subtraction and resimplify. Repeat until we get through all pairs without a simplification.
-- 5. Check if any atom can be factored out of an equation, with zero on the other side. If so, simplify this to the disjunction of this atom being zero or the other factor being zero. Split on this disjunction, and repeat from step 4 on both sides of the split.

-- This is related to the Nullstellensatz. Specifically [Buchberger's Algorithm](https://en.wikipedia.org/wiki/Buchberger%27s_algorithm) is one way of doing what I do here. Not sure yet what the relation is - probably Buchberger is more general, but more time complex? See also the coq tactic [nsatz](https://coq.inria.fr/refman/addendum/nsatz.html).

-- What is the ["effective nullstellensatz"](https://en.wikipedia.org/wiki/Hilbert%27s_Nullstellensatz#Effective_Nullstellensatz) of these problems