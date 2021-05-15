
import data.polynomial.basic
import data.polynomial.monomial
import data.polynomial.coeff

namespace polynomial
universes u
variables {R : Type u} {a : R} {m n : ℕ}

section semiring
variables [semiring R] {p q : polynomial R}

/-- A scalar multiplication is equivalent to constant polynomial multiplication for polynomials -/
lemma smul_eq_C_mul (a : R) : a • p = (polynomial.C a) * p := by simp [ext_iff]
-- [mathlib PR](https://github.com/leanprover-community/mathlib/pull/7240)
-- TODO this has now been merged, so it should be possible to upgrade the mathlib for this project and remove this file at some point

end semiring
end polynomial
