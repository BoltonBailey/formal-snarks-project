
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
-- TODO create mathlib PR

end semiring
end polynomial
