
import data.polynomial.basic
import data.polynomial.monomial
import algebra.polynomial.group_ring_action

namespace polynomial
universes u
variables {R : Type u} {a : R} {m n : ℕ}

section semiring
variables [semiring R] {p q : polynomial R}

/-- A scalar multiplication is equivalent to constant polynomial multiplication for polynomials -/
lemma smul_eq_C_mul (a : R) : a • p = (polynomial.C a) * p :=
begin
  rw polynomial.ext_iff,
  intro n,
  rw polynomial.coeff_C_mul,
  rw polynomial.coeff_smul,
end
-- TODO create mathlib PR

lemma C_mul_eq_smul (a : R) : (polynomial.C a) * p = a • p :=
begin
  rw polynomial.ext_iff,
  intro n,
  rw polynomial.coeff_C_mul,
  rw polynomial.coeff_smul,
end

end