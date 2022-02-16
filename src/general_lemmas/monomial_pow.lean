import data.mv_polynomial.basic
import data.polynomial.div
import data.polynomial.field_division

section

universes u

variables {R : Type u}
variables {σ : Type*}

variables [comm_semiring R]

open mv_polynomial

/-- Converting a single variable polynomial to a multivariable polynomial and back yields the same polynomial -/
lemma mv_polynomial.monomial_pow {s : σ →₀ ℕ} {a : R} {n : ℕ} :
  monomial s a ^ n = monomial (n • s) (a ^ n) :=
begin
  induction n,
  simp,
  rw monomial_eq,
  simp,
  -- rw nat.succ_eq_add_one,
  simp [pow_succ, succ_nsmul],
  rw n_ih,
  rw monomial_mul,
  -- library_search,
  
end


-- TODO this function is general purpose enough that it might be submitted to mathlib


end