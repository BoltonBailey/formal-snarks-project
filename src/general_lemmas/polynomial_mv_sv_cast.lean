import data.mv_polynomial.basic
import data.polynomial.div
import data.polynomial.field_division

section

universes u


parameter {R : Type u}
parameter [comm_semiring R]

/-- Converting a single variable polynomial to a multivariable polynomial and back yields the same polynomial -/
lemma multivariable_to_single_variable (S : Type) (s : S) (f : S → polynomial R) (hf : f s = polynomial.X) (t : polynomial R) : ((t.eval₂ mv_polynomial.C (mv_polynomial.X s)).eval₂ polynomial.C f) = t 
:=
begin
  -- ext,
  rw polynomial.eval₂,
  -- rw polynomial.coeff_sum,
  rw polynomial.sum,
  simp,
  conv
  begin
    to_lhs,
    congr,
    skip,
    funext,
    rw hf,
    rw polynomial.X_pow_eq_monomial,
    rw ←polynomial.monomial_zero_left,
    rw polynomial.monomial_mul_monomial,
    simp,  
  end,
  -- rw ←polynomial.coeff,
  rw t.as_sum_support.symm,
end


-- TODO this function is general purpose enough that it might be submitted to mathlib


end