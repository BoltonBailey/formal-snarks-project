
import data.mv_polynomial.basic


open mv_polynomial
section

universes u

variables {R : Type u}
variables {σ : Type*} 

variables [decidable_eq σ]
variables [comm_semiring R]

lemma coeff_X_mul' (m) (s : σ) (p : mv_polynomial σ R) :
  coeff m (X s * p) = if s ∈ m.support then coeff (m - finsupp.single s 1) p else 0 := 
begin
  rw mul_comm,
  rw mv_polynomial.coeff_mul_X',
  finish,
end

end