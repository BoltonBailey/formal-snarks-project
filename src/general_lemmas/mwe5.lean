import data.mv_polynomial.basic

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u
variables {R : Type u} 


namespace mv_polynomial
variables {σ : Type*} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section comm_semiring

variables [comm_semiring R] {p q : mv_polynomial σ R}


-- variables [decidable_eq σ]


lemma coeff_X_mul' (m) (s : σ) (p : mv_polynomial σ R) :
  coeff m (X s * p) = if s ∈ m.support then coeff (m - finsupp.single s 1) p else 0 := 
begin
  rw mul_comm,
  rw mv_polynomial.coeff_mul_X',
  -- finish,
end

end comm_semiring

