
import algebra.big_operators.ring

open_locale big_operators

section

universe variables u v

parameter {F : Type u}
parameter [field F]

-- Probably not appropriate for mathlib
lemma mul_sum_symm {α : Type u} {β : Type v} {s : finset α} {b : β} {f : α → β} 
  [non_unital_non_assoc_semiring β] : 
  ∑ (x : α) in s, b * f x = b * ∑ (x : α) in s, f x := finset.mul_sum.symm

example (n : ℕ) (a : F) (b : fin n -> F) : 
(∑ (i : fin n) in finset.fin_range n, a * b i) = a * (∑ (i : fin n) in finset.fin_range n, b i) :=
begin
  -- rw <-finset.mul_sum, -- works fine
  rw mul_sum_symm, -- this fails without "universe variables" above
end

end