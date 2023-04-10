
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

end