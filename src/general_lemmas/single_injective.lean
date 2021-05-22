import data.finsupp.basic

-- THis was working fine until I updated mathlib and it broke, someone must hvae changes injective from an iff to a implication

open finsupp


variables {α M : Type*}

variables [has_zero M] (a a' : α) (b b' : M)

lemma single_injective_iff : single a b = single a b' ↔ b = b' :=
begin
  split,
  intro h,
  have h1 := (ext_iff.1 h) a ,
  simp at h1,
  exact h1,
  intro h,
  rw h,
end