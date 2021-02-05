
import data.finsupp.basic
import data.finset.basic
-- import ..vars

section

parameter {S : Type}
parameter [decidable_eq S]

/-- A general lemma about the anitdiagonal of a finsupp.single. Currently incomplete TODO-/
lemma single_antidiagonal_support (s : S) (n : ℕ) : 
  (finsupp.single s n).antidiagonal.support 
  = (finset.range (n+1)).image (λ i, (finsupp.single s (n-i), finsupp.single s (i))) 
:=
begin
  rw finset.ext_iff,
  intro a,
  rw finsupp.mem_antidiagonal_support,
  rw finset.mem_image,
  split,
  intro h,
  use a.snd s,
  split,
  rw finsupp.ext_iff at h,
  have h1 := h s,
  simp at h1,
  rw finset.mem_range,
  rw ←h1,
  apply @nat.lt_of_lt_of_le (a.snd s) (a.snd s + 1) _,
  exact lt_add_one ((a.snd) s),
  rw add_assoc,
  exact ((a.snd) s + 1).le_add_left ((a.fst) s),
  rw prod.ext_iff,
  simp,
  split,
  sorry,
  sorry,
  sorry,

  -- linarith,
end

/-- A copy of the square_antidiagonal lemma, which relies on the more general single_antidiagonal_support rather than being self contained. This should be less code, but currently single_antidiagonal_support uses sorry -/
lemma single_2_antidiagonal_support (s : S) : (finsupp.single s 2).antidiagonal.support = 
{
  (finsupp.single s 0, finsupp.single s 2), 
  (finsupp.single s 1, finsupp.single s 1), 
  (finsupp.single s 2, finsupp.single s 0), 
}
:=
begin
  rw single_antidiagonal_support s 2,
  rw finset.ext_iff,
  intro a,
  rw finset.range,
  rw finset.image,
  simp [-finsupp.single_sub],
end

/-- The antidiagonal of Z^2 consists of three elements -/
lemma square_antidiagonal (s : S) : (finsupp.single s 2).antidiagonal.support = 
{
  (finsupp.single s 0, finsupp.single s 2), 
  (finsupp.single s 1, finsupp.single s 1), 
  (finsupp.single s 2, finsupp.single s 0), 
}
:=
begin
  rw finset.ext_iff,
  intro a,
  rw finsupp.mem_antidiagonal_support,
  split,
  intro h,
  simp,
  have h1 : ∃ i , a.fst = finsupp.single s i ∧ i ≤ 2 ∧ a.snd = finsupp.single s (2-i),
  use a.fst s,
  split,
  rw finsupp.ext_iff,
  intro a1,
  by_cases h2 : a1 = s,
  rw h2,
  rw finsupp.single_apply,
  rw if_pos,
  simp,
  rw finsupp.single_apply,
  rw if_neg,
  rw finsupp.ext_iff at h,
  let h3 := h a1,
  rw finsupp.single_apply at h3,
  rw if_neg at h3,
  rw finsupp.add_apply at h3,
  rw add_eq_zero_iff at h3,
  exact h3.left,
  intro h4,
  rw h4 at h2,
  exact h2 (refl a1),
  intro h4,
  rw h4 at h2,
  exact h2 (refl a1),
  rw finsupp.ext_iff at h,
  let h5 := h s,
  rw finsupp.single_apply at h5,
  rw if_pos at h5,
  rw finsupp.add_apply at h5,
  split,
  exact nat.le.intro h5,
  rw finsupp.ext_iff,
  intro a1,
  by_cases h2 : a1 = s,
  rw h2,
  rw finsupp.single_apply,
  rw if_pos,
  exact (norm_num.sub_nat_pos 2 ((a.fst) s) ((a.snd) s) h5).symm,
  refl,
  rw finsupp.single_apply,
  rw if_neg,
  let h6 := h a1,
  rw finsupp.single_apply at h6,
  rw if_neg at h6,
  rw finsupp.add_apply at h6,
  rw add_comm at h6,
  exact nat.eq_zero_of_add_eq_zero_right h6,
    intro h4,
  rw h4 at h2,
  exact h2 (refl a1),
    intro h4,
  rw h4 at h2,
  exact h2 (refl a1),
  refl,
  -- h1 done
  cases h1,
  cases h1_h,
  cases h1_h_right,



  -- case 2,
  have h6 := eq_or_lt_of_le h1_h_right_left,
  cases h6,
  right,
  right,
  rw h6 at h1_h_left,
  rw h6 at h1_h_right_right,
  have h7 : a.snd = 0,
  rw h1_h_right_right,
  simp,
  exact prod.ext h1_h_left h7,
  have h6_2 : h1_w ≤ 1,
  exact nat.lt_succ_iff.mp h6,
  clear h6,
  -- case 1
  have h6 := eq_or_lt_of_le h6_2,
  cases h6,
  right,
  left,
  rw h6 at h1_h_left,
  rw h6 at h1_h_right_right,
  have h7 : a.snd = finsupp.single s (1),
  rw h1_h_right_right,
  have h8 : 2-1 = 1,
  simp,
  exact prod.ext h1_h_left h7,
  clear h6_2,
  have h6_2 : h1_w ≤ 0,
  exact nat.lt_succ_iff.mp h6,
  clear h6,
  -- case 0
  have h6 := eq_or_lt_of_le h6_2,
  cases h6,
  left,
  rw h6 at h1_h_left,
  rw h6 at h1_h_right_right,
  have h7 : a.snd = finsupp.single s (2),
  rw h1_h_right_right,
  simp at h1_h_left,
  exact prod.ext h1_h_left h7,
  have f : false,
  exact nat.not_lt_zero h1_w h6,
  exfalso,
  exact f,

  -- Forward case
  simp,
  intro h,
  cases h,
  have h1 : a.fst = 0,
  exact (congr_arg prod.fst h).trans rfl,
  have h2 : a.snd = finsupp.single s 2,
  exact (congr_arg prod.snd h).trans rfl,
  rw [h1, h2],
  simp,
  cases h,
  have h1 : a.fst = finsupp.single s 1,
  exact (congr_arg prod.fst h).trans rfl,
  have h2 : a.snd = finsupp.single s 1,
  exact (congr_arg prod.snd h).trans rfl,
  rw [h1, h2],
  rw ← finsupp.single_add,
  have h1 : a.fst = finsupp.single s 2,
  exact (congr_arg prod.fst h).trans rfl,
  have h2 : a.snd = 0,
  exact (congr_arg prod.snd h).trans rfl,
  rw [h1, h2],
  simp,


end


end