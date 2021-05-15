
import data.finsupp.basic
import data.finset.basic
-- import ..vars

section

parameter {S : Type}
parameter [decidable_eq S]

/-- A general lemma about the anitdiagonal of a finsupp.single. -/
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
  rw finsupp.ext_iff,
  intro a_1,
  rw finsupp.nat_sub_apply,
  rw finsupp.single_apply,
  rw finsupp.single_apply,
  by_cases h2 : a_1 = s,
   rw h2,
   simp,
   have h3 : (a.fst + a.snd) s = (finsupp.single s n) s,
   rw h,
   rw finsupp.add_apply at h3,
   rw finsupp.single_apply at h3,
   simp at h3,
   rw ←h3,
   simp,
   rw if_neg,
   rw if_neg,
   have h3 : (a.fst + a.snd) a_1 = (finsupp.single s n) a_1,
   rw h,
   rw finsupp.add_apply at h3,
   rw finsupp.single_apply at h3,
   simp at h3,
   rw if_neg at h3,
   rw add_eq_zero_iff at h3,
   rw h3.left,
   finish,
   finish,
   finish,
  rw finsupp.ext_iff,
  intro a_1,
  rw finsupp.single_apply,
  by_cases h2 : a_1 = s,
    rw h2,
    simp,
    rw if_neg,
    have h3 : (a.fst + a.snd) a_1 = (finsupp.single s n) a_1,
    rw h,
    rw finsupp.add_apply at h3,
    rw finsupp.single_apply at h3,
    simp at h3,
    rw if_neg at h3,
    rw add_eq_zero_iff at h3,
    rw h3.right,
    finish,
    finish,
  intro h,
  cases h,
  cases h_h,
  let h1 := prod.ext_iff.1 h_h_h,
  rw [←h1.left, ←h1.right],
  simp,
  rw [←finsupp.single_sub, ←finsupp.single_add],
  rw finset.mem_range at h_h_w,
  have h4 : n - h_w + h_w = n,
    rw nat.lt_succ_iff at h_h_w,
    exact nat.sub_add_cancel h_h_w,
  rw h4,
end

-- TODO make a lemma about how the antidiagonal of a sum of disjoint support finsupps is given by taking the product over the individual antidiagonals and summing.

/-- A copy of the square_antidiagonal lemma, which relies on the more general single_antidiagonal_support rather than being self contained. -/
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
end