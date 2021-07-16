
import data.finsupp.basic
import data.finsupp.lattice
import data.finset.basic
import data.finsupp.antidiagonal
-- import ..vars

section

open finsupp

parameter {S : Type}
parameter [decidable_eq S]

-- TODO rephrase lemma with nat_antidiagonal

/-- A general lemma about the anitdiagonal of a finsupp.single. -/
lemma single_antidiagonal (s : S) (n : ℕ) : 
  (single s n).antidiagonal 
  = (finset.range (n+1)).image (λ i, (finsupp.single s (n-i), finsupp.single s (i))) 
:=
begin
  rw finset.ext_iff,
  intro a,
  rw finsupp.mem_antidiagonal,
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
   simp at h3,
  --  rw nat.sub_zero,
  --  rw add_eq_zero_iff at h3,
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
    -- rw add_eq_zero_iff at h3,
    simp at h3,

    rw h3.right,
    finish,
    finish,
  intro h,
  cases h,
  cases h_h,
  let h1 := prod.ext_iff.1 h_h_h,
  rw [←h1.left, ←h1.right],
  simp,  
  rw [←finsupp.single_nat_sub, ←finsupp.single_add],
  rw finset.mem_range at h_h_w,
  have h4 : n - h_w + h_w = n,
    rw nat.lt_succ_iff at h_h_w,
    exact nat.sub_add_cancel h_h_w,
  rw h4,
end



lemma finsupp.sub_le_right_of_le_add (a b c : S →₀ ℕ) (h : a ≤ b + c) : a - c ≤ b := 
begin
  intro,
  have z := h s,
  rw nat_sub_apply,
  rw add_apply at z,
  -- rw z,
  exact nat.sub_le_right_of_le_add z,
end

-- TODO generalize and add to mathlib
lemma nat.add_inf (a b c : ℕ) : a + (b ⊓ c) = (a + b) ⊓ (a + c) := 
begin
  by_cases b ≤ c,
  simp [inf_eq_left.2 h],
  exact h,
  have h' : c ≤ b,
    exact le_of_not_ge h,
  simp [inf_eq_right.2 h'],
  exact h',
end

lemma finsupp.nat_add_inf (a b c : S →₀ ℕ) : a + (b ⊓ c) = (a + b) ⊓ (a + c) := 
begin
  ext,
  simp only [add_apply, finsupp.inf_apply],
  apply nat.add_inf,
end

-- -- TODO generalize and add to mathlib
-- lemma nat.add_lemma (a b c : ℕ) (h : b ≤ a) : a - b + c = a + c - b := 
-- begin
--   exact nat.sub_add_eq_add_sub h,
-- end

-- TODO generalize and add to mathlib
lemma nat.add_lemma2 (a b c : ℕ) : c = a + b -> c - a = b := 
begin
  exact nat.sub_eq_of_eq_add
end

lemma helper (a b c d : ℕ) (h : b + d = a + c) : a - b ⊓ a + (c - (b - b ⊓ a)) = d :=
begin
  by_cases h1 : b ≤ a,
  simp [inf_eq_left.2 h1],
  rw nat.sub_add_eq_add_sub,
  rw <-h,
  exact norm_num.sub_nat_pos (b + d) b d rfl,
  exact h1,
  have h' : a ≤ b,
    exact le_of_not_ge h1,
  simp [inf_eq_right.2 h'],
  apply nat.sub_eq_of_eq_add,
  rw nat.sub_add_eq_add_sub,
  rw h,
  simp only [nat.add_sub_cancel_left],
  exact h'
end

-- TODO: Put in mathlib
lemma add_antidiagonal (f g : S →₀ ℕ) : (f + g).antidiagonal = (finset.product (f.antidiagonal) (g.antidiagonal)).image (λ x, ((x.fst.fst + x.snd.fst), (x.fst.snd + x.snd.snd))) :=
begin
  rw finset.ext_iff,
  intro a,
  rw mem_antidiagonal,
  rw finset.mem_image,
  split,
  { 
    intro h,
    use ((a.fst ⊓ f, f - (a.fst ⊓ f)), (a.fst - (a.fst ⊓ f), g - (a.fst - (a.fst ⊓ f)))),
    split,
    -- TODO abstract lemma about a+b, a+c, b+d, c+d
    rw finset.mem_product,
    split,
    simp only [mem_antidiagonal],
    apply finsupp.nat_add_sub_of_le,
    exact inf_le_right,
    simp only [mem_antidiagonal],
    apply finsupp.nat_add_sub_of_le,
    apply finsupp.sub_le_right_of_le_add,
    rw finsupp.nat_add_inf,
    simp,
    rw add_comm,
    rw ←h,
    simp,
    -- simp only,
    have tmp : a = (a.fst, a.snd),
    simp,
    rw tmp,
    simp only,
    apply congr_arg2,
    apply finsupp.nat_add_sub_of_le,
    exact inf_le_left,

    -- TODO probably the best way to finish is
    ext,
    simp only [add_apply, nat_sub_apply, finsupp.inf_apply],
    apply helper,
    have h1 := finsupp.ext_iff.1 h,
    exact h1 a_1,

    -- then by_cases on the ⊓ which is greater.
  },
  { intro h,
    cases h with a1 h2,
    cases h2 with H h3,
    rw finset.mem_product at H,
    rw finsupp.mem_antidiagonal at H,
    rw finsupp.mem_antidiagonal at H,
    rw [←H.left, ←H.right],
    rw prod.ext_iff at h3,
    rw [←h3.left, ←h3.right],
    finish,
    }
  -- hint,
  -- ext,
  -- simp only,
  -- use 
end


/-- A copy of the square_antidiagonal lemma, which relies on the more general single_antidiagonal rather than being self contained. -/
lemma single_2_antidiagonal (s : S) : (finsupp.single s 2).antidiagonal = 
{
  (finsupp.single s 0, finsupp.single s 2), 
  (finsupp.single s 1, finsupp.single s 1), 
  (finsupp.single s 2, finsupp.single s 0), 
}
:=
begin
  rw single_antidiagonal,
  rw finset.range,
  rw finset.image,
  simp [-finsupp.single_nat_sub],
end

lemma single_1_antidiagonal (s : S) : (finsupp.single s 1).antidiagonal = 
{
  (finsupp.single s 0, finsupp.single s 1), 
  (finsupp.single s 1, finsupp.single s 0), 
}
:=
begin
  rw single_antidiagonal,
  rw finset.range,
  rw finset.image,
  simp [-finsupp.single_nat_sub],
end

end