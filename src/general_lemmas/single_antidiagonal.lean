
import data.finsupp.basic
-- import data.finsupp.lattice
import data.finset.basic
import data.finsupp.antidiagonal
import data.finset.nat_antidiagonal
import tactic.linarith
import algebra.order.sub.basic
-- import ..vars

section

open finsupp

parameter {S : Type}
parameter [decidable_eq S]

-- TODO rephrase lemma with nat_antidiagonal
lemma single_antidiagonal (s : S) (n : ℕ) : 
  (single s n).antidiagonal 
  = (finset.nat.antidiagonal n).image (λ antis, (finsupp.single s antis.1, finsupp.single s antis.2)) 
:=
begin
  rw finset.ext_iff,
  intro a,
  rw finsupp.mem_antidiagonal,
  rw finset.mem_image,
  split,
  {
    intro h,
    use ⟨a.fst s, a.snd s⟩,
    simp,
    have := congr_fun h s,
    simp at this,
    rw this,
    simp,
    ext;
    { have foo := congr_fun h a_1,
      simp [finsupp.single_apply] at *,
      split_ifs at *,
      rw h_1,
      simp at foo,
      tauto, },
  },
  {
    rintros ⟨a_1, H, foo⟩,
    rw finset.nat.mem_antidiagonal at H,

    rw foo.symm at *,
    simp,
    rw ←H,
    simp,
  },
end

/-- A general lemma about the anitdiagonal of a finsupp.single. -/
lemma single_antidiagonal' (s : S) (n : ℕ) : 
  (single s n).antidiagonal 
  = (finset.range (n+1)).image (λ i, (finsupp.single s (n-i), finsupp.single s (i))) 
:=
begin
  rw single_antidiagonal,
  ext singles,
  unfold finset.nat.antidiagonal,
  simp,
  split,
  {
    rintros ⟨a, b, h1, h2⟩,
    use b,
    split,
    {
      linarith,
    },
    rw <-h2,
    simp,
    ext,
    simp [finsupp.single_apply],
    split_ifs,
    tidy,
  },
  {
    rintros ⟨a, h1, h2⟩,
    use (n-a), use a,
    split,
    tidy,
    rw nat.lt_succ_iff at h1,
    exact nat.sub_add_cancel h1,
  },
end



lemma finsupp.sub_le_right_of_le_add (a b c : S →₀ ℕ) (h : a ≤ b + c) : a - c ≤ b := 
begin
  intro s,
  have z := h s,
  rw tsub_apply,
  -- rw add_apply at z,
  rw tsub_le_iff_right,
  rw ←add_apply,
  exact z,
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

lemma helper (a b c d : ℕ) (h : b + d = a + c) : a - b ⊓ a + (c - (b - b ⊓ a)) = d :=
begin
  by_cases h1 : b ≤ a,
  simp [inf_eq_left.2 h1],
  rw tsub_add_eq_add_tsub,
  rw <-h,
  exact norm_num.sub_nat_pos (b + d) b d rfl,
  exact h1,
  have h' := le_of_not_ge h1,
  simp [inf_eq_right.2 h'],
  apply tsub_eq_of_eq_add,
  have h'' := nat.add_sub_of_le h',
  linarith,
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
    apply add_tsub_cancel_of_le,
    exact inf_le_right,
    simp only [mem_antidiagonal],
    apply add_tsub_cancel_of_le,
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
    apply add_tsub_cancel_of_le,
    exact inf_le_left,

    -- TODO probably the best way to finish is
    ext,
    simp only [add_apply, tsub_apply, finsupp.inf_apply],
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
  rw single_antidiagonal',
  rw finset.range,
  rw finset.image,
  simp [-finsupp.single_tsub, ←finsupp.single_tsub],
end

lemma single_1_antidiagonal (s : S) : (finsupp.single s 1).antidiagonal = 
{
  (finsupp.single s 0, finsupp.single s 1), 
  (finsupp.single s 1, finsupp.single s 0), 
}
:=
begin
  rw single_antidiagonal',
  rw finset.range,
  rw finset.image,
  simp [-finsupp.single_tsub, ←finsupp.single_tsub],
end

end