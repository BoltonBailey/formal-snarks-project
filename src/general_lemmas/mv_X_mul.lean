

import data.mv_polynomial.basic

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v
variables {R : Type u} 


namespace mv_polynomial
variables {σ : Type*} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section comm_semiring

variables [comm_semiring R] {p q : mv_polynomial σ R}

section decidable_eq 

variables [decidable_eq σ]


lemma coeff_X_mul' (m) (s : σ) (p : mv_polynomial σ R) :
  coeff m (X s * p) = if s ∈ m.support then coeff (m - finsupp.single s 1) p else 0 := 
begin
  rw mul_comm,
  rw mv_polynomial.coeff_mul_X',
end

end decidable_eq

lemma coeff_mul_X_pow (m) (n : ℕ) (s : σ) (p : mv_polynomial σ R) :
  coeff (m + single s n) (p * X s ^ n) = coeff m p :=
begin
  have : (m, single s n) ∈ (m + single s n).antidiagonal := mem_antidiagonal.2 rfl,
  rw [coeff_mul, ← finset.insert_erase this, finset.sum_insert (finset.not_mem_erase _ _),
      finset.sum_eq_zero, add_zero, coeff_X_pow, if_pos, mul_one],
      simp only [eq_self_iff_true],
  rintros ⟨i,j⟩ hij,
  rw [finset.mem_erase, mem_antidiagonal] at hij,
  by_cases H : single s n = j,
  { subst j, simpa using hij },
  { rw [coeff_X_pow, if_neg H, mul_zero] },
end

lemma support_X_pow [nontrivial R] : (X n ^ e : mv_polynomial σ R).support = {single n e} :=
by rw [X_pow_eq_single, support_monomial, if_neg]; exact one_ne_zero

lemma coeff_mul_X_pow' (m) (n : ℕ) (s : σ) (p : mv_polynomial σ R) :
  coeff m (p * X s ^ n ) = if n ≤ m s then coeff (m - finsupp.single s n) p else 0 := 
begin
  nontriviality R,
  split_ifs with h h,
  { conv_rhs {rw ← coeff_mul_X_pow _ n s},
    congr' with  t,
    by_cases hj : s = t,
    { subst t, simp only [nat_sub_apply, add_apply, single_eq_same], exact (nat.sub_eq_iff_eq_add h).mp rfl,
      },
    { simp [single_eq_of_ne hj] } },
  { rw ← not_mem_support_iff, intro hm, apply h,
    have H := support_mul _ _ hm, simp only [finset.mem_bUnion] at H,
    rcases H with ⟨j, hj, i', hi', H⟩,
    rw [support_X_pow, finset.mem_singleton] at hi', subst i',
    rw finset.mem_singleton at H, subst m,
    rw [add_apply, single_apply, if_pos rfl],
    finish, }
end

lemma coeff_X_pow_mul' (m) (n : ℕ) (s : σ) (p : mv_polynomial σ R) :
  coeff m (X s ^ n * p) = if n ≤ m s then coeff (m - finsupp.single s n) p else 0 := 
begin
  rw mul_comm,
  rw coeff_mul_X_pow',
end



lemma sum_X_mul {α : Type u} (r : finset α) (f : α -> mv_polynomial σ R) (s : σ) : 
  (∑ x in r, X s * f x) = X s * (∑ x in r, f x)
:= 
begin
  rw finset.mul_sum,
end

lemma sum_C_mul {α : Type u} {r : finset α} {f : α -> mv_polynomial σ R} (e : R) : 
  (∑ x in r, C e * f x) = C e * (∑ x in r, f x)
:= 
begin
  rw finset.mul_sum,
end

lemma C_mul_C (a a' : R) : C a * C a' = (C (a * a') : mv_polynomial σ R)  := 
begin
  simp,
end

-- FOr some reason, this lemma is actually useless https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Extracting.20constant.20from.20sum
-- I expect many other lemmas in theis file may be useless as well
-- TODO investigate and clean up
lemma finset_sum_C {α : Type u} {r : finset α} {f : α -> R} (e : R) : 
  (∑ x in r, (C (f x) : mv_polynomial σ R)) = C (∑ x in r, f x)
:= 
begin
  rw finset.sum_hom,
end

-- lemma rearrange1 (n : ℕ) (v1 v2 : σ) (p : mv_polynomial σ R) : (mv_polynomial.X v1 ^ n) * (mv_polynomial.X v2 * p) = mv_polynomial.X v2 * ((mv_polynomial.X v1 ^ n) * p) :=
-- begin
--   ring,
-- end

-- lemma rearrange2 (n : ℕ) (f : R) (v1 : σ) (p : mv_polynomial σ R) : (mv_polynomial.X v1 ^ n) * (mv_polynomial.C f * p) = mv_polynomial.C f * ((mv_polynomial.X v1 ^ n) * p) :=
-- begin
--   ring,
-- end

-- move constants right of X
lemma rearrange_constants_right (f : R) (v1 : σ) : 
 mv_polynomial.C f * mv_polynomial.X v1 = (mv_polynomial.X v1) * (mv_polynomial.C f)
:=
begin
  ring,
end


lemma rearrange_constants_right_with_extra (f : R) (v1 : σ) (p : mv_polynomial σ R) : 
 mv_polynomial.C f * (mv_polynomial.X v1 * p) = (mv_polynomial.X v1) * (mv_polynomial.C f * p)
:=
begin
  ring,
end


lemma rearrange_constants_right_hard (f : R) (p : polynomial R) : 
  polynomial.C f * p = (p) * (polynomial.C f)
:=
begin
  ring,
end

lemma rearrange_sums_right_with_extra {α : Type u} {r : finset α} {f : α -> mv_polynomial σ R} (s : σ) (p : mv_polynomial σ R) : 
  (∑ x in r, f x) * (X s * p) = X s * (∑ x in r, f x) * p
:=
begin
  ring,
end

lemma rearrange_sums_right {α : Type u} {r : finset α} {f : α -> mv_polynomial σ R} (s : σ) : 
  (∑ x in r, f x) * X s = X s * (∑ x in r, f x)
:=
begin
  ring,
end


-- move constants right of X
lemma rearrange_smul_right (n : ℕ) (a : R) (v1 : σ) (p : mv_polynomial σ R) : 
 a • (mv_polynomial.X v1 * p) = (mv_polynomial.X v1) * (a • p)
:=
begin
  rw mul_smul_comm,
end

end comm_semiring

end mv_polynomial