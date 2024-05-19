
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Monad

section

/-!

This file contains lemmas needed for the transformations file

-/

universe u

variable {F : Type}

variable [Field F]

-- https://github.com/leanprover-community/mathlib4/pull/13023
@[to_additive]
lemma List.prod_map_ite_eq {A B : Type} [DecidableEq A] [CommGroup B] (f g : A → B) (a : A) (l : List A) :
    List.prod (List.map (fun x => ite (x = a) (f x) (g x)) l)
      =
    (f a / g a) ^ (List.count a l) * List.prod (List.map g l)  :=
  by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [map_cons, prod_cons, nodup_cons, ne_eq, mem_cons] at ih ⊢
    rw [ih]
    clear ih
    rw [List.count_cons]
    by_cases hx : x = a
    · simp [hx, ite_true, pow_add]
      -- TODO replace with `abel`
      simp only [mul_assoc, mul_comm (f a / g a) _, mul_comm (f a) _]
      simp only [mul_right_inj]
      simp only [mul_assoc, mul_comm (g a) _]
      simp only [mul_right_inj]
      simp only [div_mul_cancel]
    · simp only [hx, ite_false, ne_comm.mp hx, add_zero]
      simp only [mul_assoc, mul_comm (g x) _]

-- https://github.com/leanprover-community/mathlib4/pull/11106
theorem MvPolynomial.degreeOf_C_mul {σ R : Type} [Field R] (j : σ)
    (c : R) (hc : c ≠ 0) (f : MvPolynomial σ R) :
    MvPolynomial.degreeOf j (MvPolynomial.C c * f) = MvPolynomial.degreeOf j f := by
  rw [Nat.eq_iff_le_and_ge]
  constructor
  · convert MvPolynomial.degreeOf_C_mul_le f j c
  · have := MvPolynomial.degreeOf_C_mul_le (C (c) * f) j (1/c)
    rw [<-mul_assoc] at this
    rw [←C_mul] at this
    simp only [one_div, ne_eq, hc, not_false_eq_true, inv_mul_cancel, map_one, one_mul] at this
    convert this

-- https://github.com/leanprover-community/mathlib4/pull/13024
@[simp]
lemma MvPolynomial.coeff_single_X {R : Type} {σ : Type u_1} [CommSemiring R] [DecidableEq σ]
    (j : σ) (n : ℕ)
    (x : σ) :
    MvPolynomial.coeff (R := R) (Finsupp.single j n) (MvPolynomial.X x) = if n = 1 ∧ j = x then 1 else 0  := by
  simp_rw [MvPolynomial.X, MvPolynomial.coeff_monomial, Finsupp.single_eq_single_iff]
  congr
  simp_rw [eq_iff_iff]
  tauto

-- https://github.com/leanprover-community/mathlib4/pull/13024
@[simp]
lemma MvPolynomial.coeff_single_X_pow {R : Type} {σ : Type u_1} [CommSemiring R] [DecidableEq σ]
    (j : σ) (n k : ℕ)
    (x : σ) :
    MvPolynomial.coeff (R := R) (Finsupp.single j n) (MvPolynomial.X x ^ k) = if n = k ∧ j = x ∨ k = 0 ∧ n = 0 then 1 else 0  := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  congr
  simp only [Finsupp.single_eq_single_iff, eq_iff_iff]
  tauto

lemma MvPolynomial.prod_neq_pow_eq_monomial_erase {σ F : Type} [Field F] [DecidableEq σ]
  (sample_removed : σ)
  (x : σ →₀ ℕ) :
    ((x.support.filter (fun y => ¬y = sample_removed)).prod fun x_1 => X x_1 ^ x x_1)
      =
    (monomial (x.erase sample_removed)) (1 : F) := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finsupp.support_erase]
  rw [Finset.prod_erase]
  · rw [Finset.prod_filter]
    congr
    funext x_1
    simp
    by_cases h : x_1 = sample_removed
    · simp only [h, ↓reduceIte, Finsupp.erase_same, pow_zero]
    · simp only [h, ↓reduceIte, ne_eq, not_false_eq_true, Finsupp.erase_ne]
  simp

-- https://github.com/leanprover-community/mathlib4/pull/13026
@[simp]
lemma MvPolynomial.coeff_zero_of_not_mem_support {σ F : Type} [Field F]
    (p : MvPolynomial σ F)
    (m : σ →₀ ℕ)
    (h : m ∉ p.support) :
    coeff m p = 0 := not_mem_support_iff.mp h

lemma MvPolynomial.lt_of_degreeOf_lt_mem_support {σ F : Type} [Field F] [DecidableEq σ]
    (p : MvPolynomial σ F)
    (m : σ →₀ ℕ)
    (d : ℕ)
    (sample_target : σ)
    (hdegree: degreeOf sample_target p < d)
    (m_mem_support: m ∈ support p) :
    m sample_target < d := by
  have hd : 0 < d := by linarith
  rw [MvPolynomial.degreeOf_lt_iff hd] at hdegree
  exact hdegree m m_mem_support

lemma mod_cast_eq_cast_mod (a b : ℕ) : ((a : ℤ) % (b : ℤ)) = ((a % b : ℕ): ℤ) := by
  exact rfl

-- Junyan from Zulip mentions Nat.ModEq.eq_of_lt_of_lt for this
lemma near_mods (a b d : ℕ) (c : ℤ) (ha : a < d) (hb : b < d) (habcd : a = b + c * d) :
    c = 0 := by
  have h := congr_arg (fun p => p % (d : ℤ)) habcd
  simp at h
  rw [mod_cast_eq_cast_mod] at h
  rw [mod_cast_eq_cast_mod] at h
  rw [Int.ofNat_inj] at h
  simp only [ha, Nat.mod_eq_of_lt, hb] at h -- Why isn't the lemma simp tagged?
  rw [h] at habcd
  simp at habcd
  cases habcd <;> linarith

lemma MvPolynomial.bind_ite_filter_aux {σ F : Type} [Field F] [DecidableEq σ]
    (p : MvPolynomial σ F)
    (sample_removed sample_target : σ)
    (hsa : sample_target ≠ sample_removed)
    (d : ℕ) (hd : 0 < d)
    (hdegree: ∀ a ∈ support p, a sample_target < d)
    (m : σ →₀ ℕ)
    (m_sample_target_bound : m sample_target < d) :
    (Finset.filter
      (fun a : σ →₀ ℕ =>
        ((a sample_removed : ℕ) * d ≤ m sample_target + d * m sample_removed )∧
        (Finsupp.erase sample_removed a =
            (Finsupp.erase sample_removed m + Finsupp.single (sample_target) (d * m sample_removed)) -
              Finsupp.single sample_target (a sample_removed * d)))
      (support p))
      =
    (Finset.filter
      (fun a : σ →₀ ℕ => a = m)
      (support p)) := by
  apply Finset.filter_congr
  intro x hx
  replace hx := hdegree x hx
  clear hdegree
  simp_rw [mul_comm d]
  constructor
  · intro ⟨h', h''⟩
    have h''_t := congr_arg (fun p => p sample_target) h''
    simp only [ne_eq, hsa, not_false_eq_true, Finsupp.erase_ne, Finsupp.coe_tsub, Finsupp.coe_add,
      Pi.sub_apply, Pi.add_apply, Finsupp.single_eq_same] at h''_t
    zify [h'] at h''_t
    rw [add_sub_assoc] at h''_t
    rw [<-sub_mul] at h''_t
    have nm := near_mods (x sample_target) (m sample_target) d _ hx m_sample_target_bound h''_t
    rw [nm] at h''_t
    simp at h''_t
    ext val
    by_cases h''' : val = sample_target
    · rw [h'''] at *
      clear h'''
      assumption
    by_cases h'''' : val = sample_removed
    · rw [h''''] at *
      clear h''''
      rw [sub_eq_zero] at nm
      simp at nm
      rw [nm]
    have h''_v := congr_arg (fun p => p val) h''
    clear h''
    simp only [Finsupp.erase, Finsupp.coe_mk, h'''', ↓reduceIte, Finsupp.coe_tsub, Finsupp.coe_add,
      Pi.sub_apply, Pi.add_apply, Finsupp.single_apply] at h''_v
    rw [eq_comm] at h'''
    rw [eq_comm] at h''''
    simp only [h''', ↓reduceIte, add_zero, tsub_zero] at h''_v
    rw [h''_v]
  · intro hxm
    rw [hxm] at *
    simp only [le_add_iff_nonneg_left, zero_le, Finsupp.mem_support_iff, ne_eq, not_not, ge_iff_le,
      add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right, and_self]


lemma MvPolynomial.remove_ite_for_casing {σ F : Type} [Field F] [DecidableEq σ]
    (d : ℕ)
    (sample_removed sample_target : σ)
    (x : σ →₀ ℕ) :
    ((if x sample_removed = 0
      then
        (Finset.prod (Finset.filter (fun y => ¬y = sample_removed) x.support) fun x_1 => X x_1 ^ x x_1 : MvPolynomial σ F)
      else
        (X sample_target ^ d) ^ x sample_removed *
          Finset.prod (Finset.filter (fun x => ¬x = sample_removed) x.support) fun x_1 => X x_1 ^ x x_1)
      =
    ((X sample_target ^ d) ^ x sample_removed *
          Finset.prod (Finset.filter (fun x => ¬x = sample_removed) x.support) fun x_1 => X x_1 ^ x x_1)
    ) := by
  by_cases h : x sample_removed = 0
  · simp only [h, Finsupp.mem_support_iff, ne_eq, not_not, pow_zero, one_mul, ite_self]
  · simp only [h, Finsupp.mem_support_iff, ne_eq, not_not, ite_false]

lemma MvPolynomial.bind₁_ite_pow_eq_zero_of {σ F : Type} [Field F] [DecidableEq σ]
    (p : MvPolynomial σ F)
    (d : ℕ)  (hd : 0 < d)
    (sample_removed sample_target : σ)
    (hsa : sample_target ≠ sample_removed)
    (h : MvPolynomial.bind₁
          ((fun x => (if x = sample_removed then MvPolynomial.X sample_target ^ d else MvPolynomial.X x)))
          p = 0)
    (hdegree : p.degreeOf sample_target < d) :
    p = 0 := by
  ext m
  simp only [coeff_zero]
  by_cases m_sample_target_bound : m sample_target < d
  · have :
        coeff m p
          =
        coeff
          (m.erase sample_removed + Finsupp.single sample_target (d * m sample_removed))
          ((bind₁ fun x => if x = sample_removed then X sample_target ^ d else X x) p) := by
      unfold MvPolynomial.bind₁
      nth_rewrite 2 [<-MvPolynomial.support_sum_monomial_coeff p]
      simp_rw [aeval_sum, aeval_monomial, ite_pow, algebraMap_eq, coeff_sum, coeff_C_mul, Finsupp.prod, Finset.prod_ite, Finset.filter_eq', Finsupp.mem_support_iff, ne_eq, ite_not,apply_ite Finset.prod, ite_apply, Finset.prod_empty, Finset.prod_singleton, ite_mul, one_mul, MvPolynomial.remove_ite_for_casing, X, MvPolynomial.monomial_pow,MvPolynomial.coeff_monomial_mul']
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_le_iff, Finsupp.coe_add,
        Pi.add_apply, Finsupp.single_eq_same, one_pow, one_mul, mul_ite, mul_zero]
      simp_rw [Finset.sum_ite]
      simp only [not_le, Finset.sum_const_zero, add_zero]
      simp only [ne_eq, hsa, not_false_eq_true, Finsupp.erase_ne]
      simp_rw [←MvPolynomial.X_pow_eq_monomial]
      simp_rw [MvPolynomial.prod_neq_pow_eq_monomial_erase sample_removed]
      simp only [coeff_monomial, mul_ite, mul_one, mul_zero]
      simp_rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, add_zero]
      rw [eq_comm]
      rw [MvPolynomial.degreeOf_lt_iff hd] at hdegree
      rw [Finset.filter_filter]
      rw [MvPolynomial.bind_ite_filter_aux (σ := σ) p sample_removed sample_target hsa d hd hdegree m m_sample_target_bound]
      simp only [Finset.filter_eq', mem_support_iff, ne_eq]
      -- why is Finset.filter_eq' not simp tagged?
      by_cases h' : m ∈ p.support
      · convert Finset.sum_singleton (p.coeff) m
        simp only [ite_eq_left_iff]
        tauto
      · have h''' : (if m ∈ support p then ({m} : Finset (σ →₀ ℕ)) else ∅) = (∅ : Finset (σ →₀ ℕ)) := by
          simp only [h', ↓reduceIte]
        rw [h''']
        simp only [Finset.sum_empty, mem_support_iff, coeff_zero_of_not_mem_support p m h', ne_eq,
          not_true_eq_false, not_false_eq_true, coeff_zero_of_not_mem_support]
    rw [this]
    rw [h]
    simp
  · apply MvPolynomial.coeff_zero_of_not_mem_support
    contrapose! m_sample_target_bound
    exact lt_of_degreeOf_lt_mem_support p m d sample_target hdegree m_sample_target_bound

lemma AlgHom.list_map_sum {R : Type u} {A : Type v} {B : Type w}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {ι : Type u_1} (f : ι → A) (s : List ι) :
    φ (List.sum (s.map fun (x : ι) => f x)) = List.sum (s.map fun (x : ι) => φ (f x)) := by
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih]


end
