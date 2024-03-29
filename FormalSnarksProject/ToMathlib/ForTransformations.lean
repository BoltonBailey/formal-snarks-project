
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.MvPolynomial.Monad

section

/-!

This file contains lemmas needed for the transformations file

-/

universe u

variable {F : Type}

variable [Field F]

-- https://github.com/leanprover-community/mathlib4/pull/11071
@[simp]
lemma MvPolynomial.X_ne_zero {σ R : Type _} [Field R] (s : σ) :
    MvPolynomial.X (R := R) s ≠ 0 := by
  intro h
  have h' := congr_arg (fun p => p.coeff (Finsupp.single s 1)) h
  simp only [coeff_X, coeff_zero, one_ne_zero] at h'

-- Additive version. TODO use @[to_additive] instead
lemma List.sum_map_ite_eq {A B : Type} [DecidableEq A] [CommRing B] (f g : A → B) (a : A) (l : List A) :
    List.sum (List.map (fun x => ite (x = a) (f x) (g x)) l)
      =
    ((List.count a l) : B) * (f a - g a) + List.sum (List.map g l)  :=
  by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [map_cons, sum_cons, nodup_cons, ne_eq, mem_cons] at ih ⊢
    rw [ih]
    clear ih
    rw [List.count_cons]
    simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    by_cases hx : x = a
    · simp only [hx, ite_true]
      ring
    · simp only [hx, ite_false, ne_comm.mp hx, add_zero]
      ring

-- https://github.com/leanprover-community/mathlib4/pull/11073
theorem MvPolynomial.degreeOf_C_mul_le {R σ : Type} [CommSemiring R] (j : σ)
    (c : R) (f : MvPolynomial σ R) :
    MvPolynomial.degreeOf j (MvPolynomial.C c * f) ≤ MvPolynomial.degreeOf j f := by
  unfold degreeOf
  have := degrees_mul (C c) f
  simp [MvPolynomial.degrees_C] at this
  convert Multiset.count_le_of_le j this

-- https://github.com/leanprover-community/mathlib4/pull/11106
theorem MvPolynomial.degreeOf_C_mul {σ R : Type} [Field R] (j : σ)
    (c : R) (hc : c ≠ 0) (f : MvPolynomial σ R) :
    MvPolynomial.degreeOf j (MvPolynomial.C c * f) = MvPolynomial.degreeOf j f := by
  rw [Nat.eq_iff_le_and_ge]
  constructor
  · convert MvPolynomial.degreeOf_C_mul_le j c f
  · have := MvPolynomial.degreeOf_C_mul_le j (1/c) (C (c) * f)
    rw [<-mul_assoc] at this
    rw [←C_mul] at this
    simp only [one_div, ne_eq, hc, not_false_eq_true, inv_mul_cancel, map_one, one_mul] at this
    convert this

@[simp]
lemma MvPolynomial.coeff_single_X {R : Type} {σ : Type u_1} [CommSemiring R] [DecidableEq σ]
    (j : σ) (n : ℕ)
    (x : σ) :
    MvPolynomial.coeff (R := R) (Finsupp.single j n) (MvPolynomial.X x) = if n = 1 ∧ j = x then 1 else 0  := by
  rw [MvPolynomial.X, MvPolynomial.coeff_monomial]
  congr
  simp [Finsupp.single_eq_single_iff]
  tauto

@[simp]
lemma MvPolynomial.coeff_single_X_pow {R : Type} {σ : Type u_1} [CommSemiring R] [DecidableEq σ]
    (j : σ) (n k : ℕ)
    (x : σ) :
    MvPolynomial.coeff (R := R) (Finsupp.single j n) (MvPolynomial.X x ^ k) = if n = k ∧ j = x ∨ k = 0 ∧ n = 0 then 1 else 0  := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  congr
  simp [Finsupp.single_eq_single_iff]
  tauto

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

-- https://github.com/leanprover-community/mathlib4/pull/11109
lemma MvPolynomial.prod_X_pow_eq_monomial {σ F : Type} [Field F] [DecidableEq σ]
  (x : σ →₀ ℕ) :
    (Finset.prod (x.support) fun x_1 => X x_1 ^ x x_1)
      =
    (monomial x) (1 : F) := by
  rw [MvPolynomial.monomial_eq]
  simp
  unfold Finsupp.prod
  simp

lemma MvPolynomial.prod_neq_pow_eq_monomial_erase {σ F : Type} [Field F] [DecidableEq σ]
  (sample_removed : σ)
  (x : σ →₀ ℕ) :
    (Finset.prod (Finset.filter (fun y => ¬y = sample_removed) x.support) fun x_1 => X x_1 ^ x x_1)
      =
    (monomial (x.erase sample_removed)) (1 : F) := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial (F := F) (x.erase sample_removed)]
  simp only [Finsupp.mem_support_iff, ne_eq, not_not, Finsupp.support_erase]
  rw [Finset.prod_erase]
  · rw [Finset.prod_filter]
    congr
    funext x_1
    simp
    by_cases h : x_1 = sample_removed
    · simp [h]
    · simp [h]
  simp

@[simp]
lemma MvPolynomial.coeff_zero_of_not_mem_support {σ F : Type} [Field F] [DecidableEq σ]
    (p : MvPolynomial σ F)
    (m : σ →₀ ℕ)
    (h : m ∉ p.support) :
    coeff m p = 0 := by
  exact not_mem_support_iff.mp h

lemma MvPolynomial.not_mem_support_of_degreeOf {σ F : Type} [Field F] [DecidableEq σ]
    (p : MvPolynomial σ F)
    (m : σ →₀ ℕ)
    (d : ℕ)  (hd : 0 < d)
    (sample_target : σ)
    (hdegree: degreeOf sample_target p < d)
    (m_sample_target_bound: ¬m sample_target < d) :
    m ∉ support p := by
  intro h
  rw [MvPolynomial.degreeOf_lt_iff hd] at hdegree
  apply m_sample_target_bound
  exact hdegree m h

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
  simp [ha,hb, Nat.mod_eq_of_lt]  at h -- Why isn't the lemma simp tagged?
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
            (Finsupp.erase sample_removed m + fun₀ | sample_target => d * m sample_removed) -
              fun₀ | sample_target => a sample_removed * d))
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
    simp [hsa] at h''_t
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
    simp [h''', h'''', Finsupp.single_apply, Finsupp.erase] at h''_v
    rw [eq_comm] at h'''
    rw [eq_comm] at h''''
    simp [h''', h'''', Finsupp.single_apply, Finsupp.erase] at h''_v
    rw [h''_v]
  · intro hxm
    rw [hxm] at *
    simp only [le_add_iff_nonneg_left, zero_le, Finsupp.mem_support_iff, ne_eq, not_not, ge_iff_le,
      add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right, and_self]

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
      simp?
      simp_rw [Finset.sum_ite]
      simp?
      simp [hsa]
      simp_rw [←MvPolynomial.X_pow_eq_monomial]
      simp_rw [MvPolynomial.prod_neq_pow_eq_monomial_erase sample_removed]
      simp?
      simp_rw [Finset.sum_ite]
      simp?
      rw [eq_comm]
      rw [MvPolynomial.degreeOf_lt_iff hd] at hdegree
      rw [Finset.filter_filter]
      rw [MvPolynomial.bind_ite_filter_aux (σ := σ) p sample_removed sample_target hsa d hd hdegree m m_sample_target_bound]
      simp [Finset.filter_eq'] -- why is this lemma not simp tagged?
      by_cases h' : m ∈ p.support
      · convert Finset.sum_singleton (p.coeff) m
        simp only [ite_eq_left_iff]
        tauto
      · have h''' : (if m ∈ support p then ({m} : Finset (σ →₀ ℕ)) else ∅) = (∅ : Finset (σ →₀ ℕ)) := by
          simp [h']
          exact coeff_zero_of_not_mem_support p m h'
        rw [h''']
        simp [coeff_zero_of_not_mem_support p m h']
    rw [this]
    rw [h]
    simp
  · apply MvPolynomial.coeff_zero_of_not_mem_support
    exact not_mem_support_of_degreeOf p m d hd sample_target hdegree m_sample_target_bound

lemma AlgHom.list_map_sum {R : Type u} {A : Type v} {B : Type w}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {ι : Type u_1} (f : ι → A) (s : List ι) :
    φ (List.sum (s.map fun (x : ι) => f x)) = List.sum (s.map fun (x : ι) => φ (f x)) := by
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    simp [ih]


end
