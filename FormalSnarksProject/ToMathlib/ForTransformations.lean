/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Monad
public import CompPoly.OrdMultivariate.Operations
public import CompPoly.OrdMultivariate.Rename
public import CompPoly.OrdMultivariate.MvPolyEquiv

/-!

This file contains lemmas needed for the transformations file

-/

public section

section

universe u

variable {F : Type}

variable [Field F]

-- `List.prod_map_ite_eq` / `List.sum_map_ite_eq` (PR 13023) are now in Mathlib.

-- `MvPolynomial.degreeOf_C_mul` (PR 11106) is now in Mathlib.

-- `MvPolynomial.coeff_single_X` / `coeff_single_X_pow` (PR 13024) are now in Mathlib.

lemma MvPolynomial.prod_neq_pow_eq_monomial_erase {σ F : Type} [Field F] [DecidableEq σ]
  (sample_removed : σ)
  (x : σ →₀ ℕ) :
    ((x.support.filter (fun y => ¬y = sample_removed)).prod fun x_1 => X x_1 ^ x x_1)
      =
    (monomial (x.erase sample_removed)) (1 : F) := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  simp only [Finsupp.support_erase]
  rw [Finset.prod_erase]
  · rw [Finset.prod_filter]
    congr
    funext x_1
    simp
    by_cases h : x_1 = sample_removed
    · simp only [h, ↓reduceIte, Finsupp.erase_same, pow_zero]
    · simp only [h, ↓reduceIte, ne_eq, not_false_eq_true, Finsupp.erase_ne]
  simp

lemma Int.near_mods (a b c d : ℤ) (ha' : 0 ≤ a) (hb' : 0 ≤ b)
    (ha : a < d) (hb : b < d) (habcd : a = b + c * d) :
    c = 0 := by
  -- TODO reprove with `Int.eq_zero_of_abs_lt_dvd`?
  -- TODO reprove below with this lemma
  have h := congr_arg (fun p => p % (d : ℤ)) habcd
  simp_rw [Int.add_mul_emod_self_right] at h
  rw [emod_eq_of_lt ha' ha, emod_eq_of_lt hb' hb] at h
  have hd : 0 < d := lt_of_le_of_lt ha' ha
  have hcd : c * d = 0 := by linarith
  exact (mul_eq_zero.mp hcd).resolve_right (by omega)


-- Junyan from Zulip mentions Nat.ModEq.eq_of_lt_of_lt for this
lemma near_mods (a b d : ℕ) (c : ℤ) (ha : a < d) (hb : b < d) (habcd : a = b + c * d) :
    c = 0 :=
  Int.near_mods a b c d (by positivity) (by positivity)
    (by exact_mod_cast ha) (by exact_mod_cast hb) habcd

lemma MvPolynomial.bind_ite_filter_aux {σ F : Type} [Field F] [DecidableEq σ]
    (p : MvPolynomial σ F)
    (sample_removed sample_target : σ)
    (hsa : sample_target ≠ sample_removed)
    (d : ℕ) (_hd : 0 < d)
    (hdegree : ∀ a ∈ support p, a sample_target < d)
    (m : σ →₀ ℕ)
    (m_sample_target_bound : m sample_target < d) :
    (Finset.filter
      (fun a : σ →₀ ℕ =>
        ((a sample_removed : ℕ) * d ≤ m sample_target + d * m sample_removed )∧
        (Finsupp.erase sample_removed a =
            (Finsupp.erase sample_removed m +
                Finsupp.single (sample_target) (d * m sample_removed)) -
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
    simp only [zero_mul, add_zero, Nat.cast_inj] at h''_t
    ext val
    by_cases h''' : val = sample_target
    · rw [h'''] at *
      clear h'''
      assumption
    by_cases h'''' : val = sample_removed
    · rw [h''''] at *
      clear h''''
      rw [sub_eq_zero] at nm
      simp only [Nat.cast_inj] at nm
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
    simp only [le_add_iff_nonneg_left, zero_le, add_tsub_cancel_right, and_self]


lemma MvPolynomial.remove_ite_for_casing {σ F : Type} [Field F] [DecidableEq σ]
    (d : ℕ)
    (sample_removed sample_target : σ)
    (x : σ →₀ ℕ) :
    ((if x sample_removed = 0
      then
        (Finset.prod (Finset.filter (fun y => ¬y = sample_removed) x.support)
          fun x_1 => X x_1 ^ x x_1 : MvPolynomial σ F)
      else
        (X sample_target ^ d) ^ x sample_removed *
          Finset.prod (Finset.filter (fun x => ¬x = sample_removed) x.support)
            fun x_1 => X x_1 ^ x x_1)
      =
    ((X sample_target ^ d) ^ x sample_removed *
          Finset.prod (Finset.filter (fun x => ¬x = sample_removed) x.support)
            fun x_1 => X x_1 ^ x x_1)
    ) := by
  by_cases h : x sample_removed = 0
  · simp only [h, pow_zero, one_mul, ite_self]
  · simp only [h, ite_false]

lemma MvPolynomial.bind₁_ite_pow_eq_zero_of {σ F : Type} [Field F] [DecidableEq σ]
    (p : MvPolynomial σ F)
    (d : ℕ) (hd : 0 < d)
    (sample_removed sample_target : σ)
    (hsa : sample_target ≠ sample_removed)
    (h : MvPolynomial.bind₁
          ((fun x =>
            (if x = sample_removed then MvPolynomial.X sample_target ^ d else MvPolynomial.X x)))
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
      simp_rw [aeval_sum, aeval_monomial, ite_pow, algebraMap_eq, coeff_sum, coeff_C_mul,
        Finsupp.prod, Finset.prod_ite, Finset.filter_eq', Finsupp.mem_support_iff, ne_eq, ite_not,
        apply_ite Finset.prod, ite_apply, Finset.prod_empty, Finset.prod_singleton, ite_mul,
        one_mul, MvPolynomial.remove_ite_for_casing, X, MvPolynomial.monomial_pow,
        MvPolynomial.coeff_monomial_mul']
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
      rw [MvPolynomial.bind_ite_filter_aux (σ := σ) p sample_removed sample_target hsa d hd hdegree
        m m_sample_target_bound]
      simp only [Finset.filter_eq', mem_support_iff, ne_eq]
      -- why is Finset.filter_eq' not simp tagged?
      by_cases h' : m ∈ p.support
      · convert Finset.sum_singleton (p.coeff) m
        simp only [ite_eq_left_iff]
        tauto
      · have h''' :
            (if m ∈ support p then ({m} : Finset (σ →₀ ℕ)) else ∅) = (∅ : Finset (σ →₀ ℕ)) := by
          simp only [h', ↓reduceIte]
        rw [h''']
        simp only [Finset.sum_empty, notMem_support_iff.mp h']
    rw [this]
    rw [h]
    simp
  · apply MvPolynomial.notMem_support_iff.mp
    contrapose! m_sample_target_bound
    exact lt_of_le_of_lt (monomial_le_degreeOf sample_target m_sample_target_bound) hdegree

lemma AlgHom.list_map_sum {R : Type u} {A : Type v} {B : Type w}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) {ι : Type u_1} (f : ι → A) (s : List ι) :
    φ (List.sum (s.map fun (x : ι) => f x)) = List.sum (s.map fun (x : ι) => φ (f x)) := by
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih]

lemma RingHom.list_map_sum {A : Type v} {B : Type w} [Semiring A] [Semiring B]
    (φ : A →+* B) {ι : Type u_1} (f : ι → A) (s : List ι) :
    φ (List.sum (s.map fun (x : ι) => f x)) = List.sum (s.map fun (x : ι) => φ (f x)) := by
  induction s with
  | nil =>
    simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih]

/-! ### `COrdMvPolynomial` counterparts, transported along `CPoly.COrdMvPolynomial.ordPolyRingEquiv`

The transformations file manipulates the computable `COrdMvPolynomial` check polynomials
directly; these lemmas transport the needed algebraic facts (no zero divisors, `X ≠ 0`, and
naturality of `bind₁`) from their mathlib `MvPolynomial` counterparts. -/

section CompPolyBridge

open CPoly
open CPoly.COrdMvPolynomial

variable {σ τ F : Type} [Ord σ] [Std.TransOrd σ] [Std.LawfulEqOrd σ]
  [Ord τ] [Std.TransOrd τ] [Std.LawfulEqOrd τ] [Field F] [BEq F] [LawfulBEq F]

/-- `COrdMvPolynomial` over a field has no zero divisors (transported from `MvPolynomial` along
the ring equivalence). -/
instance : NoZeroDivisors (COrdMvPolynomial σ F) :=
  Function.Injective.noZeroDivisors (ordPolyRingEquiv (σ := σ) (R := F))
    (ordPolyRingEquiv (σ := σ) (R := F)).injective (map_zero _) (map_mul _)

lemma CPoly.COrdMvPolynomial.X_ne_zero (v : σ) :
    (COrdMvPolynomial.X v : COrdMvPolynomial σ F) ≠ 0 := by
  intro h
  have equivX : (ordPolyRingEquiv (σ := σ) (R := F)) (COrdMvPolynomial.X v) = MvPolynomial.X v :=
    CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_X v
  have equivZero : (ordPolyRingEquiv (σ := σ) (R := F)) 0 = 0 := map_zero
  have h' := congr_arg (ordPolyRingEquiv (σ := σ) (R := F)) h
  rw [equivX, equivZero] at h'
  exact MvPolynomial.X_ne_zero v h'

/-- `COrdMvPolynomial.bind₁` as an application of the bundled `eval₂Hom` ring homomorphism, so
that `map_*` lemmas apply to it. -/
lemma CPoly.COrdMvPolynomial.bind₁_eq_eval₂Hom
    (f : σ → COrdMvPolynomial τ F) (p : COrdMvPolynomial σ F) :
    COrdMvPolynomial.bind₁ f p
      = COrdMvPolynomial.eval₂Hom (algebraMap F (COrdMvPolynomial τ F)) f p := by
  rw [COrdMvPolynomial.bind₁_eq_aeval]
  rfl

/-- The substitution homomorphism fixes constants. -/
lemma CPoly.COrdMvPolynomial.eval₂Hom_algebraMap_C
    (f : σ → COrdMvPolynomial τ F) (c : F) :
    COrdMvPolynomial.eval₂Hom (algebraMap F (COrdMvPolynomial τ F)) f (COrdMvPolynomial.C c)
      = COrdMvPolynomial.C c := by
  rw [COrdMvPolynomial.eval₂Hom_apply, ← COrdMvPolynomial.aeval_eq_eval₂, COrdMvPolynomial.aeval_C]
  rfl

/-- Naturality of substitution: the computable `COrdMvPolynomial.bind₁` corresponds to mathlib's
`MvPolynomial.bind₁` across the ring equivalence. -/
lemma CPoly.COrdMvPolynomial.ordPolyRingEquiv_bind₁
    (f : σ → COrdMvPolynomial τ F) (p : COrdMvPolynomial σ F) :
    (ordPolyRingEquiv (σ := τ) (R := F)) (COrdMvPolynomial.bind₁ f p)
      = MvPolynomial.bind₁ (fun i => (ordPolyRingEquiv (σ := τ) (R := F)) (f i))
          ((ordPolyRingEquiv (σ := σ) (R := F)) p) := by
  calc (ordPolyRingEquiv (σ := τ) (R := F)) (COrdMvPolynomial.bind₁ f p)
      = ((ordPolyRingEquiv (σ := τ) (R := F)) : COrdMvPolynomial τ F →+* MvPolynomial τ F)
          (MvPolynomial.eval₂ (algebraMap F (COrdMvPolynomial τ F)) f (fromCOrdMvPolynomial p)) := by
        rw [COrdMvPolynomial.bind₁_eq_aeval, COrdMvPolynomial.aeval_eq_eval₂, eval₂_equiv]
        rfl
    _ = MvPolynomial.eval₂
          (((ordPolyRingEquiv (σ := τ) (R := F)) : COrdMvPolynomial τ F →+* MvPolynomial τ F).comp
            (algebraMap F (COrdMvPolynomial τ F)))
          (fun i => (ordPolyRingEquiv (σ := τ) (R := F)) (f i))
          (fromCOrdMvPolynomial p) :=
        MvPolynomial.eval₂_comp_left _ _ _ _
    _ = MvPolynomial.bind₁ (fun i => (ordPolyRingEquiv (σ := τ) (R := F)) (f i))
          ((ordPolyRingEquiv (σ := σ) (R := F)) p) := by
        rw [MvPolynomial.bind₁, MvPolynomial.aeval_def, MvPolynomial.algebraMap_eq]
        congr 1
        exact RingHom.ext fun c => CPoly.COrdMvPolynomial.fromCOrdMvPolynomial_C c

end CompPolyBridge

end
