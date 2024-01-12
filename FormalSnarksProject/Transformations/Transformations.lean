
import FormalSnarksProject.Transformations.AGMProofSystem

-- correct import?
-- correct import?
-- name changed to logic equiv fin
-- name changed to logic equiv fin
open scoped BigOperators

section

/-!

This file contains classes for noninteractive proof systems.

-/


universe u

variable {F : Type}

variable [Field F]

-- The types of the statement and witness are assumed to be collections of n_stmt and n_wit field elements respectively.
-- variables {n_sample n_crs n_stmt n_wit n_proof : ℕ}
variable {n_stmt n_wit : ℕ}

-- def STMT := fin n_stmt -> F
-- def WIT := fin n_wit -> F
theorem lambda_mul {A B : Type u} [Mul A] (a : A) (b : B → A) :
    (fun i : B => a * b i) = (fun i => a) * b :=
  by
  ext i
  rw [Pi.mul_apply]
#align lambda_mul lambda_mul

-- def uniform_degree {σ F : Type*} [field F] (p : mv_polynomial σ F) (d : ℕ) : Prop :=
-- TODO mathlib
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/MvPolynomial/Homogeneous.html#MvPolynomial.IsHomogeneous
def UniformDegree {σ F : Type _} [Field F] (p : MvPolynomial σ F) (d : ℕ) : Prop :=
  ∀ m ∈ p.support, (Finsupp.sum m fun s k => k) = d
#align uniform_degree UniformDegree

theorem MvPolynomial.bind₁_sum (T σ τ F : Type _) (S : Finset T) [CommSemiring F]
    (f : σ → MvPolynomial τ F) (g : T → MvPolynomial σ F) :
    MvPolynomial.bind₁ f (∑ s in S, g s) = ∑ s in S, MvPolynomial.bind₁ f (g s) :=
  (MvPolynomial.bind₁ f).map_sum (fun x : T => g x) S
#align mv_polynomial.bind₁_sum MvPolynomial.bind₁_sum

example (T σ τ F : Type _) (A B : Finset T) (f g : T → F) [CommSemiring F]
    (h : ∀ a ∈ A, f a = g a) : ∑ a in A, f a = ∑ a in A, g a := by refine' Finset.sum_congr rfl h

-- todo mathlib
theorem uniformDegree_implies_bind₁_uniformity {σ τ F : Type _} [Field F] (p : MvPolynomial σ F)
    (d : ℕ) (h : UniformDegree p d) (f : σ → MvPolynomial τ F) (a) :
    MvPolynomial.bind₁ ((fun x => MvPolynomial.X a) * f) p =
      MvPolynomial.X a ^ d * MvPolynomial.bind₁ f p :=
  by
  rw [MvPolynomial.as_sum p]
  rw [MvPolynomial.bind₁_sum]
  rw [MvPolynomial.bind₁_sum]
  rw [Finset.mul_sum]
  -- rw [Finset.sum_congr]
  apply Finset.sum_congr
  simp only


  intro y y_mem_support
  unfold UniformDegree at h
  replace h := h y y_mem_support
  simp_rw [MvPolynomial.bind₁_monomial]
  simp only [Pi.mul_apply]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  simp_rw [← mul_assoc]
  congr 1
  rw [mul_comm]
  congr 1
  rw [← h]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
#align uniform_degree_implies_bind₁_uniformity uniformDegree_implies_bind₁_uniformity

-- ring_nf,
-- end
theorem MvPolynomial.mul_x_eq_zero {σ R : Type _} [CommSemiring R] (s : σ) (p : MvPolynomial σ R)
    (h : MvPolynomial.X s * p = 0) : p = 0 :=
  by
  rw [MvPolynomial.ext_iff] at h ⊢
  intro m
  replace h := h (m + Finsupp.single s 1)
  simp at h
  rw [mul_comm] at h
  rw [MvPolynomial.coeff_mul_X] at h
  -- generalize to X_pow
  simp [h]
#align mv_polynomial.mul_X_eq_zero MvPolynomial.mul_x_eq_zero

-- todo mathlib
theorem MvPolynomial.mul_x_pow_eq_zero {σ R : Type _} [CommSemiring R] {s : σ} (d : ℕ)
    (p : MvPolynomial σ R) (h : MvPolynomial.X s ^ d * p = 0) : p = 0 :=
  by
  induction d with
  | zero =>
    simp at h
    exact h
  | succ x' d_ih =>
    apply d_ih
    rw [pow_succ] at h
    apply MvPolynomial.mul_x_eq_zero s
    rw [← mul_assoc]
    exact h
#align mv_polynomial.mul_X_pow_eq_zero MvPolynomial.mul_x_pow_eq_zero

/--
Given a particular toxic waste sample, we can multiply this sample through all crs elems without affecting the soundness of the SNARK. This assumes that all checks have uniform degree as polynomials over the proof elements, (indeed for bilinear pairings, these polynomials will have degree 2) -/
noncomputable def changeExponent (𝓟 : AGMProofSystem F n_stmt n_wit) (sample : Fin 𝓟.nSample)
    (d : ℕ) (all_checks_uniform_degree : ∀ c ∈ 𝓟.polynomial_checks, UniformDegree c d) :
    AGMProofSystem F n_stmt n_wit where
  relation := 𝓟.relation
  nSample := 𝓟.nSample
  nCrs := 𝓟.nCrs
  crs_elems := (fun i => MvPolynomial.X sample) * 𝓟.crs_elems
  proof_elems_index := 𝓟.proof_elems_index
  -- proof_crs_component := 𝓟.proof_crs_component,
  polynomial_checks := 𝓟.polynomial_checks
  proof_element_checks := 𝓟.proof_element_checks
  extractor := 𝓟.extractor
  soundness :=
    by
    -- sorry,
    rintro stmt agm ⟨poly_checks_pass', proof_elem_checks_pass'⟩
    apply 𝓟.soundness
    constructor
    · intro c in_checks
      -- f, -- f_never_zero,
      replace poly_checks_pass' := poly_checks_pass' c in_checks
      simp at *
      have :
        (⇑(MvPolynomial.bind₁ fun pf_idx : 𝓟.proof_elems_index =>
                ∑ x : Fin 𝓟.n_crs, agm pf_idx x • (MvPolynomial.X sample * 𝓟.crs_elems x)))
            c =
          MvPolynomial.X sample ^ d *
            (⇑(MvPolynomial.bind₁ fun pf_idx : 𝓟.proof_elems_index =>
                  ∑ x : Fin 𝓟.n_crs, agm pf_idx x • 𝓟.crs_elems x))
              c :=
        by
        have funeq :
          (fun pf_idx : 𝓟.proof_elems_index =>
              ∑ x : Fin 𝓟.n_crs, agm pf_idx x • (MvPolynomial.X sample * 𝓟.crs_elems x)) =
            fun pf_idx : 𝓟.proof_elems_index =>
            ∑ x : Fin 𝓟.n_crs, MvPolynomial.X sample * agm pf_idx x • 𝓟.crs_elems x :=
          by
          funext
          congr
          funext
          simp_rw [MvPolynomial.smul_eq_C_mul]
          ring
        -- library_search,
        simp_rw [funeq]
        simp_rw [← Finset.mul_sum]
        apply uniformDegree_implies_bind₁_uniformity
        apply all_checks_uniform_degree
        apply in_checks
      -- sorry,
      rw [this] at poly_checks_pass'
      have foo := MvPolynomial.mul_x_pow_eq_zero _ _ poly_checks_pass'
      exact foo
    -- rw mv_polynomial.eval
    -- exact poly_checks_pass',
    -- unfold function.comp at checks_give_zero ⊢,
    -- simp at *,
    -- simp_rw mv_polynomial.smul_eq_C_mul at *,
    · intro idx val val_in
      replace proof_elem_checks_pass' := proof_elem_checks_pass' idx val val_in
      exact proof_elem_checks_pass'
#align change_exponent changeExponent

theorem sum_conditional {S R : Type} [Fintype S] [CommRing R] (f : S → R) (p : S → Prop)
    [DecidablePred p] : ∑ s : S, f s = ∑ s : S, ite (p s) (f s) 0 + ∑ s : S, ite (p s) 0 (f s) :=
  by
  rw [← Finset.sum_add_distrib]
  congr
  funext s
  by_cases hp : p s
  simp [hp]
  simp [hp]
#align sum_conditional sum_conditional

theorem ite_or_eq_sum {S R : Type} [Fintype S] [CommRing R] {s a b : S} (h : a ≠ b) [DecidableEq S]
    (f : S → R) : ite (s = a ∨ s = b) (f s) 0 = ite (s = a) (f a) 0 + ite (s = b) (f b) 0 :=
  by
  by_cases ha : s = a
  · by_cases hb : s = b
    simp [h, ha, hb]
    exfalso
    rw [← ha, ← hb] at h
    apply h
    rfl
    simp [h, ha, hb]
  · by_cases hb : s = b
    simp [h, ha, hb]
    sorry
    sorry
#align ite_or_eq_sum ite_or_eq_sum

theorem sum_or_two_eq {S R : Type} [Fintype S] [CommRing R] {a b : S} (h : a ≠ b) [DecidableEq S]
    (f : S → R) : ∑ s : S, ite (s = a ∨ s = b) (f s) 0 = f a + f b :=
  by
  simp_rw [ite_or_eq_sum h]
  -- doesn't work without the h, why?
  rw [Finset.sum_add_distrib]
  congr
  simp
  simp
#align sum_or_two_eq sum_or_two_eq

example {S R : Type} [Fintype S] [CommRing R] (f : S → R) (a : S) (p : Prop) [Decidable p] :
    ite p a a = a :=
  if_t_t p a

@[simp]
theorem or_and_self_left (p q : Prop) : (p ∨ q) ∧ q ↔ q := by tauto
#align or_and_self_left or_and_self_left

@[simp]
theorem or_and_self_right (p q : Prop) : (p ∨ q) ∧ p ↔ p := by tauto
#align or_and_self_right or_and_self_right

@[simp]
theorem foobar1 (α : Type) (a b c : α) (h : b ≠ c) : (a = b ∨ a = c) ∧ ¬a = c ↔ a = b := by tidy
#align foobar1 foobar1

@[simp]
theorem foobar2 (α : Type) (a b c : α) (h : b ≠ c) : (a = b ∨ a = c) ∧ ¬a = b ∧ ¬a = c ↔ False := by
  tidy
#align foobar2 foobar2

-- example {A : Type} (a b : A) : a = b ↔ b = a := by {exact eq_comm}
/--
Adds one crs element to another and zeros out the added element. This might be useful in the case where in the given SNARK, this pair of CRS elements are always used with the same coefficient, in which case the resulting SNARK is complete. -/
noncomputable def collapseCrsElement (𝓟 : AGMProofSystem F n_stmt n_wit) (twin1 twin2 : Fin 𝓟.nCrs)
    (not_same : twin1 ≠ twin2)
    (interchangeable :
      ∀ (stmt : Fin n_stmt → F) (val : (Fin n_stmt → F) → Fin 𝓟.nCrs → F) (idx : 𝓟.proof_elems_index)
        (val_in : val ∈ 𝓟.proof_element_checks idx) (agm : 𝓟.proof_elems_index → Fin 𝓟.nCrs → F),
        val stmt = agm idx → agm idx twin1 = agm idx twin2) :
    AGMProofSystem F n_stmt n_wit where
  relation := 𝓟.relation
  nSample := 𝓟.nSample
  nCrs := 𝓟.nCrs
  crs_elems crs :=
    if crs = twin1 then 𝓟.crs_elems twin1 + 𝓟.crs_elems twin2
    else if crs = twin2 then 0 else 𝓟.crs_elems crs
  proof_elems_index := 𝓟.proof_elems_index
  polynomial_checks := 𝓟.polynomial_checks
  proof_element_checks := 𝓟.proof_element_checks
  -- λ idx,
  --   (𝓟.proof_element_checks idx).map
  --   (λ old stmt crs, (if crs = twin2 then old stmt twin1 else old stmt crs)) ,
  -- When the extractor goes to read the component of the second twin, it should instead read the first
  extractor agm wit :=
    𝓟.extractor (fun proof_elem crs => agm proof_elem (if crs = twin2 then twin1 else crs)) wit
  soundness :=
    by
    -- sorry,
    rintro stmt agm ⟨poly_checks_pass', proof_elem_checks_pass'⟩
    apply 𝓟.soundness
    constructor
    · intro c in_checks
      -- f, -- f_never_zero,
      replace poly_checks_pass' := poly_checks_pass' c in_checks
      -- simp at *,
      rw [← poly_checks_pass']
      apply congr; apply congr; rfl; apply congr; rfl
      funext
      simp_rw [MvPolynomial.smul_eq_C_mul]
      simp_rw [apply_ite (agm pf_idx)]
      simp_rw [apply_ite MvPolynomial.C]
      simp_rw [ite_mul]
      simp_rw [mul_ite]
      -- simp_rw [if_t_t p a],
      rw [sum_conditional _ fun x => x = twin1 ∨ x = twin2]
      nth_rw 3 [sum_conditional _ fun x => x = twin1 ∨ x = twin2]
      congr 1
      · simp_rw [sum_or_two_eq not_same]
        simp
        simp_rw [@eq_comm _ twin2 twin1]
        simp [not_same]
        ring
      · congr 1
        funext s
        simp
        -- simp_rw finset.sum_ite_eq',
        -- simp only [finset.mem_univ, if_true],
        sorry
      -- simp_rw ←ite_and,
      -- split_ifs,
      -- refl,
      -- contrapose! not_same,
      -- rw [<-h_1, <-h_2],
      -- contrapose! h, right, assumption,
      -- contrapose! h, left, assumption,
      -- refl,
      -- tidy,
      rfl
    · -- sorry,
      intro idx val val_in
      -- need to pass in a different val
      replace proof_elem_checks_pass' := proof_elem_checks_pass' idx val val_in
      rw [proof_elem_checks_pass']
      funext
      split_ifs
      rotate_left
      rfl
      rw [h]
      replace interchangeable := interchangeable stmt val idx val_in agm proof_elem_checks_pass'
      rw [interchangeable]
#align collapse_crs_element collapseCrsElement

noncomputable def zeroAndCarry {A : Type} (x : A →₀ ℕ) (source target : A) (factor : ℕ) : A →₀ ℕ :=
  x.eraseₓ source + Finsupp.single target (factor * x source)
#align zero_and_carry zeroAndCarry

/-- This is the technical lemma on which the toxic waste collapse is based. We omit the proof. -/
theorem commutable_zeroAndCarry {F proof_elems_index : Type} [Field F] (n_sample n_crs : ℕ)
    (d d2 : ℕ) (sample_removed sample_target : Fin n_sample) (multinomial : Fin n_sample →₀ ℕ)
    (crs_elems : Fin n_crs → MvPolynomial (Fin n_sample) F)
    (agm : proof_elems_index → Fin n_crs → F) (c : MvPolynomial proof_elems_index F)
    (h : ∀ crs_idx : Fin n_crs, MvPolynomial.degreeOf sample_target (crs_elems crs_idx) < d)
    (uniform_deg : UniformDegree c d2) :
    MvPolynomial.coeff multinomial
        ((MvPolynomial.aeval fun pf_idx : proof_elems_index =>
            ∑ crs_idx : Fin n_crs, agm pf_idx crs_idx • crs_elems crs_idx)
          c) =
      MvPolynomial.coeff (zeroAndCarry multinomial sample_removed sample_target (d * d2))
        ((MvPolynomial.aeval fun pf_idx : proof_elems_index =>
            ∑ x : Fin n_crs,
              agm pf_idx x •
                MvPolynomial.eval₂ MvPolynomial.C
                  (fun x : Fin n_sample =>
                    ite (x = sample_removed) (MvPolynomial.X sample_target ^ d) (MvPolynomial.X x))
                  (crs_elems x))
          c) :=
  by sorry
#align commutable_zero_and_carry commutable_zeroAndCarry

-- Returns a SNARK where one fewer toxic waste element is actually used, replaced by sample_target ^ d
noncomputable def collapseToxicWaste (𝓟 : AGMProofSystem F n_stmt n_wit) (d d2 : ℕ)
    (sample_removed sample_target : Fin 𝓟.nSample)
    (h : ∀ crs_idx : Fin 𝓟.nCrs, MvPolynomial.degreeOf sample_target (𝓟.crs_elems crs_idx) < d)
    -- (all polychecks are of uniform degree d2)
    (uniform_deg : ∀ p ∈ 𝓟.polynomial_checks, UniformDegree p d2) :
    AGMProofSystem F n_stmt n_wit where
  relation := 𝓟.relation
  nSample := 𝓟.nSample
  nCrs := 𝓟.nCrs
  crs_elems :=
    (MvPolynomial.eval₂ MvPolynomial.C fun x =>
        if x = sample_removed then MvPolynomial.X sample_target ^ d else MvPolynomial.X x) ∘
      𝓟.crs_elems
  proof_elems_index := 𝓟.proof_elems_index
  -- proof_crs_component := 𝓟.proof_crs_component,
  polynomial_checks := 𝓟.polynomial_checks
  proof_element_checks := 𝓟.proof_element_checks
  extractor := 𝓟.extractor
  soundness := by
    rintro stmt agm ⟨poly_checks_pass', proof_elem_checks_pass'⟩
    apply 𝓟.soundness
    constructor
    · intro c in_checks
      replace poly_checks_pass' := poly_checks_pass' c in_checks
      -- f f_never_zero,
      simp at *
      have all_coeffs_of_new_snark_zero :
        ∀ multinomial : Fin 𝓟.n_sample →₀ ℕ,
          ((⇑(MvPolynomial.bind₁ fun pf_idx : 𝓟.proof_elems_index =>
                      ∑ x : Fin 𝓟.n_crs,
                        agm pf_idx x •
                          MvPolynomial.eval₂ MvPolynomial.C
                            (fun x : Fin 𝓟.n_sample =>
                              ite (x = sample_removed) (MvPolynomial.X sample_target ^ d)
                                (MvPolynomial.X x))
                            (𝓟.crs_elems x)))
                  c).coeff
              multinomial =
            0 :=
        mv_polynomial.eq_zero_iff.mp poly_checks_pass'
      -- follows from extensionality on the polynomial
      have
        all_coeffs_of_old_snark_are_a_coeff_of_the_new :-- in particular, the coeff of a multinomial is what you get from zeroing out the sample_removed and multiplying this value by d * d2 and adding to sample target
        ∀ multinomial : Fin 𝓟.n_sample →₀ ℕ,
          ((⇑(MvPolynomial.bind₁ fun pf_idx : 𝓟.proof_elems_index =>
                      ∑ crs_idx : Fin 𝓟.n_crs, agm pf_idx crs_idx • 𝓟.crs_elems crs_idx))
                  c).coeff
              multinomial =
            ((⇑(MvPolynomial.bind₁ fun pf_idx : 𝓟.proof_elems_index =>
                      ∑ x : Fin 𝓟.n_crs,
                        agm pf_idx x •
                          MvPolynomial.eval₂ MvPolynomial.C
                            (fun x : Fin 𝓟.n_sample =>
                              ite (x = sample_removed) (MvPolynomial.X sample_target ^ d)
                                (MvPolynomial.X x))
                            (𝓟.crs_elems x)))
                  c).coeff
              (zeroAndCarry multinomial sample_removed sample_target (d * d2)) :=
        by
        intro
        clear all_coeffs_of_new_snark_zero
        simp_rw [MvPolynomial.bind₁]
        apply commutable_zeroAndCarry
        apply h
        apply uniform_deg
        exact in_checks
      rw [MvPolynomial.eq_zero_iff]
      intro d
      rw [all_coeffs_of_old_snark_are_a_coeff_of_the_new d]
      rw [all_coeffs_of_new_snark_zero]
    -- thus all coeffs for old snark zero
    -- thus sound
    · intro idx val val_in
      replace proof_elem_checks_pass' := proof_elem_checks_pass' idx val val_in
      exact proof_elem_checks_pass'
#align collapse_toxic_waste collapseToxicWaste

end
