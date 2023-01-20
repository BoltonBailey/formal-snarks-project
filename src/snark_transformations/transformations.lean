
import .proof_system_fin
import algebra.big_operators.basic

open_locale big_operators

section

/-!

This file contains classes for noninteractive proof systems.

-/

universe u
/-- The finite field parameter of our SNARK -/
variable {F : Type}
variable [field F]

-- The types of the statement and witness are assumed to be collections of n_stmt and n_wit field elements respectively.
-- variables {n_sample n_crs n_stmt n_wit n_proof : ℕ}
variables {n_stmt n_wit : ℕ}

-- def STMT := fin n_stmt -> F
-- def WIT := fin n_wit -> F

lemma lambda_mul {A B : Type u} [has_mul A] (a : A) (b : B → A) : (λ (i : B), a * b i) = (λ i, a) * b :=
begin
  ext i,
  rw pi.mul_apply,
end

-- def uniform_degree {σ F : Type*} [field F] (p : mv_polynomial σ F) (d : ℕ) : Prop :=

-- TODO mathlib
def uniform_degree {σ F : Type*} [field F] (p : mv_polynomial σ F) (d : ℕ) : Prop := 
∀ m ∈ p.support, finsupp.sum m (λ s k, k) = d


lemma mv_polynomial.bind₁_sum (T σ τ F : Type*) (S : finset T) [comm_semiring F] (f : σ → mv_polynomial τ F) (g : T -> mv_polynomial σ F) :
  mv_polynomial.bind₁ f (∑ s in S, g s) = (∑ s in S, mv_polynomial.bind₁ f (g s)) :=
begin
  exact (mv_polynomial.bind₁ f).map_sum (λ (x : T), g x) S,
end


example (T σ τ F : Type*) (A B : finset T) (f g : T -> F) [comm_semiring F] (h :  ∀ a ∈ A, f a = g a ) : ∑ a in A, f a = ∑ a in A, g a := by refine finset.sum_congr rfl h

-- todo mathlib
lemma uniform_degree_implies_bind₁_uniformity {σ τ F : Type*} [field F] (p : mv_polynomial σ F) (d : ℕ) 
  (h : uniform_degree p d) (f : σ → mv_polynomial τ F) (a):
    mv_polynomial.bind₁ ((λ x, mv_polynomial.X a) * f) p = ((mv_polynomial.X a) ^ d) * mv_polynomial.bind₁ (f) p
:= 
begin
  rw mv_polynomial.as_sum p,
  rw mv_polynomial.bind₁_sum,
  rw mv_polynomial.bind₁_sum,
  rw finset.mul_sum,
  rw finset.sum_congr,
  refl,
  intros y y_mem_support,
  unfold uniform_degree at h,
  replace h := h y y_mem_support,
  simp_rw mv_polynomial.bind₁_monomial,
  simp only [pi.mul_apply],
  simp_rw mul_pow,
  rw finset.prod_mul_distrib,
  simp_rw <-mul_assoc,
  congr' 1,
  rw mul_comm,
  congr' 1,
  rw <- h,
  rw finset.prod_pow_eq_pow_sum,
  congr' 1,
  -- ring_nf,
end


-- end

lemma mv_polynomial.mul_X_eq_zero {σ R : Type*} [comm_semiring R] (s : σ) (p : mv_polynomial σ R)(h : ((mv_polynomial.X s)) * p = 0) : p = 0 := 
begin
  rw mv_polynomial.ext_iff at h ⊢,
  intros m,
  replace h := h (m + finsupp.single s 1),
  simp at h,
  rw mul_comm at h,
  rw mv_polynomial.coeff_mul_X at h, -- generalize to X_pow
  simp [h],
end


-- todo mathlib
lemma mv_polynomial.mul_X_pow_eq_zero {σ R : Type*} [comm_semiring R] {s : σ} (d : ℕ) (p : mv_polynomial σ R)(h : ((mv_polynomial.X s) ^ d) * p = 0) : p = 0 := 
begin
  induction d,
  simp at h,
  exact h,
  apply d_ih,
  rw pow_succ at h,
  apply mv_polynomial.mul_X_eq_zero s,
  rw <-mul_assoc,
  exact h,
  
end

/-- Given a particular toxic waste sample, we can multiply this sample through all crs elems without affecting the soundness of the SNARK. This assumes that all checks have uniform degree as polynomials over the proof elements, (indeed for bilinear pairings, these polynomials will have degree 2) -/
noncomputable def change_exponent (𝓟 : AGM_proof_system F n_stmt n_wit) 
  (sample : fin 𝓟.n_sample) (d : ℕ) 
  (all_checks_uniform_degree : ∀ c ∈ 𝓟.polynomial_checks, uniform_degree c d) : AGM_proof_system F n_stmt n_wit :=
{ relation := 𝓟.relation,
  n_sample := 𝓟.n_sample,
  n_crs := 𝓟.n_crs,
  crs_elems := (λ i, mv_polynomial.X sample) * (𝓟.crs_elems),  
  proof_elems_index := 𝓟.proof_elems_index,
  -- proof_crs_component := 𝓟.proof_crs_component,
  polynomial_checks := 𝓟.polynomial_checks,
  proof_element_checks := 𝓟.proof_element_checks,
  extractor := 𝓟.extractor,
  soundness :=
  begin
  -- sorry,
    rintros stmt agm ⟨poly_checks_pass', proof_elem_checks_pass'⟩,
    apply 𝓟.soundness,
    split,
    {
      intros c in_checks, -- f, -- f_never_zero,

      replace poly_checks_pass' := poly_checks_pass' c in_checks,
      simp at *,
      have : ⇑(mv_polynomial.bind₁ (λ (pf_idx : 𝓟.proof_elems_index), ∑ (x : fin 𝓟.n_crs), agm pf_idx x • (mv_polynomial.X sample * 𝓟.crs_elems x))) c
      = 
      ((mv_polynomial.X sample) ^ d) * (⇑(mv_polynomial.bind₁ (λ (pf_idx : 𝓟.proof_elems_index), ∑ (x : fin 𝓟.n_crs), agm pf_idx x • (𝓟.crs_elems x))) c),
      {
        have funeq : (λ (pf_idx : 𝓟.proof_elems_index), ∑ (x : fin 𝓟.n_crs), agm pf_idx x • (mv_polynomial.X sample * 𝓟.crs_elems x))
        =
        (λ (pf_idx : 𝓟.proof_elems_index), ∑ (x : fin 𝓟.n_crs), mv_polynomial.X sample * agm pf_idx x • (𝓟.crs_elems x)),
        {
          funext,
          congr,
          funext,
          simp_rw mv_polynomial.smul_eq_C_mul,
          ring,
          -- library_search, 
        },
        simp_rw funeq,
        simp_rw <-finset.mul_sum,
        apply uniform_degree_implies_bind₁_uniformity,
        apply all_checks_uniform_degree,
        apply in_checks,
        -- sorry,
      },
      rw this at poly_checks_pass',
      have foo := mv_polynomial.mul_X_pow_eq_zero _ _ poly_checks_pass',
      exact foo,
      -- rw mv_polynomial.eval
      -- exact poly_checks_pass',
      -- unfold function.comp at checks_give_zero ⊢,
      -- simp at *,
      -- simp_rw mv_polynomial.smul_eq_C_mul at *,
    },
    {
      intros idx val val_in,
      replace proof_elem_checks_pass' :=  proof_elem_checks_pass' idx val val_in,
      exact proof_elem_checks_pass',
    },
  end 
}

lemma sum_conditional {S R : Type} [fintype S] [comm_ring R] (f : S -> R) (p : S -> Prop) [decidable_pred p] : 
  ∑ (s : S), f s = (∑ (s : S), ite (p s) (f s) 0) + (∑ (s : S), ite (p s) 0 (f s)) :=
begin
  rw ←finset.sum_add_distrib,
  congr,
  funext,
  by_cases hp : p s,
  simp [hp],
  simp [hp],
end

lemma ite_or_eq_sum {S R : Type} [fintype S] [comm_ring R] {s a b : S} (h : a ≠ b) [decidable_eq S] (f : S -> R)  : ite (s = a ∨ s = b) (f s) 0 = (ite (s = a) (f a) 0) + (ite (s = b) (f b) 0) :=
begin
  by_cases ha : s = a,
  { by_cases hb : s = b,
    simp [h, ha, hb],  
    exfalso,
    rw [<-ha, <-hb] at h,
    apply h,
    refl,
    simp [h, ha, hb],  

    },
  { by_cases hb : s = b,
    simp [h, ha, hb],  
    simp [h, ha, hb],  
    },
  
end

lemma sum_or_two_eq {S R : Type} [fintype S] [comm_ring R] {a b : S} (h : a ≠ b) [decidable_eq S] (f : S -> R)  : 
  ∑ (s : S), ite (s = a ∨ s = b) (f s) 0 = f a + f b :=
begin
  simp_rw [ite_or_eq_sum h], -- doesn't work without the h, why?
  rw finset.sum_add_distrib,
  congr,
  simp,
  simp,
end

example {S R : Type} [fintype S] [comm_ring R] (f : S -> R) (a : S) (p : Prop) [decidable p] : ite p a a = a := 
begin
  exact if_t_t p a
end


@[simp] lemma or_and_self_left (p q : Prop) : ((p ∨ q) ∧ q) ↔ q := by tauto
@[simp] lemma or_and_self_right (p q : Prop) : ((p ∨ q) ∧ p) ↔ p := by tauto
@[simp] lemma foobar1 (α : Type) (a b c : α) (h : b ≠ c) : ((a = b ∨ a = c) ∧ ¬ a = c) ↔ a = b := 
begin
  tidy,
end
@[simp] lemma foobar2 (α : Type) (a b c : α) (h : b ≠ c) : ((a = b ∨ a = c) ∧ ¬ a = b ∧ ¬ a = c) ↔ false := 
begin
  tidy,
end

-- example {A : Type} (a b : A) : a = b ↔ b = a := by {exact eq_comm}

/-- Adds one crs element to another and zeros out the added element. This might be useful in the case where in the given SNARK, this pair of CRS elements are always used with the same coefficient, in which case the resulting SNARK is complete. -/
noncomputable def collapse_crs_element (𝓟 : AGM_proof_system F n_stmt n_wit) 
  (twin1 twin2 : fin 𝓟.n_crs) (not_same : twin1 ≠ twin2) 
  (interchangeable : 
    ∀ (stmt : fin n_stmt -> F) (val : (fin n_stmt → F) → fin 𝓟.n_crs → F) (idx : 𝓟.proof_elems_index)
        (val_in : val ∈ 𝓟.proof_element_checks idx) (agm : 𝓟.proof_elems_index → fin 𝓟.n_crs → F), val stmt = agm idx -> agm idx twin1 = agm idx twin2 ): 
  AGM_proof_system F n_stmt n_wit :=
{ relation := 𝓟.relation,
  n_sample := 𝓟.n_sample,
  n_crs := 𝓟.n_crs,
  crs_elems := λ crs, 
    if crs = twin1 
      then 𝓟.crs_elems twin1 + 𝓟.crs_elems twin2 
    else if crs = twin2 
      then 0
    else 𝓟.crs_elems crs,  
  proof_elems_index := 𝓟.proof_elems_index,
  polynomial_checks := 𝓟.polynomial_checks,
  proof_element_checks := 𝓟.proof_element_checks,
    -- λ idx, 
    --   (𝓟.proof_element_checks idx).map 
    --   (λ old stmt crs, (if crs = twin2 then old stmt twin1 else old stmt crs)) ,
  -- When the extractor goes to read the component of the second twin, it should instead read the first
  extractor := λ agm wit, 𝓟.extractor (λ proof_elem crs, agm proof_elem (if crs = twin2 then twin1 else crs)) wit,
  soundness :=
  begin
  -- sorry,
    rintros stmt agm ⟨poly_checks_pass', proof_elem_checks_pass'⟩,
    apply 𝓟.soundness,
    split,
    {
      intros c in_checks, -- f, -- f_never_zero,

      replace poly_checks_pass' := poly_checks_pass' c in_checks,
      -- simp at *,
      rw <-poly_checks_pass',
      apply congr, apply congr, refl, apply congr, refl, 
      funext,
      simp_rw [mv_polynomial.smul_eq_C_mul],
      simp_rw [apply_ite (agm pf_idx)],
      simp_rw [apply_ite (mv_polynomial.C)],
      simp_rw ite_mul,
      simp_rw mul_ite,
      -- simp_rw [if_t_t p a],
      rw sum_conditional _ (λ x, x = twin1 ∨ x = twin2),
      nth_rewrite 2 sum_conditional _ (λ x, x = twin1 ∨ x = twin2),
      congr' 1,
      { simp_rw [sum_or_two_eq not_same],
        simp,
        simp_rw [@eq_comm _ twin2 twin1],
        simp [not_same],
        ring,
      },
      {
        congr' 1,
        funext s,
        simp,
        -- simp_rw finset.sum_ite_eq',
        -- simp only [finset.mem_univ, if_true],
        simp_rw ←ite_and,
        split_ifs,
        refl,
        contrapose! not_same, 
        rw [<-h_1, <-h_2],
        contrapose! h, right, assumption, 
        contrapose! h, left, assumption, 
        refl,
        -- tidy,
      },
      refl,
    },
    {
      -- sorry,
      intros idx val val_in, -- need to pass in a different val
      replace proof_elem_checks_pass' :=  proof_elem_checks_pass' idx val val_in,
      rw proof_elem_checks_pass',
      funext,
      split_ifs,
      rotate,
      refl,
      rw [h],
      replace interchangeable := interchangeable stmt val idx val_in agm proof_elem_checks_pass',
      rw [interchangeable],
    },
  end 
}


noncomputable def zero_and_carry {A : Type} (x : A →₀ ℕ) (source target : A) (factor : ℕ) : A →₀ ℕ :=
  x.erase source + finsupp.single target (factor * x source)

lemma commutable_zero_and_carry {F proof_elems_index: Type} [field F] (n_sample n_crs : ℕ)    
    (d d2 : ℕ)
    (sample_removed sample_target : fin n_sample) 
    (multinomial: fin n_sample →₀ ℕ)
    (crs_elems : (fin n_crs) → (mv_polynomial (fin n_sample) F))
    (agm: proof_elems_index → fin n_crs → F) (c : mv_polynomial proof_elems_index F)
    (h : ∀ (crs_idx : fin n_crs), mv_polynomial.degree_of sample_target (crs_elems crs_idx) < d) 
    (uniform_deg : uniform_degree c d2) : 
  mv_polynomial.coeff multinomial ((mv_polynomial.aeval (λ (pf_idx : proof_elems_index), ∑ (crs_idx : fin n_crs), agm pf_idx crs_idx • crs_elems crs_idx)) c) 
  = 
  mv_polynomial.coeff (zero_and_carry multinomial sample_removed sample_target (d * d2)) ((mv_polynomial.aeval (λ (pf_idx : proof_elems_index), ∑ (x : fin n_crs), agm pf_idx x • mv_polynomial.eval₂ mv_polynomial.C (λ (x : fin n_sample), ite (x = sample_removed) (mv_polynomial.X sample_target ^ d) (mv_polynomial.X x)) (crs_elems x))) c) := 
begin
  sorry
end

-- Returns a SNARK where one fewer toxic waste element is actually used, replaced by sample_target ^ d
noncomputable def collapse_toxic_waste (𝓟 : AGM_proof_system F n_stmt n_wit) (d d2 : ℕ) 
  (sample_removed sample_target : fin 𝓟.n_sample) 
  (h : ∀ (crs_idx : fin 𝓟.n_crs), mv_polynomial.degree_of sample_target (𝓟.crs_elems crs_idx) < d) 
  -- (all polychecks are of uniform degree d2)
  (uniform_deg : ∀ p ∈ 𝓟.polynomial_checks, uniform_degree p d2)
  : 
  AGM_proof_system F n_stmt n_wit :=
{ relation := 𝓟.relation,
  n_sample := 𝓟.n_sample,
  n_crs := 𝓟.n_crs,
  crs_elems := (mv_polynomial.eval₂ (mv_polynomial.C) 
    (λ x, if x = sample_removed then ((mv_polynomial.X sample_target) ^ (d))
      else mv_polynomial.X x)) ∘ 𝓟.crs_elems,  
  proof_elems_index := 𝓟.proof_elems_index,
  -- proof_crs_component := 𝓟.proof_crs_component,
  polynomial_checks := 𝓟.polynomial_checks,
  proof_element_checks := 𝓟.proof_element_checks,
  extractor := 𝓟.extractor,
  soundness :=
  begin
    rintros stmt agm ⟨poly_checks_pass', proof_elem_checks_pass'⟩,
    apply 𝓟.soundness,
    split,
    {
      intros c in_checks, 

      replace poly_checks_pass' := poly_checks_pass' c in_checks, -- f f_never_zero,
      simp at *,
      have all_coeffs_of_new_snark_zero : 
        ∀ multinomial : fin 𝓟.n_sample →₀ ℕ, 
          (⇑(mv_polynomial.bind₁ (λ (pf_idx : 𝓟.proof_elems_index), ∑ (x : fin 𝓟.n_crs), agm pf_idx x • mv_polynomial.eval₂ mv_polynomial.C (λ (x : fin 𝓟.n_sample), ite (x = sample_removed) (mv_polynomial.X sample_target ^ d) (mv_polynomial.X x)) (𝓟.crs_elems x))) c).coeff multinomial = 0,
      exact mv_polynomial.eq_zero_iff.mp poly_checks_pass', -- follows from extensionality on the polynomial
      have all_coeffs_of_old_snark_are_a_coeff_of_the_new : -- in particular, the coeff of a multinomial is what you get from zeroing out the sample_removed and multiplying this value by d * d2 and adding to sample target
        ∀ multinomial : fin 𝓟.n_sample →₀ ℕ,
          (⇑(mv_polynomial.bind₁ (λ (pf_idx : 𝓟.proof_elems_index), ∑ (crs_idx : fin 𝓟.n_crs), agm pf_idx crs_idx • 𝓟.crs_elems crs_idx)) c).coeff multinomial
            =
          (⇑(mv_polynomial.bind₁ (λ (pf_idx : 𝓟.proof_elems_index), ∑ (x : fin 𝓟.n_crs), agm pf_idx x • mv_polynomial.eval₂ mv_polynomial.C (λ (x : fin 𝓟.n_sample), ite (x = sample_removed) (mv_polynomial.X sample_target ^ d) (mv_polynomial.X x)) (𝓟.crs_elems x))) c).coeff (zero_and_carry multinomial sample_removed sample_target (d * d2)),
      {
        intro,
        clear all_coeffs_of_new_snark_zero,
        simp_rw [mv_polynomial.bind₁],
        apply commutable_zero_and_carry,
        apply h,
        apply uniform_deg,
        exact in_checks,
      },

      rw mv_polynomial.eq_zero_iff,
      intro d,
      rw all_coeffs_of_old_snark_are_a_coeff_of_the_new d,
      rw all_coeffs_of_new_snark_zero,


      -- thus all coeffs for old snark zero
      -- thus sound


    },
    {
      intros idx val val_in,
      replace proof_elem_checks_pass' :=  proof_elem_checks_pass' idx val val_in,
      exact proof_elem_checks_pass',
    },
  end 
}

end