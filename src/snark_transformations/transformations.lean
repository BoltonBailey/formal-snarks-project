
import .proof_system_fin

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
  sorry,
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


-- Returns a SNARK where one fewer toxic waste element is actually used, replaced by sample_target ^ d
noncomputable def collapse_toxic_waste (𝓟 : AGM_proof_system F n_stmt n_wit) (d : ℕ) (sample_removed sample_target : fin 𝓟.n_sample) 
  (h : ∀ (crs_idx : fin 𝓟.n_crs), mv_polynomial.degree_of sample_target (𝓟.crs_elems crs_idx) < d) : 
  AGM_proof_system F n_stmt n_wit :=
{ relation := 𝓟.relation,
  n_sample := 𝓟.n_sample,
  n_crs := 𝓟.n_crs,
  crs_elems := (mv_polynomial.eval₂ (mv_polynomial.C) (λ x, ((mv_polynomial.X 0) ^ (single_variable_degrees x)))) ∘ 𝓟.crs_elems,  
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
      simp_rw <-mul_assoc at poly_checks_pass',
      simp_rw [mul_comm _ (f sample)]  at poly_checks_pass',
      simp_rw mul_assoc at poly_checks_pass',
      simp_rw <-finset.mul_sum at poly_checks_pass',
      -- unfold mv_polynomial.eval at poly_checks_pass',
      -- rw mv_polynomial.eval_mul at poly_checks_pass',
      have : 
        (λ (pf_idx : 𝓟.proof_elems_index), f sample * ∑ (x : fin 𝓟.n_crs), agm pf_idx x * (mv_polynomial.eval f) (𝓟.crs_elems x))
        = 
        ((λ x : 𝓟.proof_elems_index, (f sample))) 
        * 
        λ (pf_idx : 𝓟.proof_elems_index),
        ∑ (x : fin 𝓟.n_crs), agm pf_idx x * (mv_polynomial.eval f) (𝓟.crs_elems x)
        ,
      {
        ext,
        refl,
      },
      rw this at poly_checks_pass',

      rw all_checks_uniform_degree c  at poly_checks_pass',

      -- rw mv_polynomial.eval_mul _ _ (f sample) at poly_checks_pass',
      rw mul_eq_zero at poly_checks_pass',
      cases poly_checks_pass',
      {
        exfalso,
        apply f_never_zero sample,
        exact pow_eq_zero poly_checks_pass',
      },
      {
        exact poly_checks_pass',
      },
      exact in_checks,
      
      
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

-- noncomputable def mv_polynomial.map_varset {σ τ : Type*} (f : σ → τ) {R : Type*} [comm_semiring R] : 
--   mv_polynomial σ R →+* mv_polynomial τ R := mv_polynomial.eval₂_hom (mv_polynomial.C) (mv_polynomial.X ∘ f)

@[simp] lemma mv_polynomial.eval_map_varset {σ τ : Type*} (f : σ → τ) {R : Type*} [comm_semiring R] (g : τ -> R) (p : mv_polynomial σ R) : mv_polynomial.eval g (mv_polynomial.rename f p) = mv_polynomial.eval (g ∘ f) p :=
begin
  unfold mv_polynomial.eval,
  simp only [mv_polynomial.coe_eval₂_hom],
  rw mv_polynomial.eval₂_rename,

end
 

-- lemma mynat.div_lt_of_lt_mul (a b c : ℕ) (h : c < a * b) : c / a < b := 
-- begin
-- apply nat.div_lt_of_lt_mul,
--   cases a,
--   linarith,
--   have : 0 < a.succ, exact nat.succ_pos a,
--   rw <-mul_lt_mul_left this,
--   apply lt_of_le_of_lt _ h,
--   exact nat.mul_div_le c (nat.succ a),
--   -- linarith,
-- end

-- maps an element of a fin of a sum of naturals, to an index into the sum, and an index into the value
def fin_mul_to_fin_fin_1 (a : ℕ) (b : ℕ) (i : fin (a * b)) : fin a := 
fin.mk ((i : ℕ) / b) 
  (by { 
    have : (i : ℕ) < a * b, exact fin.is_lt i,  
    apply nat.div_lt_of_lt_mul,
    simp_rw nat.mul_comm,
    exact this,
    })


lemma pos_of_fin_inhabited (a : ℕ) ( i : fin a) : 0 < a := 
begin
  rcases i,
  apply lt_of_le_of_lt _ i_property,
  exact zero_le i_val,
end

def fin_mul_to_fin_fin_2 (a : ℕ) (b : ℕ) (i : fin (a * b)) : fin b := 
fin.mk ((i : ℕ) % b) 
  (by { 
    apply nat.mod_lt,
    have : 0 < a * b, exact pos_of_fin_inhabited _ i,
    contrapose! this,
    simp at this ⊢,
    right,
    exact this,
    })

def fin_fin_to_mul_fin (a : ℕ) (b : ℕ) (ai : fin a) (bi : fin b) : fin (a * b) := 
fin.mk (b * ai + bi) 
  (by { 
    rcases ai,
    rcases bi,
    simp only [fin.coe_mk],
    sorry,
    })

@[simp] lemma fin_mul_to_fin_fin_1_fin_fin_to_mul_fin (a : ℕ) (b : ℕ) (ai : fin a) (bi : fin b) :
  fin_mul_to_fin_fin_1 a b (fin_fin_to_mul_fin a b ai bi) = ai := sorry

@[simp] lemma fin_mul_to_fin_fin_2_fin_fin_to_mul_fin (a : ℕ) (b : ℕ) (ai : fin a) (bi : fin (b)) :
  fin_mul_to_fin_fin_2 a b (fin_fin_to_mul_fin a b ai bi) = bi := sorry

lemma sum_of_fin_mul {S : Type*} [add_comm_monoid S] 
  (a : ℕ) (b : ℕ) (f : fin (a * b) -> S) : 
  ∑ i : fin (a * b), f i 
  = ∑ (ai : fin a), (∑ bi : fin (b), f (fin_fin_to_mul_fin a b ai bi))
:= sorry

def fin_add_of_fin_fin {S : Type*} {a b : ℕ} (f : fin a -> S ) (g : fin b -> S ) (x : fin (a + b)) :
S := sorry

@[simp] lemma fin_add_of_fin_fin_nat_add  {S : Type*} {a b : ℕ} (f : fin a -> S ) (g : fin b -> S ) (i : fin b) : 
  fin_add_of_fin_fin f g (fin.nat_add a i) = g i := sorry

@[simp] lemma fin_add_of_fin_fin_cast_add  {S : Type*} {a b : ℕ} (f : fin a -> S ) (g : fin b -> S ) (i : fin a) : 
  fin_add_of_fin_fin f g (fin.cast_add b i) = f i := sorry

@[simp] lemma fin_add_of_fin_fin_comp_cast_add  {S : Type*} {a b : ℕ} (f : fin a -> S ) (g : fin b -> S ) : 
  (fin_add_of_fin_fin f g) ∘ (fin.cast_add b) = f := sorry

example  {S : Type*} [add_comm_monoid S]  {a : ℕ} (f : fin a -> S ) : 
  (∑ i : fin a, (f i)) = ∑ i : fin a, f (fin_rotate a i) :=
begin
  refine (equiv.sum_comp (fin_rotate a) f).symm,
end

lemma rotate_cancel (crs_splits pncrs pnsample : ℕ) : ∀ x : fin pncrs, 
            ∑ (x_1 : fin crs_splits),
                @mv_polynomial.X F _ _ 
                  ((fin.nat_add pnsample) (fin_fin_to_mul_fin pncrs crs_splits x ((fin_rotate crs_splits) x_1)))
            =
            ∑ (x_1 : fin crs_splits),
                mv_polynomial.X
                  ((fin.nat_add pnsample) (fin_fin_to_mul_fin pncrs crs_splits x x_1)) 
                   :=
begin
  -- apply equiv.sum_comp,
  sorry,
end

lemma rename_zero {σ τ : Type} (f : σ -> τ) : @mv_polynomial.rename σ τ F _ f 0 = 0 := 
begin
  simp only [alg_hom.map_zero],
end

lemma rename_bind₁ {σ τ υ : Type} (f : τ → υ) (g : σ -> mv_polynomial τ F) (p : mv_polynomial σ F): 
  mv_polynomial.rename f (mv_polynomial.bind₁ g p) = 
  mv_polynomial.bind₁ ((mv_polynomial.rename f) ∘ g) p :=
begin
  sorry,
end

-- Given a decomposition of each crs element into a collection of polynomials that sum to it
-- we can construct a new proof system splitting those terms up
-- Here, we assume all crs elements are decomposed into the same number of elements, but this need not be the case in principle.
noncomputable def split_crs (𝓟 : AGM_proof_system F n_stmt n_wit) 
  -- For each old crs element, a number of splits for it
  (crs_splits : ℕ)
  -- For each split, a polynomial over the old sample elements
  (split : 
    Π crs_idx : fin 𝓟.n_crs, 
      (fin (crs_splits) -> mv_polynomial (fin 𝓟.n_sample) F) ) 
  -- The sum of polynomials over a split must equal the old crs polynomial.
  (sum_split : 
    Π crs_idx : fin 𝓟.n_crs, 
      ∑ split_idx : fin (crs_splits), split crs_idx split_idx = 𝓟.crs_elems crs_idx)
  -- A default element for each split
  (default :
    Π crs_idx : fin 𝓟.n_crs, fin (crs_splits)
  )
      : AGM_proof_system F n_stmt n_wit :=
{ relation := 𝓟.relation,
  n_sample := 𝓟.n_sample + 𝓟.n_crs * crs_splits,
  n_crs := 𝓟.n_crs * crs_splits,
  crs_elems := λ idx, 
    let old_crs_index : fin 𝓟.n_crs := fin_mul_to_fin_fin_1 𝓟.n_crs crs_splits idx in 
    let split_index : fin (crs_splits) := fin_mul_to_fin_fin_2 𝓟.n_crs crs_splits idx in 
      (mv_polynomial.rename (fin.cast_add _) (split old_crs_index split_index))
      + mv_polynomial.X (fin.nat_add 𝓟.n_sample (idx))
      - mv_polynomial.X (fin.nat_add 𝓟.n_sample (fin_fin_to_mul_fin 𝓟.n_crs crs_splits old_crs_index ((fin_rotate _) split_index)))
      ,
  proof_elems_index := 𝓟.proof_elems_index,
  polynomial_checks := 𝓟.polynomial_checks,
  proof_element_checks := λ proof_elem_idx, 
    option.map 
      (begin
        intros old_map stmt idx,
        exact old_map stmt (fin_mul_to_fin_fin_1 𝓟.n_crs crs_splits idx),
      end ) 
      (𝓟.proof_element_checks proof_elem_idx),
  -- old_map stmt (fin_sum_to_fin_fin_1 𝓟.n_crs crs_splits idx)
  extractor := begin
    intro thing,
    apply 𝓟.extractor,
    intros proof_elems_idx old_crs_idx,
    apply thing proof_elems_idx,
    exact fin_fin_to_mul_fin 𝓟.n_crs crs_splits old_crs_idx (default old_crs_idx),
  end,
  soundness := begin
    rintros stmt agm ⟨poly_checks_pass', proof_elem_checks_pass'⟩,
    apply 𝓟.soundness,

    split,
    { 
      intros c in_checks,

      -- TODO: restructure defalut so that it equals 0?

      

      have same : ∀ (pr : 𝓟.proof_elems_index) (ai : fin 𝓟.n_crs) (bi : fin crs_splits), agm pr (fin_fin_to_mul_fin _ _ ai bi) = agm pr (fin_fin_to_mul_fin _ _ ai (default ai)),
      {
        clear proof_elem_checks_pass',
        sorry
      },
      -- done,
      replace poly_checks_pass' := poly_checks_pass' c in_checks,



      simp only [mv_polynomial.eval_X, and_imp, ring_hom.map_sub, algebra.id.smul_eq_mul, ring_hom.map_add, ne.def,
  mv_polynomial.eval_map_varset, option.mem_def, exists_imp_distrib, option.map_eq_some'] at *,
      simp_rw [add_sub_assoc] at poly_checks_pass',
      simp_rw [mv_polynomial.smul_eq_C_mul] at poly_checks_pass',
      simp_rw [mul_add] at poly_checks_pass',
      simp_rw [finset.sum_add_distrib] at poly_checks_pass',
      simp_rw [sum_of_fin_mul] at poly_checks_pass',
      simp at poly_checks_pass',
      simp_rw [same] at poly_checks_pass',
      simp_rw [←finset.mul_sum] at poly_checks_pass',
      simp_rw [finset.sum_sub_distrib] at poly_checks_pass', -- alias this lemma
      -- have rotate_cancel : ∀ x : fin 𝓟.n_crs, 
      --       ∑ (x_1 : fin crs_splits),
      --           mv_polynomial.X
      --             ((fin.nat_add 𝓟.n_sample) (fin_fin_to_mul_fin 𝓟.n_crs crs_splits x ((fin_rotate crs_splits) x_1)))
      --       -
      --       ∑ (x_1 : fin crs_splits),
      --           mv_polynomial.X
      --             ((fin.nat_add 𝓟.n_sample) (fin_fin_to_mul_fin 𝓟.n_crs crs_splits x x_1)) = 0,
      -- {
      --   sorry,
      -- },


      simp_rw [rotate_cancel] at poly_checks_pass',
      simp only [add_zero, finset.sum_const_zero, mul_zero, sub_self] at poly_checks_pass',
      simp_rw [mv_polynomial.smul_eq_C_mul],    


      have foobar : 
          (mv_polynomial.bind₁ 
            (λ (pf_idx : 𝓟.proof_elems_index), 
              ∑ (x : fin 𝓟.n_crs), mv_polynomial.C (agm pf_idx (fin_fin_to_mul_fin 𝓟.n_crs crs_splits x (default x))) 
                * ∑ (x_1 : fin crs_splits), (mv_polynomial.rename (fin.cast_add (𝓟.n_crs * crs_splits))) (split x x_1))) c
          = 
          (mv_polynomial.rename (fin.cast_add (𝓟.n_crs * crs_splits))) ((mv_polynomial.bind₁ 
            (λ (pf_idx : 𝓟.proof_elems_index), 
              ∑ (x : fin 𝓟.n_crs), mv_polynomial.C (agm pf_idx (fin_fin_to_mul_fin 𝓟.n_crs crs_splits x (default x))) 
                * ∑ (x_1 : fin crs_splits), (split x x_1))) c),
      {
        simp_rw rename_bind₁,
        -- congr' 1,
        sorry,
      },
      simp_rw foobar at poly_checks_pass',

      simp_rw sum_split at poly_checks_pass',

      have zero_eq_rename : 0 = mv_polynomial.rename (fin.cast_add (𝓟.n_crs * crs_splits)) 0, 
      {
        symmetry,
        rw rename_zero,
      },

      rw zero_eq_rename at poly_checks_pass',

      convert mv_polynomial.rename_injective (fin.cast_add (𝓟.n_crs * crs_splits)) _ poly_checks_pass',

      exact rel_embedding.injective (fin.cast_add (𝓟.n_crs * crs_splits)),


      done,

      
    },
    {
      sorry,
    },
    
  end }

-- -- Given a decomposition of each crs element into a collection of polynomials that sum to it
-- -- we can construct a new proof system splitting those terms up
-- def split_crs (𝓟 : AGM_proof_system) 

--   (crs_numbering : 
--    fin (new_n_crs) ->
--     (Σ crs_idx : fin 𝓟.n_crs, 
--       (fin (𝓟.crs_elems crs_idx).support.card) ) )
--   (crs_numbering_inj : function.bijective crs_numbering)
--   (monomial_numbering : 
--     Π crs_idx : fin 𝓟.n_crs, 
--       (fin (𝓟.crs_elems crs_idx).support.card  -> (𝓟.crs_elems crs_idx).support) ) 
--   (monomial_numbering_bijective : 
--     ∀ crs_idx : fin 𝓟.n_crs, 
--       function.bijective (monomial_numbering crs_idx)  ) 
--       : AGM_proof_system :=
-- { relation := 𝓟.relation,
--   n_sample := 𝓟.n_sample + new_n_crs,
--   n_crs := new_n_crs,
--   crs_elems := λ idx,
--   begin
--     rcases crs_numbering idx with ⟨old_crs, old_crs_number⟩,
--     clear crs_numbering_inj crs_numbering,
--     replace monomial_numbering_bijective := monomial_numbering_bijective old_crs,
--     clear monomial_numbering_bijective,
--     replace monomial_numbering := monomial_numbering old_crs,
--     exact (monomial_numbering old_crs_number + mv_polynomial.X (old_crs_number + 𝓟.n_sample) - mv_polynomial.X (old_crs_number.rotate + 𝓟.n_sample))
--     -- + oldcrs number (with additional shift for generic samples) - old_crs number rotate (with additional shift for generic samples) + monomial 
--   end,
--   proof_elems_index := 𝓟.proof_elems_index,
--   polynomial_checks := _,
--   proof_element_checks := _,
--   extractor := _,
--   soundness := _ }


-- { -- The relation the flattened SNARK checks is the same
--   relation := 𝓟.relation,
--   -- We have an additional sample for each support monomial of each crs element polynomial
--   sample_space := 𝓟.sample_space ⊕ (Σ (crs_idx : 𝓟.crs_elems_index), fin ((𝓟.crs_elems crs_idx).support.card + 1)),
--   fin_sample_space := begin
--     apply @sum.fintype _ _ (𝓟.fin_sample_space) _,
--     apply @sigma.fintype _ _ _ _,
--     classical,
--     -- exact classical.dec_eq 𝓟.crs_elems_index,
--     exact 𝓟.fin_crs,
--     intro a,
--     apply fin.fintype,
--   end,
--   -- The CRS elements become polynomials with one monomial from the original polynomial
--   -- an additional sample added, and an additional sample subtracted.
--   crs_elems_index := (Σ (crs_idx : 𝓟.crs_elems_index), fin ((𝓟.crs_elems crs_idx).support.card + 1)),
--   fin_crs := begin
--     apply @sigma.fintype _ _ _ _,
--     classical,
--     -- exact classical.dec_eq 𝓟.crs_elems_index,
--     exact 𝓟.fin_crs,
--     intro a,
--     apply fin.fintype,
--   end,
--   crs_elems := λ ⟨c1, c2⟩, if c2 = 0 then (tau00)_ else (tau0c2) zmod
--   ,
--   proof_elems_index := 𝓟.proof_elems_index,
--   proof_crs_component := _,
--   checks := _,
--   extractor := _,
--   soundness := _ }


end