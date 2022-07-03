
import algebra.field
import algebra.polynomial.big_operators -- correct import?
import data.mv_polynomial.comm_ring
import data.equiv.fin -- name changed to logic equiv fin
import data.mv_polynomial.rename

open_locale big_operators

section

/-!

This file contains classes for noninteractive proof systems.

-/

universe u
/-- The finite field parameter of our SNARK -/
parameter {F : Type u}
parameter [field F]

-- The types of the statement and witness are assumed to be collections of n_stmt and n_wit field elements respectively.
-- parameters {n_sample n_crs n_stmt n_wit n_proof : ℕ}
parameters {n_stmt n_wit : ℕ}

def STMT := fin n_stmt -> F
def WIT := fin n_wit -> F
-- def SAMPLE := fin n_sample -> F
-- def CRS := fin n_crs -> F
-- def PROOF := fin n_proof -> F
-- def PROOF_MODEL := fin n_crs -> fin n_proof -> ℕ





structure AGM_proof_system' :=
  (relation : STMT → WIT → Prop)
  (sample_space : Type) -- a type of symbols to represent toxic waste elems
  [fin_sample_space : fintype sample_space]
  (crs_elems_index : Type) -- a type of indices for crs elems
  [fin_crs : fintype crs_elems_index]
  (crs_elems : crs_elems_index → (mv_polynomial sample_space F)) -- the value of each crs elem as a polynomial of toxic waste elems
  (proof_elems_index : Type) -- an index into proof elems
  -- the coefficient of a particular crs elem in a particular proof elem for an honest prover (Not needed in soundness def)
  -- (proof_crs_component : STMT → WIT → proof_elems_index → crs_elems_index → F) 
  -- (permissible_inclusion : proof_elems_index → crs_elems_index → bool) -- whether it is possible for a malicious prover to include a particular crs elem in a particular proof elem - used to represent distinction between G1 and G2
  (checks : list (STMT → mv_polynomial crs_elems_index (mv_polynomial proof_elems_index F))) -- mv_polynomials of proof elems that the verifier checks to be zero
  (extractor : (proof_elems_index → crs_elems_index → F) → WIT)
  -- given an agm which makes a valid proof, the extractor must give a correct witness
  (soundness : 
    ∀ stmt : STMT, 
      ∀ agm : proof_elems_index → crs_elems_index → F,
        -- if all checks on the proof pass, the extracted witness must satisfy the relation
        (∀ c ∈ checks, 
          (∀ f : sample_space → F, 
          -- TODO need nonzeroness on f
            mv_polynomial.eval 
              ((mv_polynomial.eval f) ∘ (λ pi, ∑ i : crs_elems_index, agm pi i • crs_elems i)) (mv_polynomial.eval (mv_polynomial.C ∘ (mv_polynomial.eval f) ∘ crs_elems) (c stmt)) 
            = 0
            ))
          → relation stmt (extractor agm)) -- crs_elems proof check_polynomial

structure AGM_proof_system'' :=
  (relation : STMT → WIT → Prop)
  (sample_space : Type) -- a type of symbols to represent toxic waste elems
  [fin_sample_space : fintype sample_space]
  (crs_elems_index : Type) -- a type of indices for crs elems
  [fin_crs : fintype crs_elems_index]
  (crs_elems : crs_elems_index → (mv_polynomial sample_space F)) -- the value of each crs elem as a polynomial of toxic waste elems
  -- an index into proof elems
  -- To avoid nested indexing, we assume that the prover provides the values of any elements in the checks that the verifier would compute. In this formalism, the verifier makes two kinds of checks - checks that the polynomial evaluates to 0, and checks that the verifier proof elements are consistent with the statement.
  (proof_elems_index : Type) 
  -- the coefficient of a particular crs elem in a particular proof elem for an honest prover (Not needed in soundness def)
  -- (proof_crs_component : STMT → WIT → proof_elems_index → crs_elems_index → F) 
  -- (permissible_inclusion : proof_elems_index → crs_elems_index → bool) -- whether it is possible for a malicious prover to include a particular crs elem in a particular proof elem - used to represent distinction between G1 and G2
  -- mv_polynomials of proof elems that the verifier checks to be zero
  (polynomial_checks : list (mv_polynomial proof_elems_index F)) 
  -- proof elements constructed from the statement that the verifier checks the construction of
  (proof_element_checks : proof_elems_index → option (STMT → crs_elems_index → F))
  -- Extracts the witness from an AGM
  (extractor : (proof_elems_index → crs_elems_index → F) → WIT)
  -- given an agm which makes a valid proof, the extractor must give a correct witness
  (soundness : 
    ∀ stmt : STMT, 
      ∀ agm : proof_elems_index → crs_elems_index → F,
        -- if all checks on the proof pass, the extracted witness must satisfy the relation
        (
          (∀ c ∈ polynomial_checks, 
          (∀ f : sample_space → F, 
          -- TODO need nonzeroness on f
          (mv_polynomial.eval (λ pf_idx, ∑ crs_idx : crs_elems_index, agm pf_idx crs_idx • (mv_polynomial.eval f (crs_elems crs_idx))) (c)) 
            = 0
            ))
            ∧
          (∀ idx : proof_elems_index, 
            ∀ val ∈ proof_element_checks idx, 
              ((val : STMT → crs_elems_index → F) stmt = agm idx))
        )
          → relation stmt (extractor agm)) -- crs_elems proof check_polynomial
structure AGM_proof_system :=
  (relation : STMT → WIT → Prop)
  (n_sample : ℕ) -- a type of symbols to represent toxic waste elems
  (n_crs : ℕ) -- a type of indices for crs elems
  (crs_elems : (fin n_crs) → (mv_polynomial (fin n_sample) F)) -- the value of each crs elem as a polynomial of toxic waste elems
  -- an index into proof elems
  -- To avoid nested indexing, we assume that the prover provides the values of any elements in the checks that the verifier would compute. In this formalism, the verifier makes two kinds of checks - checks that the polynomial evaluates to 0, and checks that the verifier proof elements are consistent with the statement.
  (proof_elems_index : Type) 
  -- the coefficient of a particular crs elem in a particular proof elem for an honest prover (Not needed in soundness def)
  -- (proof_crs_component : STMT → WIT → proof_elems_index → crs_elems_index → F) 
  -- (permissible_inclusion : proof_elems_index → crs_elems_index → bool) -- whether it is possible for a malicious prover to include a particular crs elem in a particular proof elem - used to represent distinction between G1 and G2
  -- mv_polynomials of proof elems that the verifier checks to be zero
  (polynomial_checks : list (mv_polynomial proof_elems_index F)) 
  -- proof elements constructed from the statement that the verifier checks the construction of
  (proof_element_checks : proof_elems_index → option (STMT → (fin n_crs)  → F))
  -- Extracts the witness from an AGM
  (extractor : (proof_elems_index → (fin n_crs) → F) → WIT)
  -- given an agm which makes a valid proof, the extractor must give a correct witness
  (soundness : 
    ∀ stmt : STMT, 
      ∀ agm : proof_elems_index → (fin n_crs)  → F,
        -- if all checks on the proof pass, the extracted witness must satisfy the relation
        (
          (∀ c ∈ polynomial_checks, 
          (∀ f : (fin n_sample) → F, 
          (∀ s : fin n_sample, f s ≠ 0) →
          (mv_polynomial.eval (λ pf_idx, ∑ crs_idx : (fin n_crs) , agm pf_idx crs_idx • (mv_polynomial.eval f (crs_elems crs_idx))) (c)) 
            = 0
            ))
            ∧
          (∀ idx : proof_elems_index, 
            ∀ val ∈ proof_element_checks idx, 
              ((val : STMT → (fin n_crs)  → F) stmt = agm idx))
        )
          → relation stmt (extractor agm)) -- crs_elems proof check_polynomial

lemma lambda_mul {A B : Type u} [has_mul A] (a : A) (b : B → A) : (λ (i : B), a * b i) = (λ i, a) * b :=
begin
  ext i,
  rw pi.mul_apply,
end

-- def uniform_degree {σ F : Type*} [field F] (p : mv_polynomial σ F) (d : ℕ) : Prop :=


def uniform_degree {σ F : Type*} [field F] (p : mv_polynomial σ F) (d : ℕ) : Prop := 
∀ (f : σ → F), ∀ (a : F), mv_polynomial.eval ((λ x, a) * f) p = a ^ d * mv_polynomial.eval (f) p


-- example (my_type my_type' F : Type) [field F] [fintype my_type'] (a c : F) 
--   (b : my_type -> my_type' -> F) : 
--   (λ (p : my_type), a * ∑ (x : my_type'), b p x * c) = 0 → false :=
-- begin
--   intro h,
--   -- have : (λ (p : my_type), a * ∑ (x : my_type'), b p x * c) = a * (λ (p : my_type), ∑ (x : my_type'), b p x * c), 
--   -- a has type F but is expected to have type my_type → F
--     have : (λ (p : my_type), a * ∑ (x : my_type'), b p x * c) = (λ x : my_type, a) * (λ (p : my_type), ∑ (x : my_type'), b p x * c), 
--     {
--       ext,
--       refl,
--     },
--     rw this at h,

-- end

noncomputable def change_exponent (𝓟 : AGM_proof_system) 
  (sample : fin 𝓟.n_sample) (d : ℕ) 
  (all_checks_uniform_degree : ∀ c ∈ 𝓟.polynomial_checks, uniform_degree c d) : AGM_proof_system :=
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
    rintros stmt agm ⟨poly_checks_pass', proof_elem_checks_pass'⟩,
    apply 𝓟.soundness,
    split,
    {
      intros c in_checks f f_never_zero,

      replace poly_checks_pass' := poly_checks_pass' c in_checks f f_never_zero,
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
 

-- maps an element of a fin of a sum of naturals, to an index into the sum, and an index into the value
def fin_sum_to_fin_fin_1 (a : ℕ) (b : fin a -> ℕ) (i : fin (∑ ai : fin a, b ai)) : fin a := sorry
def fin_sum_to_fin_fin_2 (a : ℕ) (b : fin a -> ℕ) (i : fin (∑ ai : fin a, b ai)) : fin (b (fin_sum_to_fin_fin_1 a b i)) := sorry

def fin_fin_to_sum_fin (a : ℕ) (b : fin a -> ℕ) (ai : fin a) (bi : fin (b ai)) : fin (∑ ai : fin a, b ai) := sorry

@[simp] lemma fin_sum_to_fin_fin_1_fin_fin_to_sum_fin (a : ℕ) (b : fin a -> ℕ) (ai : fin a) (bi : fin (b ai)) :
  fin_sum_to_fin_fin_1 a b (fin_fin_to_sum_fin a b ai bi) = ai := sorry

-- @[simp] lemma fin_sum_to_fin_fin_2_fin_fin_to_sum_fin (a : ℕ) (b : fin a -> ℕ) (ai : fin a) (bi : fin (b ai)) :
--   fin_sum_to_fin_fin_2 a b (fin_fin_to_sum_fin a b ai bi) == bi := sorry

lemma sum_of_fin_sum {S : Type*} [add_comm_monoid S] 
  (a : ℕ) (b : fin a -> ℕ) (f : fin (∑ ai : fin a, b ai) -> S) : 
  ∑ i : fin (∑ ai : fin a, b ai), f i 
  = ∑ (ai : fin a), (∑ bi : fin (b ai), f (fin_fin_to_sum_fin a b ai bi))
:= sorry

def fin_add_of_fin_fin {S : Type*} {a b : ℕ} (f : fin a -> S ) (g : fin b -> S ) (x : fin (a + b)) :
S := sorry

@[simp] lemma fin_add_of_fin_fin_nat_add  {S : Type*} {a b : ℕ} (f : fin a -> S ) (g : fin b -> S ) (i : fin b) : 
  fin_add_of_fin_fin f g (fin.nat_add a i) = g i := sorry

@[simp] lemma fin_add_of_fin_fin_cast_add  {S : Type*} {a b : ℕ} (f : fin a -> S ) (g : fin b -> S ) (i : fin a) : 
  fin_add_of_fin_fin f g (fin.cast_add b i) = f i := sorry

@[simp] lemma fin_add_of_fin_fin_comp_cast_add  {S : Type*} {a b : ℕ} (f : fin a -> S ) (g : fin b -> S ) : 
  (fin_add_of_fin_fin f g) ∘ (fin.cast_add b) = f := sorry

-- Given a decomposition of each crs element into a collection of polynomials that sum to it
-- we can construct a new proof system splitting those terms up
-- Here, we assume all crs elements are decomposed into the same number of elements, but this need not be the case in principle.
noncomputable def split_crs (𝓟 : AGM_proof_system) 
  -- For each old crs element, a number of splits for it
  (crs_splits : 
   fin (𝓟.n_crs) -> ℕ)
  -- For each split, a polynomial over the old sample elements
  (split : 
    Π crs_idx : fin 𝓟.n_crs, 
      (fin (crs_splits crs_idx) -> mv_polynomial (fin 𝓟.n_sample) F) ) 
  -- The sum of polynomials over a split must equal the old crs polynomial.
  (sum_split : 
    Π crs_idx : fin 𝓟.n_crs, 
      ∑ split_idx : fin (crs_splits crs_idx), split crs_idx split_idx = 𝓟.crs_elems crs_idx)
  -- A default element for each split
  (default :
    Π crs_idx : fin 𝓟.n_crs, fin (crs_splits crs_idx)
  )
      : AGM_proof_system :=
{ relation := 𝓟.relation,
  n_sample := 𝓟.n_sample + ∑ crs_idx : fin 𝓟.n_crs, crs_splits crs_idx,
  n_crs := ∑ crs_idx : fin 𝓟.n_crs, crs_splits crs_idx,
  crs_elems := λ idx, 
    let old_crs_index : fin 𝓟.n_crs := fin_sum_to_fin_fin_1 𝓟.n_crs crs_splits idx in 
    let split_index : fin (crs_splits old_crs_index) := fin_sum_to_fin_fin_2 𝓟.n_crs crs_splits idx in 
      (mv_polynomial.rename (fin.cast_add _) (split old_crs_index split_index))
      + mv_polynomial.X (fin.nat_add 𝓟.n_sample (idx))
      - mv_polynomial.X (fin.nat_add 𝓟.n_sample (fin_fin_to_sum_fin 𝓟.n_crs crs_splits old_crs_index ((fin_rotate _) split_index)))
      ,
  proof_elems_index := 𝓟.proof_elems_index,
  polynomial_checks := 𝓟.polynomial_checks,
  proof_element_checks := λ proof_elem_idx, 
    option.map 
      (begin
        intros old_map stmt idx,
        exact old_map stmt (fin_sum_to_fin_fin_1 𝓟.n_crs crs_splits idx),
      end ) 
      (𝓟.proof_element_checks proof_elem_idx),
  -- old_map stmt (fin_sum_to_fin_fin_1 𝓟.n_crs crs_splits idx)
  extractor := begin
    intro thing,
    apply 𝓟.extractor,
    intros proof_elems_idx old_crs_idx,
    apply thing proof_elems_idx,
    exact fin_fin_to_sum_fin 𝓟.n_crs crs_splits old_crs_idx (default old_crs_idx),
  end,
  soundness := begin
    rintros stmt agm ⟨poly_checks_pass', proof_elem_checks_pass'⟩,
    apply 𝓟.soundness,
    -- TODO prove something about the agm
    split,
    { 
      intros c in_checks f f_never_zero,

      replace poly_checks_pass' := poly_checks_pass' c in_checks,
      simp at *,      
      replace poly_checks_pass' := poly_checks_pass' (@fin_add_of_fin_fin F 𝓟.n_sample _ f (λ x, 1)),
      have : ∀ (s : fin (𝓟.n_sample + ∑ (crs_idx : fin 𝓟.n_crs), crs_splits crs_idx)), ¬fin_add_of_fin_fin f (λ (x : fin (∑ (crs_idx : fin 𝓟.n_crs), crs_splits crs_idx)), 1) s = 0,
      {
        sorry
      },
      replace poly_checks_pass' := poly_checks_pass' this,
      simp at poly_checks_pass',
      simp_rw [sum_of_fin_sum] at poly_checks_pass',
      simp_rw [fin_sum_to_fin_fin_1_fin_fin_to_sum_fin] at poly_checks_pass',


      convert poly_checks_pass',
      funext pf_idx,
      congr' 1,
      funext ai,
      have foo : (λ (ai : fin 𝓟.n_crs), crs_splits ai) = crs_splits,
      {
        funext, 
        refl,
      },
      rw foo,
      sorry,
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