
import algebra.field
import algebra.polynomial.big_operators -- correct import?
import data.mv_polynomial.basic

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
parameters {n_sample n_crs n_stmt n_wit n_proof : ℕ}

def STMT := fin n_stmt -> F
def WIT := fin n_wit -> F
def SAMPLE := fin n_sample -> F
def CRS := fin n_crs -> F
def PROOF := fin n_proof -> F
def PROOF_MODEL := fin n_crs -> fin n_proof -> ℕ

-- The prove function is to multiply the crs vector by the  n_crs by n_proof matrix from proof model, then
def prove (crs : CRS) (model : PROOF_MODEL) : PROOF :=
  λ (i : fin n_proof), 
    ∑ x in (finset.fin_range n_crs), (crs x) * (model x i)

/-- A `AGM_proof_system` is a noninteractive proof system under the AGM assumption. The type class is defined over a product of types and functions

- Relation is the relation on statements and witnesses for which the system makes proofs.
- setup takes a (random) sample and outputs a common reference string (this should really all be dependent types on a security parameter in ℕ)
- prove takes the crs, and the satisfying instance, and outputs a proof
- verify verifies the proof (against the statement and crs)

The class requires proof of the following propositions
- 
-/
class AGM_proof_system 
  (relation : STMT -> WIT -> Prop) 
  (setup : SAMPLE -> CRS) 
  (prover : STMT -> WIT -> PROOF_MODEL)
  (verify : CRS -> STMT -> PROOF -> bool) 
  (extractor : PROOF_MODEL -> WIT)
:=
  (correctness : 
    ∀ (sample : SAMPLE), 
      ∀ (stmt : STMT), 
        ∀ (wit : WIT), 
          (let crs := setup sample in 
          verify crs stmt (prove crs (prover stmt wit)) = tt ))
  (knowledge_soundness : 
    ∀ (sample : SAMPLE), 
    ∀ (stmt : STMT), 
      ∀ (model : PROOF_MODEL), 
        (let crs := setup sample in 
        verify crs stmt (prove crs model) = tt 
          -> relation stmt (extractor model)))













-- TODO(Bolton): Perhaps an easier approach would be to explictly give flatten a map into the support monomials and also avoid type theory by going for fins

-- TODO parameters above into definition
-- todo completeness
structure AGM_proof_system' :=
  (relation : STMT → WIT → Prop)
  (sample_space : Type) -- a type of symbols to represent toxic waste elems
  [fin_sample_space : fintype sample_space]
  (crs_elems_index : Type) -- a type of indices for crs elems
  [fin_crs : fintype crs_elems_index]
  (crs_elems : crs_elems_index → (mv_polynomial sample_space F)) -- the value of each crs elem as a polynomial of toxic waste elems
  (proof_elems_index : Type) -- an index into proof elems
  (proof_crs_component : STMT → WIT → proof_elems_index → crs_elems_index → F) -- the coefficient of a particular crs elem in a particular proof elem for an honest prover
  (permissible_inclusion : proof_elems_index → crs_elems_index → bool) -- whether it is possible for a malicious prover to include a particular crs elem in a particular proof elem - used to represent distinction between G1 and G2
  (checks : list (STMT → mv_polynomial proof_elems_index (mv_polynomial crs_elems_index F))) -- mv_polynomials of proof elems that the verifier checks to be zero
  (extractor : (proof_elems_index → crs_elems_index → F) → WIT)
  -- given an agm which makes a valid proof, the extractor must give a correct witness
  (soundness : 
    ∀ stmt : STMT, 
      ∀ agm : proof_elems_index → crs_elems_index → F,
        let wit := extractor agm in
        let proof : proof_elems_index → mv_polynomial sample_space F := λ pi, ∑ i : crs_elems_index, agm pi i • crs_elems i in
        -- if all checks on the proof pass, the extracted witness
        (∀ c ∈ checks,
          mv_polynomial.eval₂ (mv_polynomial.eval₂_hom mv_polynomial.C crs_elems) proof ((c : STMT → mv_polynomial proof_elems_index (mv_polynomial crs_elems_index F)) stmt) = 0)
          → relation stmt (extractor agm))

-- example (α β : Type) (hα : fintype α) (hβ : fintype β) : fintype (α ⊕ β) := by library_search

def flatten (𝓟 : AGM_proof_system') : AGM_proof_system' :=
{ -- The relation the flattened SNARK checks is the same
  relation := 𝓟.relation,
  -- We have an additional sample for each support monomial of each crs element polynomial
  sample_space := 𝓟.sample_space ⊕ (Σ (crs_idx : 𝓟.crs_elems_index), (𝓟.crs_elems crs_idx).support),
  fin_sample_space := begin
    apply @sum.fintype _ _ (𝓟.fin_sample_space) _,
    apply @sigma.fintype _ _ _ _,
    classical,
    -- exact classical.dec_eq 𝓟.crs_elems_index,
    exact 𝓟.fin_crs,
    intro a,
    exact (𝓟.crs_elems a).support.fintype_coe_sort,
  end,
  -- The CRS elements become polynomials with one monomial from the original polynomial
  -- an additional sample added, and an additional sample subtracted.
  crs_elems_index := (Σ (crs_idx : 𝓟.crs_elems_index), (𝓟.crs_elems crs_idx).support),
  fin_crs := begin
    apply @sigma.fintype _ _ _ _,
    classical,
    -- exact classical.dec_eq 𝓟.crs_elems_index,
    exact 𝓟.fin_crs,
    intro a,
    exact (𝓟.crs_elems a).support.fintype_coe_sort,
  end,
  crs_elems := λ ⟨c1, c2⟩, begin
    
  end
  ,
  proof_elems_index := _,
  proof_crs_component := _,
  permissible_inclusion := _,
  checks := _,
  extractor := _,
  soundness := _ }


end