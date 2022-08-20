
import algebra.field
import algebra.polynomial.big_operators -- correct import?
import data.mv_polynomial.comm_ring
import data.equiv.fin -- name changed to logic equiv fin
import data.mv_polynomial.rename
import data.mv_polynomial.variables

open_locale big_operators

section

/-!

This file contains classes for noninteractive proof systems.

-/

universe u
/-- The finite field parameter of our SNARK -/
parameter {F : Type}
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
  -- proof elements constructed from the statement that the verifier checks the construction of (or, more simply, constructs themselves)
  (proof_element_checks : proof_elems_index → option (STMT → (fin n_crs) → F))
  -- Extracts the witness from an AGM
  (extractor : (proof_elems_index → (fin n_crs) → F) → WIT)
  -- given an agm which makes a valid proof, the extractor must give a correct witness
  (soundness : 
    ∀ stmt : STMT, 
      ∀ agm : proof_elems_index → (fin n_crs)  → F,
        -- if all checks on the proof pass, the extracted witness must satisfy the relation
        (
          (∀ c ∈ polynomial_checks,
          -- (∀ f : (fin n_sample) → F, 
          -- (∀ s : fin n_sample, f s ≠ 0) →
          (mv_polynomial.bind₁ 
            (λ pf_idx,
              ∑ crs_idx : (fin n_crs) , 
                agm pf_idx crs_idx • ((crs_elems crs_idx))) 
            (c)) 
            = 0
            )
            ∧
          (∀ idx : proof_elems_index, 
            ∀ val ∈ proof_element_checks idx, 
              ((val : STMT → (fin n_crs)  → F) stmt = agm idx)))
          → relation stmt (extractor agm)) -- crs_elems proof check_polynomial


end