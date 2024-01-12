import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.MvPolynomial.Monad
import Mathlib.Algebra.BigOperators.Basic

open scoped BigOperators

section

/-!

This file contains classes for noninteractive proof systems.

-/


-- universe u
-- /-- The finite field parameter of our SNARK -/
-- parameter {F : Type}
-- parameter [field F]
-- The types of the statement and witness are assumed to be collections of n_stmt and n_wit field elements respectively.
-- parameters {n_sample n_crs n_stmt n_wit n_proof : ℕ}
-- def STMT := fin n_stmt -> F
-- def WIT := fin n_wit -> F
-- def SAMPLE := fin n_sample -> F
-- def CRS := fin n_crs -> F
-- def PROOF := fin n_proof -> F
-- def PROOF_MODEL := fin n_crs -> fin n_proof -> ℕ
structure AGMProofSystem (F : Type) [Field F] (n_stmt n_wit : ℕ) where
  relation : (Fin n_stmt → F) → (Fin n_wit → F) → Prop
  nSample : ℕ
  -- a type of symbols to represent toxic waste elems
  nCrs : ℕ
  -- a type of indices for crs elems
  crs_elems : Fin n_crs → MvPolynomial (Fin n_sample) F
  -- the value of each crs elem as a polynomial of toxic waste elems
  -- an index into proof elems
  -- To avoid nested indexing, we assume that the prover provides the values of any elements in the checks that the verifier would compute. In this formalism, the verifier makes two kinds of checks - checks that the polynomial evaluates to 0, and checks that the verifier proof elements are consistent with the statement.
  proof_elems_index : Type
  -- mv_polynomials of proof elems that the verifier checks to be zero
  polynomial_checks : List (MvPolynomial proof_elems_index F)
  -- proof elements constructed from the statement that the verifier checks the construction of (or, more simply, constructs themselves)
  proof_element_checks : proof_elems_index → Option ((Fin n_stmt → F) → Fin n_crs → F)
  -- Extracts the witness from an AGM
  extractor : (proof_elems_index → Fin n_crs → F) → Fin n_wit → F
  -- given an agm which makes a valid proof, the extractor must give a correct witness
  soundness :
    ∀ stmt : Fin n_stmt → F,
      ∀ agm : proof_elems_index → Fin n_crs → F,
        ((-- if all checks on the proof pass, the extracted witness must satisfy the relation
            -- (∀ f : (fin n_sample) → F, 
            -- (∀ s : fin n_sample, f s ≠ 0) →
            ∀ c ∈ polynomial_checks,
              (MvPolynomial.bind₁
                  (fun pf_idx => ∑ crs_idx : Fin n_crs, agm pf_idx crs_idx • crs_elems crs_idx) : 
                  MvPolynomial proof_elems_index F -> MvPolynomial (Fin n_sample) F) c =
                0) ∧
            ∀ idx : proof_elems_index,
              ∀ val ∈ proof_element_checks idx,
                (val : (Fin n_stmt → F) → Fin n_crs → F) stmt = agm idx) →
          relation stmt (extractor agm)
#align AGM_proof_system AGMProofSystem

-- crs_elems proof check_polynomial
-- potential other components
-- the coefficient of a particular crs elem in a particular proof elem for an honest prover (Not needed in soundness def)
-- (proof_crs_component : (fin n_stmt -> F) → WIT → proof_elems_index → crs_elems_index → F) 
-- (permissible_inclusion : proof_elems_index → crs_elems_index → bool) -- whether it is possible for a malicious prover to include a particular crs elem in a particular proof elem - used to represent distinction between G1 and G2
end
