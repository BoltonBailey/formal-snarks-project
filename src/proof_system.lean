
import algebra.field
import algebra.polynomial.big_operators -- correct import?

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


-- structure pairing_based_snark_scheme (F : Type) [field F] (toxic : Type) (crs_size : ℕ) (crs : fin crs_size -> mv_polynomial toxic F) (prove : sorry)