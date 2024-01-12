import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.MvPolynomial.Monad
import Mathlib.Algebra.BigOperators.Basic


open scoped BigOperators Classical

section

open MvPolynomial


-- TODO before all this, finalize the terminology for the various levels of instantiation.
-- TODO make a structure that doesn't track components/linear extractor
--    then make another structure that returns AGMProofSystemv2




structure AGMProofSystemInstantiation (F : Type) [Field F] where
  /-- The type of statements -/
  Stmt : Type
  /-- The type indexing toxic waste elements sampled -/
  Sample : Type
  /-- The type indexing crs elements in group I, -/
  CrsElements_Left : Type
  [FintypeCrsElements_Left : Fintype CrsElements_Left]
  /-- Similarly -/
  CrsElements_Right : Type
  [FintypeCrsElements_Right : Fintype CrsElements_Right]

  /-- The crs elements themselves, described as polynomials in the samples -/
  crsElementValue_Left : (i : CrsElements_Left) → MvPolynomial (Sample) F
  crsElementValue_Right : (i : CrsElements_Right) → MvPolynomial (Sample) F

  /-- A type indexing proof elements in each group -/
  Proof_Left : Type
  [FintypeProof_Left : Fintype Proof_Left]
  Proof_Right : Type
  [FintypeProof_Right : Fintype Proof_Right]

  /-- The type indexing equations the verifier checks -/
  EqualityChecks : Type

  /-- The pairings that the verifier computes for each equation
  (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  Pairings : EqualityChecks → Type

  [FintypePairings : (k : EqualityChecks) → Fintype (Pairings k)]

  /-- The coefficient that the verifier uses for the jth element of the ith component of the CRSI
  in the left half of the lth paring of the kth equality check -/
  verificationPairingCRSLeft : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : CrsElements_Left) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the CRSII
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingCRSRight : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : CrsElements_Right) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_Left
  in the left half of the lth paring of the kth equality check -/
  verificationPairingProofLeft : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : Proof_Left) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_Right
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingProofRight : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : Proof_Right) → F

attribute [instance] AGMProofSystemInstantiation.FintypeCrsElements_Left
attribute [instance] AGMProofSystemInstantiation.FintypeCrsElements_Right
attribute [instance] AGMProofSystemInstantiation.FintypeProof_Left
attribute [instance] AGMProofSystemInstantiation.FintypeProof_Right
attribute [instance] AGMProofSystemInstantiation.FintypePairings


/-- The type of possible provers in the AGM model.
A prover simply assigns, for each proof element and each crs element from the group of that proof element, a coefficient. -/
def AGMProofSystemInstantiation.Prover (F : Type) [Field F]
    (𝓟 : AGMProofSystemInstantiation F) : Type :=
  (𝓟.Proof_Left -> 𝓟.CrsElements_Left -> F) × (𝓟.Proof_Right -> 𝓟.CrsElements_Right -> F)

def AGMProofSystemInstantiation.verify {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) : Prop :=
  ∀ check_idx : 𝓟.EqualityChecks,
    ∑ pairing : (𝓟.Pairings check_idx),
      ( -- LHS of pairing TODO double check this I was tired
        -- Proof component
        (
          ∑ pf_elem : 𝓟.FintypeProof_Left.elems, -- Sum over all left proof components
            C (𝓟.verificationPairingProofLeft stmt check_idx pairing pf_elem) -- Coefficient of that element
            *
            -- Times the proof component itself TODO refactor this to be a function
            ∑ crs_elem : 𝓟.FintypeCrsElements_Left.elems,
              C (prover.fst pf_elem crs_elem) * (𝓟.crsElementValue_Left crs_elem)
        )
        +
        ( -- CRS component
          ∑ crs_elem : 𝓟.FintypeCrsElements_Left.elems,
            C (𝓟.verificationPairingCRSLeft stmt check_idx pairing crs_elem) * (𝓟.crsElementValue_Left crs_elem)
        )
      )
      *
      ( -- RHS of pairing
        -- Proof component
        (
          ∑ pf_elem : 𝓟.FintypeProof_Right.elems, -- Sum over all right proof components
            C (𝓟.verificationPairingProofRight stmt check_idx pairing pf_elem) -- Coefficient of that element
            *
            -- Times the proof component itself TODO refactor this to be a function
            ∑ crs_elem : 𝓟.FintypeCrsElements_Right.elems,
              C (prover.snd pf_elem crs_elem) * (𝓟.crsElementValue_Right crs_elem)
        )
        +
        ( -- CRS component
          ∑ crs_elem : 𝓟.FintypeCrsElements_Right.elems,
            C (𝓟.verificationPairingCRSRight stmt check_idx pairing crs_elem) * (𝓟.crsElementValue_Right crs_elem)
        )
      )
    = 0


def AGMProofSystemInstantiation.soundness (F : Type) [Field F]
    (𝓟 : AGMProofSystemInstantiation F)
    (Wit : Type) (relation : 𝓟.Stmt -> Wit -> Prop)
    (extractor : 𝓟.Prover -> Wit) : Prop :=
   ∀ stmt : 𝓟.Stmt,
    ∀ prover : 𝓟.Prover,
      𝓟.verify prover stmt -> relation stmt (extractor prover)

end
