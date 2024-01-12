import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.Variables
import Mathlib.Data.MvPolynomial.Monad
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.List.BigOperators.Basic


open scoped BigOperators Classical

section

open MvPolynomial


-- TODO before all this, finalize the terminology for the various levels of instantiation.
-- TODO make a structure that doesn't track components/linear extractor
--    then make another structure that returns AGMProofSystemv2



/--
An `AGMProofSystemInstantiation` is a SNARK for a particular arithmetic circuit over a
particular field
-/
structure AGMProofSystemInstantiation (F : Type) [Field F] where
  /-- The type of statements -/
  Stmt : Type
  /-- The type indexing toxic waste elements sampled -/
  Sample : Type
  /-- The type indexing crs elements in group I, -/
  CrsElements_Left : Type
  ListCrsElements_Left : List CrsElements_Left
  /-- Similarly -/
  CrsElements_Right : Type
  ListCrsElements_Right : List CrsElements_Right

  /-- The crs elements themselves, described as polynomials in the samples -/
  crsElementValue_Left : (i : CrsElements_Left) → MvPolynomial (Sample) F
  crsElementValue_Right : (i : CrsElements_Right) → MvPolynomial (Sample) F

  /-- A type indexing proof elements in each group -/
  Proof_Left : Type
  ListProof_Left : List Proof_Left
  Proof_Right : Type
  ListProof_Right : List Proof_Right

  /-- The type indexing equations the verifier checks -/
  EqualityChecks : Type

  /-- The pairings that the verifier computes for each equation
  (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  Pairings : EqualityChecks → Type

  ListPairings : (k : EqualityChecks) → List (Pairings k)

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

  /-- Identified Proof elements that are the same on the left and right. This is sometimes
  necessary to specify in Type I SNARKs where proof elements can be passed back and forth from one
  side of the pairing to the other. It defaults to empty. -/
  Identified_Proof_Elems : List (Proof_Left × Proof_Right) := []

/-- The type of possible provers in the AGM model.
A prover simply assigns, for each proof element and each crs element from the group of that proof element, a coefficient. -/
def AGMProofSystemInstantiation.Prover (F : Type) [Field F]
    (𝓟 : AGMProofSystemInstantiation F) : Type :=
  (𝓟.Proof_Left -> 𝓟.CrsElements_Left -> F) × (𝓟.Proof_Right -> 𝓟.CrsElements_Right -> F)

noncomputable def AGMProofSystemInstantiation.proof_element_left_as_poly {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (pf_elem : 𝓟.Proof_Left) :
    MvPolynomial (𝓟.Sample) F :=
  (𝓟.ListCrsElements_Left.map fun crs_elem =>
          MvPolynomial.C (prover.fst pf_elem crs_elem) * (𝓟.crsElementValue_Left crs_elem)).sum

noncomputable def AGMProofSystemInstantiation.proof_element_right_as_poly {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (pf_elem : 𝓟.Proof_Right) :
    MvPolynomial (𝓟.Sample) F :=
  (𝓟.ListCrsElements_Right.map fun crs_elem =>
          MvPolynomial.C (prover.snd pf_elem crs_elem) * (𝓟.crsElementValue_Right crs_elem)).sum


def AGMProofSystemInstantiation.verify {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) : Prop :=
  (
    ∀ check_idx : 𝓟.EqualityChecks,
    (
    (𝓟.ListPairings check_idx).map fun pairing =>
      ( -- LHS of pairing TODO double check this I was tired
        -- Proof component
        (
          (𝓟.ListProof_Left.map fun pf_elem => -- Sum over all left proof components
            C (𝓟.verificationPairingProofLeft stmt check_idx pairing pf_elem) -- Coefficient of that element
              *
              -- Times the proof component itself
              𝓟.proof_element_left_as_poly prover pf_elem).sum
        )
        +
        ( -- CRS component
         (𝓟.ListCrsElements_Left.map fun crs_elem =>
            C (𝓟.verificationPairingCRSLeft stmt check_idx pairing crs_elem) * (𝓟.crsElementValue_Left crs_elem)).sum
        )
      )
      *
      ( -- RHS of pairing
        -- Proof component
        (
          (𝓟.ListProof_Right.map fun pf_elem => -- Sum over all Right proof components
            C (𝓟.verificationPairingProofRight stmt check_idx pairing pf_elem) -- Coefficient of that element
              *
              -- Times the proof component itself
              𝓟.proof_element_right_as_poly prover pf_elem).sum
        )
        +
        ( -- CRS component
         (𝓟.ListCrsElements_Right.map fun crs_elem =>
            C (𝓟.verificationPairingCRSRight stmt check_idx pairing crs_elem) * (𝓟.crsElementValue_Right crs_elem)).sum
        )
      )
    ).sum = 0
  )
  ∧
  ∀ pfs ∈ 𝓟.Identified_Proof_Elems,
    𝓟.proof_element_left_as_poly prover pfs.fst = 𝓟.proof_element_right_as_poly prover pfs.snd



def AGMProofSystemInstantiation.soundness (F : Type) [Field F]
    (𝓟 : AGMProofSystemInstantiation F)
    (Wit : Type) (relation : 𝓟.Stmt -> Wit -> Prop)
    (extractor : 𝓟.Prover -> Wit) : Prop :=
   ∀ stmt : 𝓟.Stmt,
    ∀ prover : 𝓟.Prover,
      𝓟.verify prover stmt -> relation stmt (extractor prover)

end
