import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Logic.Equiv.Fin
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.BigOperators.Basic


open scoped BigOperators Classical

section

open MvPolynomial


-- TODO before all this, finalize the terminology for the various levels of instantiation.
-- TODO make a structure that doesn't track components/linear extractor
--    then make another structure that returns AGMProofSystemv2
-- TODO if dependent is not needed dont use the syntax


/--
An `AGMProofSystemInstantiation` is a SNARK for a particular arithmetic circuit over a
particular field
-/
structure AGMProofSystemInstantiation (F : Type) [Field F] where
  /-- The type of statements -/
  Stmt : Type
  /-- The type indexing toxic waste elements sampled -/
  Sample : Type
  /-- The type indexing SRS elements in group I, -/
  SRSElements_G1 : Type
  ListSRSElements_G1 : List SRSElements_G1
  /-- Similarly -/
  SRSElements_G2 : Type
  ListSRSElements_G2 : List SRSElements_G2

  /-- The SRS elements themselves, described as polynomials in the samples -/
  SRSElementValue_G1 : SRSElements_G1 → MvPolynomial Sample F
  SRSElementValue_G2 : SRSElements_G2 → MvPolynomial Sample F

  /-- A type indexing proof elements in each group -/
  Proof_G1 : Type
  ListProof_G1 : List Proof_G1
  Proof_G2 : Type
  ListProof_G2 : List Proof_G2

  /-- The type indexing equations the verifier checks -/
  EqualityChecks : Type

  /-- The pairings that the verifier computes for each equation
  (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  Pairings : EqualityChecks → Type

  ListPairings : (k : EqualityChecks) → List (Pairings k)

  /-- The coefficient that the verifier uses for the jth element of the ith component of the SRSI
  in the left half of the lth paring of the kth equality check -/
  verificationPairingSRS_G1 : Stmt -> (k : EqualityChecks) → Pairings k → SRSElements_G1 → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the SRSII
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingSRS_G2 : Stmt -> (k : EqualityChecks) → Pairings k → SRSElements_G2 → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_G1
  in the left half of the lth paring of the kth equality check -/
  verificationPairingProof_G1 : Stmt -> (k : EqualityChecks) → Pairings k → Proof_G1 → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_G2
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingProof_G2 : Stmt -> (k : EqualityChecks) → Pairings k → Proof_G2 → F

  /-- Identified Proof elements that are the same on the left and right. This is sometimes
  necessary to specify in Type I SNARKs where proof elements can be passed back and forth from one
  side of the pairing to the other. It defaults to empty. -/
  Identified_Proof_Elems : List (Proof_G1 × Proof_G2) := []

namespace AGMProofSystemInstantiation

/-- The type of possible provers in the AGM model.
A prover simply assigns, for each proof element and each SRS element from the group of that proof element, a coefficient. -/
def Prover (F : Type) [Field F]
    (𝓟 : AGMProofSystemInstantiation F) : Type :=
  (𝓟.Proof_G1 -> 𝓟.SRSElements_G1 -> F) × (𝓟.Proof_G2 -> 𝓟.SRSElements_G2 -> F)

noncomputable def proof_element_G1_as_poly {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (pf_elem : 𝓟.Proof_G1) :
    MvPolynomial (𝓟.Sample) F :=
  (𝓟.ListSRSElements_G1.map fun SRS_elem =>
          MvPolynomial.C (prover.fst pf_elem SRS_elem) * (𝓟.SRSElementValue_G1 SRS_elem)).sum

noncomputable def proof_element_G2_as_poly {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (pf_elem : 𝓟.Proof_G2) :
    MvPolynomial (𝓟.Sample) F :=
  (𝓟.ListSRSElements_G2.map fun SRS_elem =>
          MvPolynomial.C (prover.snd pf_elem SRS_elem) * (𝓟.SRSElementValue_G2 SRS_elem)).sum

/-- The pairing evaluation, represented as a MvPolynomial in the samples -/
noncomputable def pairing_poly {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) (check_idx : 𝓟.EqualityChecks) (pairing : 𝓟.Pairings check_idx) :
    MvPolynomial 𝓟.Sample F :=
  (
    ( -- G1 input of pairing
      -- Proof component
      (
        (𝓟.ListProof_G1.map fun pf_elem => -- Sum over all left proof components
          C (𝓟.verificationPairingProof_G1 stmt check_idx pairing pf_elem) -- Coefficient of that element
            *
            -- Times the proof component itself
            𝓟.proof_element_G1_as_poly prover pf_elem).sum
      )
      +
      ( -- SRS component
        (𝓟.ListSRSElements_G1.map fun SRS_elem =>
          C (𝓟.verificationPairingSRS_G1 stmt check_idx pairing SRS_elem) * (𝓟.SRSElementValue_G1 SRS_elem)).sum
      )
    )
    *
    ( -- G2 input of pairing
      -- Proof component
      (
        (𝓟.ListProof_G2.map fun pf_elem => -- Sum over all Right proof components
          C (𝓟.verificationPairingProof_G2 stmt check_idx pairing pf_elem) -- Coefficient of that element
            *
            -- Times the proof component itself
            𝓟.proof_element_G2_as_poly prover pf_elem).sum
      )
      +
      ( -- SRS component
        (𝓟.ListSRSElements_G2.map fun SRS_elem =>
          C (𝓟.verificationPairingSRS_G2 stmt check_idx pairing SRS_elem) * (𝓟.SRSElementValue_G2 SRS_elem)).sum
      )
    )
  )

/-- The value that the verifier checks to be equal to 0 for a given equality check, as a
MvPolynomial in the samples.
-/
noncomputable def check_poly {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) (check_idx : 𝓟.EqualityChecks) :
    MvPolynomial 𝓟.Sample F :=
  (
  (𝓟.ListPairings check_idx).map fun pairing =>
    𝓟.pairing_poly prover stmt check_idx pairing
  ).sum


def verify {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) : Prop :=
  (
    ∀ check_idx : 𝓟.EqualityChecks, 𝓟.check_poly prover stmt check_idx = 0
  )
  ∧
  ∀ pfs ∈ 𝓟.Identified_Proof_Elems,
    𝓟.proof_element_G1_as_poly prover pfs.fst = 𝓟.proof_element_G2_as_poly prover pfs.snd


def soundness (F : Type) [Field F]
    (𝓟 : AGMProofSystemInstantiation F)
    (Wit : Type) (relation : 𝓟.Stmt -> Wit -> Prop)
    (extractor : 𝓟.Prover -> Wit) : Prop :=
   ∀ stmt : 𝓟.Stmt,
    ∀ prover : 𝓟.Prover,
      𝓟.verify prover stmt -> relation stmt (extractor prover)


def completeness (F : Type) [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (Wit : Type)
    (relation : 𝓟.Stmt -> Wit -> Prop)
    (prover : 𝓟.Stmt -> Wit -> 𝓟.Prover) : Prop :=
   ∀ stmt : 𝓟.Stmt,
    ∀ wit : Wit,
      relation stmt wit -> 𝓟.verify (prover stmt wit) stmt

end AGMProofSystemInstantiation

end
