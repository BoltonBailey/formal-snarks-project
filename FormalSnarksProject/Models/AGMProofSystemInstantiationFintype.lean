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




structure AGMProofSystemInstantiation (F : Type) [Field F] where
  /-- The type of statements -/
  Stmt : Type
  /-- The type indexing toxic waste elements sampled -/
  Sample : Type
  /-- The type indexing SRS elements in group I, -/
  SRSElements_G1 : Type
  [FintypeSRSElements_G1 : Fintype SRSElements_G1]
  /-- Similarly -/
  SRSElements_G2 : Type
  [FintypeSRSElements_G2 : Fintype SRSElements_G2]

  /-- The SRS elements themselves, described as polynomials in the samples -/
  SRSElementValue_G1 : (i : SRSElements_G1) → MvPolynomial (Sample) F
  SRSElementValue_G2 : (i : SRSElements_G2) → MvPolynomial (Sample) F

  /-- A type indexing proof elements in each group -/
  Proof_G1 : Type
  [FintypeProof_G1 : Fintype Proof_G1]
  Proof_G2 : Type
  [FintypeProof_G2 : Fintype Proof_G2]

  /-- The type indexing equations the verifier checks -/
  EqualityChecks : Type

  /-- The pairings that the verifier computes for each equation
  (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  Pairings : EqualityChecks → Type

  [FintypePairings : (k : EqualityChecks) → Fintype (Pairings k)]

  /-- The coefficient that the verifier uses for the jth element of the ith component of the SRSI
  in the left half of the lth paring of the kth equality check -/
  verificationPairingSRS_G1 : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : SRSElements_G1) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the SRSII
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingSRS_G2 : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : SRSElements_G2) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_G1
  in the left half of the lth paring of the kth equality check -/
  verificationPairingProof_G1 : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : Proof_G1) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_G2
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingProof_G2 : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : Proof_G2) → F

attribute [instance] AGMProofSystemInstantiation.FintypeSRSElements_G1
attribute [instance] AGMProofSystemInstantiation.FintypeSRSElements_G2
attribute [instance] AGMProofSystemInstantiation.FintypeProof_G1
attribute [instance] AGMProofSystemInstantiation.FintypeProof_G2
attribute [instance] AGMProofSystemInstantiation.FintypePairings


/-- The type of possible provers in the AGM model.
A prover simply assigns, for each proof element and each SRS element from the group of that proof element, a coefficient. -/
def AGMProofSystemInstantiation.Prover (F : Type) [Field F]
    (𝓟 : AGMProofSystemInstantiation F) : Type :=
  (𝓟.Proof_G1 -> 𝓟.SRSElements_G1 -> F) × (𝓟.Proof_G2 -> 𝓟.SRSElements_G2 -> F)

def AGMProofSystemInstantiation.verify {F : Type} [Field F]
    (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) : Prop :=
  ∀ check_idx : 𝓟.EqualityChecks,
    ∑ pairing : (𝓟.Pairings check_idx),
      ( -- LHS of pairing TODO double check this I was tired
        -- Proof component
        (
          ∑ pf_elem : 𝓟.FintypeProof_G1.elems, -- Sum over all left proof components
            C (𝓟.verificationPairingProof_G1 stmt check_idx pairing pf_elem) -- Coefficient of that element
            *
            -- Times the proof component itself TODO refactor this to be a function
            ∑ SRS_elem : 𝓟.FintypeSRSElements_G1.elems,
              C (prover.fst pf_elem SRS_elem) * (𝓟.SRSElementValue_G1 SRS_elem)
        )
        +
        ( -- SRS component
          ∑ SRS_elem : 𝓟.FintypeSRSElements_G1.elems,
            C (𝓟.verificationPairingSRS_G1 stmt check_idx pairing SRS_elem) * (𝓟.SRSElementValue_G1 SRS_elem)
        )
      )
      *
      ( -- RHS of pairing
        -- Proof component
        (
          ∑ pf_elem : 𝓟.FintypeProof_G2.elems, -- Sum over all right proof components
            C (𝓟.verificationPairingProof_G2 stmt check_idx pairing pf_elem) -- Coefficient of that element
            *
            -- Times the proof component itself TODO refactor this to be a function
            ∑ SRS_elem : 𝓟.FintypeSRSElements_G2.elems,
              C (prover.snd pf_elem SRS_elem) * (𝓟.SRSElementValue_G2 SRS_elem)
        )
        +
        ( -- SRS component
          ∑ SRS_elem : 𝓟.FintypeSRSElements_G2.elems,
            C (𝓟.verificationPairingSRS_G2 stmt check_idx pairing SRS_elem) * (𝓟.SRSElementValue_G2 SRS_elem)
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
