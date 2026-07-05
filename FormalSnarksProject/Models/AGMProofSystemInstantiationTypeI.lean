import Mathlib
import CompPoly.Multivariate.CMvPolynomialEvalLemmas
import CompPoly.Multivariate.Rename


open scoped BigOperators

section

open CPoly
open CPoly.CMvPolynomial


/--
An `AGMProofSystemInstantiationTypeI` is a SNARK for a particular arithmetic circuit over a
particular field, in the Type I (symmetric pairing) setting.

In a symmetric pairing there is a single source group, so unlike
`AGMProofSystemInstantiation` (the Type III model) there is only one collection of SRS
elements and one copy of each proof element. Every SRS element and every proof element can be
used on either side of any pairing; consequently there is no need for the
`Identified_Proof_Elems` field of the Type III model, which existed to identify the G1 and G2
copies of a proof element.
-/
structure AGMProofSystemInstantiationTypeI (F : Type) [Field F] where
  /-- The type of statements -/
  Stmt : Type
  /-- The type indexing toxic waste elements sampled.
  A `FinEnum` instance gives an equivalence `Sample ≃ Fin n`, which is what the computable
  multivariate polynomials (`CMvPolynomial n F`) require. -/
  Sample : Type
  [Sample_FinEnum : FinEnum Sample]
  /-- The type indexing SRS elements (all in the single source group) -/
  SRSElements : Type
  [SRSElements_FinEnum : FinEnum SRSElements]
  /-- The SRS elements themselves, described as polynomials in the samples -/
  SRSElementValue : SRSElements → CMvPolynomial Sample F
  /-- A type indexing proof elements -/
  Proof : Type
  [Proof_FinEnum : FinEnum Proof]
  /-- The type indexing equations the verifier checks -/
  EqualityChecks : Type
  /-- The pairings that the verifier computes for each equation
  (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  Pairings : EqualityChecks → Type
  [Pairings_FinEnum : (k : EqualityChecks) → FinEnum (Pairings k)]

  /-- The coefficient that the verifier uses for the jth SRS element
  in the left half of the lth pairing of the kth equality check -/
  verificationPairingSRSLeft : Stmt -> (k : EqualityChecks) → Pairings k → SRSElements → F
  /-- The coefficient that the verifier uses for the jth SRS element
  in the right half of the lth pairing of the kth equality check -/
  verificationPairingSRSRight : Stmt -> (k : EqualityChecks) → Pairings k → SRSElements → F
  /-- The coefficient that the verifier uses for the jth proof element
  in the left half of the lth pairing of the kth equality check -/
  verificationPairingProofLeft : Stmt -> (k : EqualityChecks) → Pairings k → Proof → F
  /-- The coefficient that the verifier uses for the jth proof element
  in the right half of the lth pairing of the kth equality check -/
  verificationPairingProofRight : Stmt -> (k : EqualityChecks) → Pairings k → Proof → F

-- Register the bundled `FinEnum` fields as instances so that `FinEnum.toList`, the derived
-- `Fintype`, and the `≃ Fin n` equivalences are available from a bare `𝓟`.
attribute [instance]
  AGMProofSystemInstantiationTypeI.Sample_FinEnum
  AGMProofSystemInstantiationTypeI.SRSElements_FinEnum
  AGMProofSystemInstantiationTypeI.Proof_FinEnum
  AGMProofSystemInstantiationTypeI.Pairings_FinEnum

namespace AGMProofSystemInstantiationTypeI

/-- The type of possible provers in the AGM model.
A prover simply assigns, for each proof element and each SRS element, a coefficient.
Since there is a single group, there is a single coefficient function. -/
def Prover (F : Type) [Field F]
    (𝓟 : AGMProofSystemInstantiationTypeI F) : Type :=
  𝓟.Proof -> 𝓟.SRSElements -> F

def proof_element_as_poly {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (𝓟 : AGMProofSystemInstantiationTypeI F) (prover : 𝓟.Prover) (pf_elem : 𝓟.Proof) :
    CMvPolynomial (𝓟.Sample) F :=
  ((FinEnum.toList 𝓟.SRSElements).map fun SRS_elem =>
          CMvPolynomial.C (prover pf_elem SRS_elem) * (𝓟.SRSElementValue SRS_elem)).sum

/-- The pairing evaluation, represented as a CMvPolynomial in the samples -/
def pairing_poly {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (𝓟 : AGMProofSystemInstantiationTypeI F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) (check_idx : 𝓟.EqualityChecks) (pairing : 𝓟.Pairings check_idx) :
    CMvPolynomial 𝓟.Sample F :=
  (
    ( -- Left input of pairing
      -- Proof component
      (
        ((FinEnum.toList 𝓟.Proof).map fun pf_elem => -- Sum over all left proof components
          C (𝓟.verificationPairingProofLeft stmt check_idx pairing pf_elem) -- Coefficient of that element
            *
            -- Times the proof component itself
            𝓟.proof_element_as_poly prover pf_elem).sum
      )
      +
      ( -- SRS component
        ((FinEnum.toList 𝓟.SRSElements).map fun SRS_elem =>
          C (𝓟.verificationPairingSRSLeft stmt check_idx pairing SRS_elem) * (𝓟.SRSElementValue SRS_elem)).sum
      )
    )
    *
    ( -- Right input of pairing
      -- Proof component
      (
        ((FinEnum.toList 𝓟.Proof).map fun pf_elem => -- Sum over all right proof components
          C (𝓟.verificationPairingProofRight stmt check_idx pairing pf_elem) -- Coefficient of that element
            *
            -- Times the proof component itself
            𝓟.proof_element_as_poly prover pf_elem).sum
      )
      +
      ( -- SRS component
        ((FinEnum.toList 𝓟.SRSElements).map fun SRS_elem =>
          C (𝓟.verificationPairingSRSRight stmt check_idx pairing SRS_elem) * (𝓟.SRSElementValue SRS_elem)).sum
      )
    )
  )

/-- The value that the verifier checks to be equal to 0 for a given equality check, as a
CMvPolynomial in the samples.
-/
def check_poly {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (𝓟 : AGMProofSystemInstantiationTypeI F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) (check_idx : 𝓟.EqualityChecks) :
    CMvPolynomial 𝓟.Sample F :=
  (
  (FinEnum.toList (𝓟.Pairings check_idx)).map fun pairing =>
    𝓟.pairing_poly prover stmt check_idx pairing
  ).sum


def verify {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (𝓟 : AGMProofSystemInstantiationTypeI F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) : Prop :=
  ∀ check_idx : 𝓟.EqualityChecks, 𝓟.check_poly prover stmt check_idx = 0


def soundness (F : Type) [Field F] [BEq F] [LawfulBEq F]
    (𝓟 : AGMProofSystemInstantiationTypeI F)
    (Wit : Type) (relation : 𝓟.Stmt -> Wit -> Prop)
    (extractor : 𝓟.Prover -> Wit) : Prop :=
   ∀ stmt : 𝓟.Stmt,
    ∀ prover : 𝓟.Prover,
      𝓟.verify prover stmt -> relation stmt (extractor prover)


def completeness (F : Type) [Field F] [BEq F] [LawfulBEq F]
    (𝓟 : AGMProofSystemInstantiationTypeI F) (Wit : Type)
    (relation : 𝓟.Stmt -> Wit -> Prop)
    (prover : 𝓟.Stmt -> Wit -> 𝓟.Prover) : Prop :=
   ∀ stmt : 𝓟.Stmt,
    ∀ wit : Wit,
      relation stmt wit -> 𝓟.verify (prover stmt wit) stmt

end AGMProofSystemInstantiationTypeI

end
