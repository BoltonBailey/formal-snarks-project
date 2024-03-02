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
-- TODO I -> Left and II -> Right
-- TODO before all this, finalize the terminology for the various levels of instantiation.
-- TODO make a structure that doesn't track components/linear extractor
--    then make another structure that returns AGMProofSystemv2

/-- A structure representing an AGM proof system similar to AGMProofSystemInstantiation, but using Fin rather than arbitrary types -/
structure AGMProofSystemInstantiationFin (F : Type) [Field F] where
  /-- The number of toxic waste elements sampled -/
  nSample : ℕ
  /-- The number of SRS elements in group I, -/
  nSRSElements_G1 : ℕ
  /-- Similarly -/
  nSRSElements_G2 : ℕ

  /-- The SRS elements themselves, described as polynomials in the samples -/
  SRSElementValue_G1 : (i : Fin nSRSElements_G1) → MvPolynomial (Fin nSample) F
  SRSElementValue_G2 : (i : Fin nSRSElements_G2) → MvPolynomial (Fin nSample) F

  /-- A number of proof elements in each group -/
  nProof_G1 : ℕ
  nProof_G2 : ℕ

  /-- The number of equations the verifier checks -/
  nEqualityChecks : ℕ

  /-- The pairings that the verifier computes for each equation
  (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  nPairings : Fin nEqualityChecks → ℕ

  /-- The coefficient that the verifier uses for the jth element of the ith component of the SRSI
  in the left half of the lth paring of the kth equality check -/
  verificationPairingSRS_G1 : (i : Fin nSRSElements_G1)
                                → (k : Fin nEqualityChecks) → (l : Fin (nPairings k)) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the SRSII
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingSRS_G2 : (i : Fin nSRSElements_G2)
                                → (k : Fin nEqualityChecks) → (l : Fin (nPairings k)) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_G1
  in the left half of the lth paring of the kth equality check -/
  verificationPairingProof_G1 : (i : Fin nProof_G1)
                                → (k : Fin nEqualityChecks) → (l : Fin (nPairings k)) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_G2
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingProof_G2 : (i : Fin nProof_G2)
                                → (k : Fin nEqualityChecks) → (l : Fin (nPairings k)) → F


-- def finSplit (a b : ℕ) (x : Fin (a + b)) : Sum (Fin a) (Fin b) :=
--   by
--     refine Sum.inr ?val


structure AGMProofSystemInstantiationIndexForm (F : Type) [Field F] where
  /-- The type of statements -/
  Stmt : Type
  /-- The type indexing toxic waste elements sampled -/
  Sample : Type
  /-- The type indexing SRS elements in group I, -/
  SRSElements_G1 : Type
  /-- Similarly -/
  SRSElements_G2 : Type

  /-- The SRS elements themselves, described as polynomials in the samples -/
  SRSElementValue_G1 : (i : SRSElements_G1) → MvPolynomial (Sample) F
  SRSElementValue_G2 : (i : SRSElements_G2) → MvPolynomial (Sample) F

  /-- A type indexing proof elements in each group -/
  Proof_G1 : Type
  Proof_G2 : Type

  /-- The type indexing equations the verifier checks -/
  EqualityChecks : Type

  /-- The pairings that the verifier computes for each equation
  (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  Pairings : EqualityChecks → Type

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
