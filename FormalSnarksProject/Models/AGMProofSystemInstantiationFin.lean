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
  /-- The number of crs elements in group I, -/
  nCrsElements_Left : ℕ
  /-- Similarly -/
  nCrsElements_Right : ℕ

  /-- The crs elements themselves, described as polynomials in the samples -/
  crsElementValue_Left : (i : Fin nCrsElements_Left) → MvPolynomial (Fin nSample) F
  crsElementValue_Right : (i : Fin nCrsElements_Right) → MvPolynomial (Fin nSample) F

  /-- A number of proof elements in each group -/
  nProof_Left : ℕ
  nProof_Right : ℕ

  /-- The number of equations the verifier checks -/
  nEqualityChecks : ℕ

  /-- The pairings that the verifier computes for each equation
  (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  nPairings : Fin nEqualityChecks → ℕ

  /-- The coefficient that the verifier uses for the jth element of the ith component of the CRSI
  in the left half of the lth paring of the kth equality check -/
  verificationPairingCRSLeft : (i : Fin nCrsElements_Left)
                                → (k : Fin nEqualityChecks) → (l : Fin (nPairings k)) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the CRSII
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingCRSRight : (i : Fin nCrsElements_Right)
                                → (k : Fin nEqualityChecks) → (l : Fin (nPairings k)) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_Left
  in the left half of the lth paring of the kth equality check -/
  verificationPairingProofLeft : (i : Fin nProof_Left)
                                → (k : Fin nEqualityChecks) → (l : Fin (nPairings k)) → F
  /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_Right
  in the right half of the lth paring of the kth equality check  -/
  verificationPairingProofRight : (i : Fin nProof_Right)
                                → (k : Fin nEqualityChecks) → (l : Fin (nPairings k)) → F


-- def finSplit (a b : ℕ) (x : Fin (a + b)) : Sum (Fin a) (Fin b) :=
--   by
--     refine Sum.inr ?val


structure AGMProofSystemInstantiationIndexForm (F : Type) [Field F] where
  /-- The type of statements -/
  Stmt : Type
  /-- The type indexing toxic waste elements sampled -/
  Sample : Type
  /-- The type indexing crs elements in group I, -/
  CrsElements_Left : Type
  /-- Similarly -/
  CrsElements_Right : Type

  /-- The crs elements themselves, described as polynomials in the samples -/
  crsElementValue_Left : (i : CrsElements_Left) → MvPolynomial (Sample) F
  crsElementValue_Right : (i : CrsElements_Right) → MvPolynomial (Sample) F

  /-- A type indexing proof elements in each group -/
  Proof_Left : Type
  Proof_Right : Type

  /-- The type indexing equations the verifier checks -/
  EqualityChecks : Type

  /-- The pairings that the verifier computes for each equation
  (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  Pairings : EqualityChecks → Type

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
