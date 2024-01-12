
-- -- import FormalSnarksProject.Models.AGMProofSystemInstantiation
import Mathlib


example [Field F] (a b c : F)  (h : a ^ ((10 : Fin 37) : Nat) = b) (h2 : b = c) :
    a ^ ((10 : Fin 37) : Nat) * b = b * c := by
  linear_combination c * h + a ^ ((10 : Fin 37) : ℕ) * h2





-- open scoped BigOperators Classical

-- @[simp] theorem Fin.zero_eq_zero : (0 : Fin (n + 1)) = (0 : Fin (Nat.succ n)):= rfl

-- def f (x : Fin 4) : Nat :=
--   match x with
--   | ⟨0, _⟩ => 1
--   | ⟨1, _⟩ => 2
--   | ⟨2, _⟩ => 3
--   | ⟨3, _⟩ => 4

-- def g (h : 9 = ∑ x : Fin 4, f x) : false := by
--   simp_rw [f] at h
--   simp_rw [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
--   norm_num at h








-- structure FooBar where
--   MyType : Type

--   MyFirstTypeFintype : Field MyFirstType

--   val1 : MyType
--   val2 : MyType


-- def FooBar.baz (x : FooBar) : Prop :=
--     x.val1 * 2 = x.val2





-- -- import Mathlib.Algebra.Polynomial.BigOperators
-- -- import Mathlib.Data.MvPolynomial.CommRing
-- -- import Mathlib.Logic.Equiv.Fin
-- -- import Mathlib.Data.MvPolynomial.Rename
-- -- import Mathlib.Data.MvPolynomial.Variables
-- -- import Mathlib.Data.MvPolynomial.Monad
-- -- import Mathlib.Algebra.BigOperators.Basic


-- -- open scoped BigOperators Classical

-- -- section


-- -- structure FooBar where
-- --   MyType : Type

-- --   MyFirstTypeFintype : Field MyFirstType

-- --   val1 : MyType
-- --   val2 : MyType


-- -- def FooBar.baz (x : FooBar) : Prop :=
-- --     x.val1 * 2 = x.val2



-- -- structure AGMProofSystemInstantiation (F : Type) [Field F] where
-- --   /-- The type of statements -/
-- --   Stmt : Type
-- --   /-- The type indexing toxic waste elements sampled -/
-- --   Sample : Type
-- --   /-- The type indexing crs elements in group I, -/
-- --   CrsElements_Left : Type
-- --   /-- Similarly -/
-- --   CrsElements_Right : Type

-- --   /-- The crs elements themselves, described as polynomials in the samples -/
-- --   crsElementValue_Left : (i : CrsElements_Left) → MvPolynomial (Sample) F
-- --   crsElementValue_Right : (i : CrsElements_Right) → MvPolynomial (Sample) F

-- --   /-- A type indexing proof elements in each group -/
-- --   Proof_Left : Type
-- --   [FintypeProof_Left : Fintype Proof_Left]
-- --   Proof_Right : Type

-- --   /-- The type indexing equations the verifier checks -/
-- --   EqualityChecks : Type

-- --   /-- The pairings that the verifier computes for each equation
-- --   (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
-- --   PairingsIdx : EqualityChecks → Type

-- --   pairings : (k : EqualityChecks) → Finset (PairingsIdx k)

-- --   /-- The coefficient that the verifier uses for the jth element of the ith component of the CRSI
-- --   in the left half of the lth paring of the kth equality check -/
-- --   verificationPairingCRSLeft : Stmt -> (k : EqualityChecks) → (l : (PairingsIdx k)) → (i : CrsElements_Left) → F
-- --   /-- The coefficient that the verifier uses for the jth element of the ith component of the CRSII
-- --   in the right half of the lth paring of the kth equality check  -/
-- --   verificationPairingCRSRight : Stmt -> (k : EqualityChecks) → (l : (PairingsIdx k)) → (i : CrsElements_Right) → F
-- --   /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_Left
-- --   in the left half of the lth paring of the kth equality check -/
-- --   verificationPairingProofLeft : Stmt -> (k : EqualityChecks) → (l : (PairingsIdx k)) → (i : Proof_Left) → F
-- --   /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_Right
-- --   in the right half of the lth paring of the kth equality check  -/
-- --   verificationPairingProofRight : Stmt -> (k : EqualityChecks) → (l : (PairingsIdx k)) → (i : Proof_Right) → F

-- -- /-- The type of possible provers in the AGM model.
-- -- A prover simply assigns, for each proof element and each crs element from the group of that proof element, a coefficient. -/
-- -- def AGMProofSystemInstantiation.Prover (F : Type) [Field F]
-- --     (𝓟 : AGMProofSystemInstantiation F) : Type :=
-- --   (𝓟.Proof_Left -> 𝓟.CrsElements_Left -> F) × (𝓟.Proof_Right -> 𝓟.CrsElements_Right -> F)

-- -- def AGMProofSystemInstantiation.verify {F : Type} [Field F]
-- --     (𝓟 : AGMProofSystemInstantiation F) (prover : 𝓟.Prover) (stmt : 𝓟.Stmt) : Prop :=
-- --   ∀ check_idx : 𝓟.EqualityChecks,
-- --     ∑ pairing in (𝓟.pairings check_idx),
-- --       ( -- LHS of pairing
-- --         -- Proof component
-- --         (
-- --           ∑ pf_elem : 𝓟.FintypeProof_Left.elems, 0
-- --             -- ∑ crs_elem : CrsElements_Left,
-- --             --   (prover.fst pf_elem crs_elem) * (𝓟.verificationPairingProofLeft stmt check_idx pairing pf_elem)
-- --         )
-- --         +
-- --         ( -- CRS component
-- --           -- ∑ crs_elem : CrsElements_Left,
-- --           --   (𝓟.crsElementValue_Left crs_elem) * (𝓟.verificationPairingCRSLeft stmt check_idx pairing crs_elem)
-- --           0
-- --         )
-- --       )
-- --     = 0



-- -- end
