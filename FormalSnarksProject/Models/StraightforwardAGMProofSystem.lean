import FormalSnarksProject.Models.AGMProofSystemInstantiation



/-!
This structure captures the requirements to be a straightforward linear PCP SNARK scheme.
Any straightforward linear PCP SNARK scheme can be provided with a field and additional data
representing a circuit or problem instance to return a `AGMProofSystemInstantiation`.

The `AGMProofSystemInstantiation` returned by this function has the following properties:

* the circuit representation consists of a list of naturals, along with a number of vectors of Polynomials, where each vector has a length coming from a particular element of the list.
* the statment and witness types are vectors of field elements, where the length of the vectors is determined by the first and second elements of the list.
* The sample space for toxic waste elements is an Option type
* All some _ values appears to unbounded degree in the SRS elements
* The index types into the left and right halves of the SRS are comprised of `Sum` types over components,
  * Each of these components is a Unit or Fin types
  * Each corresponding component of the SRS has the form of a sum of MvPolynomials,
    * Each component of that sum consists of a product of
      * (some _) type toxic waste elements
      * Polynomials from the vectors provided in the circuit description (cast to MvPolynomials).
* The arities of SRS and proof elements in the pairings are
  * constant over components,
  * or are given by the stmt for SRS components whose length is the same as the statement length

-/

-- TODO SRS vs SRS

structure StraightforwardAGMProofSystem where
  /-- Auxiliary data for the system -/
  Aux : Type
  /-- Index into bounded-degree toxic waste elements -/
  Vars : Type
  /-- Bound on the degree of those elements -/
  degreeBound : Vars → ℕ

  /-- The number of components in left-group SRS -/
  nSRSComponents_G1 : ℕ
  /-- The lengths of components of the SRS, in terms of the stmt and wit lengths and aux data -/
  SRSElements_G1_Lengths : Fin nSRSComponents_G1 -> ℕ -> ℕ -> Aux -> ℕ
  /-- Similarly -/
  nSRSComponents_G2 : ℕ
  SRSElements_G2_Lengths : Fin nSRSComponents_G2 -> ℕ -> ℕ -> Aux -> ℕ

  -- /-- The SRS elements themselves, described as polynomials in the samples -/
  -- SRSElementValue_G1 : (i : SRSElements_G1) → MvPolynomial (Sample) F
  -- SRSElementValue_G2 : (i : SRSElements_G2) → MvPolynomial (Sample) F

  -- /-- A type indexing proof elements in each group -/
  -- Proof_G1 : Type
  -- ListProof_G1 : List Proof_G1
  -- Proof_G2 : Type
  -- ListProof_G2 : List Proof_G2

  -- /-- The type indexing equations the verifier checks -/
  -- EqualityChecks : Type

  -- /-- The pairings that the verifier computes for each equation
  -- (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  -- Pairings : EqualityChecks → Type

  -- ListPairings : (k : EqualityChecks) → List (Pairings k)

  -- /-- The coefficient that the verifier uses for the jth element of the ith component of the SRSI
  -- in the left half of the lth paring of the kth equality check -/
  -- verificationPairingSRS_G1 : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : SRSElements_G1) → F
  -- /-- The coefficient that the verifier uses for the jth element of the ith component of the SRSII
  -- in the right half of the lth paring of the kth equality check  -/
  -- verificationPairingSRS_G2 : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : SRSElements_G2) → F
  -- /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_G1
  -- in the left half of the lth paring of the kth equality check -/
  -- verificationPairingProof_G1 : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : Proof_G1) → F
  -- /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_G2
  -- in the right half of the lth paring of the kth equality check  -/
  -- verificationPairingProof_G2 : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : Proof_G2) → F

/-- Maps [1, 2, 3] to
[,
 ((List.finRange 1).map fun i => (.inr (.inl i))) ,
 ((List.finRange 1).map fun i => (.inr (.inr (.inl i)))) ,
 ((List.finRange 1).map fun i => (.inr (.inr (.inr (.inl i)))))
]
-/
def compile_Fin_list (l : List ℕ) : List (Fin (l.length)) := sorry


def StraightforwardAGMProofSystem.toAGMProofSystem (F : Type) [Field F] (n_stmt n_wit : ℕ)
    (𝓟 : StraightforwardAGMProofSystem) (aux : 𝓟.Aux) : AGMProofSystemInstantiation F := sorry




def StraightforwardAGMProofSystem.soundness (F : Type) [Field F] (n_stmt n_wit : ℕ)
    (𝓟 : StraightforwardAGMProofSystem) : Prop := sorry
    -- ∀ stmt : Fin n_stmt → F,
    --   ∀ agm : proof_elems_index → Fin n_SRS → F,
    --     ((-- if all checks on the proof pass, the extracted witness must satisfy the relation
    --         -- (∀ f : (fin n_sample) → F,
    --         -- (∀ s : fin n_sample, f s ≠ 0) →
    --         ∀ c ∈ polynomial_checks,
    --           (MvPolynomial.bind₁
    --               (fun pf_idx => ∑ SRS_idx : Fin n_SRS, agm pf_idx SRS_idx • SRS_elems SRS_idx) :
    --               MvPolynomial proof_elems_index F -> MvPolynomial (Fin n_sample) F) c =
    --             0) ∧
    --         ∀ idx : proof_elems_index,
    --           ∀ val ∈ proof_element_checks idx,
    --             (val : (Fin n_stmt → F) → Fin n_SRS → F) stmt = agm idx) →
    --       relation stmt (extractor agm)





-- -- relation_parameters : A set of paramters for the relation. for R1CS, this is the matrix A, B, C
-- structure StraightforwardAGMProofSystem'  (F : Type) [Field F] (relation_parameters : Type) where

--   relation : (Fin n_stmt → F) → (Fin n_wit → F) → Prop
--   nSample : ℕ
--   nSRS : ℕ
--   SRS_elems : Fin n_SRS → MvPolynomial (Fin n_sample) F


-- def StraightforwardAGMProofSystem.toAGMProofSystem
