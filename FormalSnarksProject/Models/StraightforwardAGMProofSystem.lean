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
* The index types into the left and right halves of the CRS are comprised of `Sum` types over components,
  * Each of these components is a Unit or Fin types
  * Each corresponding component of the CRS has the form of a sum of MvPolynomials,
    * Each component of that sum consists of a product of
      * (some _) type toxic waste elements
      * Polynomials from the vectors provided in the circuit description (cast to MvPolynomials).
* The arities of SRS and proof elements in the pairings are
  * constant over components,
  * or are given by the stmt for SRS components whose length is the same as the statement length

-/

-- TODO CRS vs SRS

structure StraightforwardAGMProofSystem where
  /-- Auxiliary data for the system -/
  Aux : Type
  /-- Index into bounded-degree toxic waste elements -/
  Vars : Type
  /-- Bound on the degree of those elements -/
  degreeBound : Vars → ℕ

  /-- The number of components in left-group SRS -/
  nCrsComponents_Left : ℕ
  /-- The lengths of components of the SRS, in terms of the stmt and wit lengths and aux data -/
  CrsElements_Left_Lengths : Fin nCrsComponents_Left -> ℕ -> ℕ -> Aux -> ℕ
  /-- Similarly -/
  nCrsComponents_Right : ℕ
  CrsElements_Right_Lengths : Fin nCrsComponents_Right -> ℕ -> ℕ -> Aux -> ℕ

  -- /-- The crs elements themselves, described as polynomials in the samples -/
  -- crsElementValue_Left : (i : CrsElements_Left) → MvPolynomial (Sample) F
  -- crsElementValue_Right : (i : CrsElements_Right) → MvPolynomial (Sample) F

  -- /-- A type indexing proof elements in each group -/
  -- Proof_Left : Type
  -- ListProof_Left : List Proof_Left
  -- Proof_Right : Type
  -- ListProof_Right : List Proof_Right

  -- /-- The type indexing equations the verifier checks -/
  -- EqualityChecks : Type

  -- /-- The pairings that the verifier computes for each equation
  -- (each equation is treated as a sum of pairings, the result of which is compared to zero) -/
  -- Pairings : EqualityChecks → Type

  -- ListPairings : (k : EqualityChecks) → List (Pairings k)

  -- /-- The coefficient that the verifier uses for the jth element of the ith component of the CRSI
  -- in the left half of the lth paring of the kth equality check -/
  -- verificationPairingCRSLeft : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : CrsElements_Left) → F
  -- /-- The coefficient that the verifier uses for the jth element of the ith component of the CRSII
  -- in the right half of the lth paring of the kth equality check  -/
  -- verificationPairingCRSRight : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : CrsElements_Right) → F
  -- /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_Left
  -- in the left half of the lth paring of the kth equality check -/
  -- verificationPairingProofLeft : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : Proof_Left) → F
  -- /-- The coefficient that the verifier uses for the jth element of the ith component of the Proof_Right
  -- in the right half of the lth paring of the kth equality check  -/
  -- verificationPairingProofRight : Stmt -> (k : EqualityChecks) → (l : (Pairings k)) → (i : Proof_Right) → F

/-- Maps [1, 2, 3] to
[,
 ((List.finRange 1).map fun i => (.inr (.inl i))) ,
 ((List.finRange 1).map fun i => (.inr (.inr (.inl i)))) ,
 ((List.finRange 1).map fun i => (.inr (.inr (.inr (.inl i)))))
]
-/
def compile_Fin_list (l : List ℕ) : List (Fin (l.length)) := sorry


def StraightforwardAGMProofSystem.toAGMProofSystem (F : Type) [Field F] (n_stmt n_wit : ℕ)
    (𝓟 : StraightforwardAGMProofSystem) (aux : 𝓟.Aux) : AGMProofSystemInstantiation F where
  Stmt := Fin n_stmt -> F
  Sample := Option 𝓟.Vars
  CrsElements_Left := List.foldl Sum Empty ((𝓟.CrsElements_Left_Lengths n_stmt n_wit aux).map Fin)
  ListCrsElements_Left := List.foldl List.append [] (_)
  CrsElements_Right := _
  ListCrsElements_Right := _
  crsElementValue_Left := _
  crsElementValue_Right := _
  Proof_Left := _
  ListProof_Left := _
  Proof_Right := _
  ListProof_Right := _
  EqualityChecks := _
  Pairings := _
  ListPairings := _
  verificationPairingCRSLeft := _
  verificationPairingCRSRight := _
  verificationPairingProofLeft := _
  verificationPairingProofRight := _




def StraightforwardAGMProofSystem.soundness (F : Type) [Field F] (n_stmt n_wit : ℕ)
    (𝓟 : StraightforwardAGMProofSystem F n_stmt n_wit) : Prop := sorry
    -- ∀ stmt : Fin n_stmt → F,
    --   ∀ agm : proof_elems_index → Fin n_crs → F,
    --     ((-- if all checks on the proof pass, the extracted witness must satisfy the relation
    --         -- (∀ f : (fin n_sample) → F,
    --         -- (∀ s : fin n_sample, f s ≠ 0) →
    --         ∀ c ∈ polynomial_checks,
    --           (MvPolynomial.bind₁
    --               (fun pf_idx => ∑ crs_idx : Fin n_crs, agm pf_idx crs_idx • crs_elems crs_idx) :
    --               MvPolynomial proof_elems_index F -> MvPolynomial (Fin n_sample) F) c =
    --             0) ∧
    --         ∀ idx : proof_elems_index,
    --           ∀ val ∈ proof_element_checks idx,
    --             (val : (Fin n_stmt → F) → Fin n_crs → F) stmt = agm idx) →
    --       relation stmt (extractor agm)





-- -- relation_parameters : A set of paramters for the relation. for R1CS, this is the matrix A, B, C
-- structure StraightforwardAGMProofSystem'  (F : Type) [Field F] (relation_parameters : Type) where

--   relation : (Fin n_stmt → F) → (Fin n_wit → F) → Prop
--   nSample : ℕ
--   nCrs : ℕ
--   crs_elems : Fin n_crs → MvPolynomial (Fin n_sample) F


-- def StraightforwardAGMProofSystem.toAGMProofSystem
