import FormalSnarksProject.Models.AGMProofSystemInstantiation
import FormalSnarksProject.ToMathlib.FinEnumOrd
import CompPoly.OrdMultivariate.COrdMvPolynomialEvalLemmas
import CompPoly.OrdMultivariate.Operations

open CPoly
open CPoly.COrdMvPolynomial

/-!
# Straightforward linear PCP SNARK schemes

This file formalizes the class of *straightforward linear PCP SNARK schemes* from
["Formalizing Soundness Proofs of Linear PCP SNARKs", Bailey and Miller, USENIX Security '24](https://www.usenix.org/conference/usenixsecurity24/presentation/bailey).

A `StraightforwardAGMProofSystem` is a *scheme* (general over problem instances), as opposed to an
`AGMProofSystemInstantiation`, which is a SNARK for one particular circuit/instance. The paper
observes that every linear PCP SNARK scheme it is aware of belongs to this class, and that the class
is regular enough to admit an automated soundness decision procedure. `toAGMProofSystem` realizes a
scheme on a concrete instance (a piece of auxiliary circuit data `aux : Aux`, which determines the
statement size), producing an `AGMProofSystemInstantiation`.

The straightforward shape, as captured here, is:

* the sample space for toxic-waste elements is `Option Vars`, where `Vars` indexes the
  bounded-degree samples (with bound `degreeBound`) and `none` is the distinguished unbounded sample;
* the statement is a vector of field elements `Fin (Stmt_Size aux) → F`, with the size determined by
  the circuit data;
* the SRS element index of each group is split into a fixed family of *components*
  (`SRSComponents_G*`), each component being a `Fin`-indexed family whose length is a function of the
  instance — so the index is `Σ c : SRSComponents_G*, Fin (SRSElements_G*_Lengths c aux)`;
* each SRS element is a multivariate polynomial over the samples (`COrdMvPolynomial (Option Vars) F`),
  in practice a sum of products of toxic-waste monomials with circuit polynomials cast into the
  sample ring;
* the proof elements, equality checks, and pairings are arbitrary finite index types;
* the verifier's pairing coefficients are field elements depending on the statement.
-/

/-- A straightforward linear PCP SNARK scheme over the field `F`. Instantiating it on a piece of
auxiliary circuit data yields an `AGMProofSystemInstantiation` (see `toAGMProofSystem`). -/
structure StraightforwardAGMProofSystem (F : Type) [Field F] [BEq F] [LawfulBEq F] where
  /-- Auxiliary (circuit / problem-instance) data the scheme is instantiated with. -/
  Aux : Type
  /-- Index into the bounded-degree toxic-waste elements. The distinguished unbounded sample is the
  extra `none` introduced by `Option Vars`. -/
  Vars : Type
  [Vars_FinEnum : FinEnum Vars]
  [Vars_Ord : Ord Vars]
  [Vars_TransOrd : Std.TransOrd Vars]
  [Vars_LawfulEqOrd : Std.LawfulEqOrd Vars]
  /-- Bound on the degree to which each bounded sample appears in the SRS. -/
  degreeBound : Vars → ℕ
  /-- The statement size (number of public field elements), read off the circuit data. -/
  Stmt_Size : Aux → ℕ

  /-- The components into which the left-group (`G1`) SRS index is split. -/
  SRSComponents_G1 : Type
  [SRSComponents_G1_FinEnum : FinEnum SRSComponents_G1]
  /-- The length of each `G1` SRS component, as a function of the auxiliary data. -/
  SRSElements_G1_Lengths : SRSComponents_G1 → Aux → ℕ
  /-- Similarly for the right group `G2`. -/
  SRSComponents_G2 : Type
  [SRSComponents_G2_FinEnum : FinEnum SRSComponents_G2]
  SRSElements_G2_Lengths : SRSComponents_G2 → Aux → ℕ

  /-- The value of the `j`th element of the `c` `G1` SRS component, as a multivariable polynomial in
  the samples `Option Vars`. -/
  SRSElementValue_G1 : (aux : Aux) → (c : SRSComponents_G1) →
    Fin (SRSElements_G1_Lengths c aux) → COrdMvPolynomial (Option Vars) F
  /-- Similarly for `G2`. -/
  SRSElementValue_G2 : (aux : Aux) → (c : SRSComponents_G2) →
    Fin (SRSElements_G2_Lengths c aux) → COrdMvPolynomial (Option Vars) F

  /-- A type indexing proof elements in the left group. -/
  Proof_G1 : Type
  [Proof_G1_FinEnum : FinEnum Proof_G1]
  /-- A type indexing proof elements in the right group. -/
  Proof_G2 : Type
  [Proof_G2_FinEnum : FinEnum Proof_G2]
  /-- A type indexing the equality checks the verifier makes. -/
  EqualityChecks : Type
  [EqualityChecks_FinEnum : FinEnum EqualityChecks]
  /-- The pairings summed in each equality check. -/
  Pairings : EqualityChecks → Type
  [Pairings_FinEnum : (k : EqualityChecks) → FinEnum (Pairings k)]
  /-- The coefficient the verifier applies to the `j`th element of the `c` `G1` SRS component in the
  left half of the given pairing of the given equality check. -/
  verificationPairingSRS_G1 : (aux : Aux) → (Fin (Stmt_Size aux) → F) →
    (k : EqualityChecks) → Pairings k →
    (c : SRSComponents_G1) → Fin (SRSElements_G1_Lengths c aux) → F
  /-- Similarly for the right half / `G2` SRS. -/
  verificationPairingSRS_G2 : (aux : Aux) → (Fin (Stmt_Size aux) → F) →
    (k : EqualityChecks) → Pairings k →
    (c : SRSComponents_G2) → Fin (SRSElements_G2_Lengths c aux) → F
  /-- The coefficient the verifier applies to a `G1` proof element in the left half of a pairing. -/
  verificationPairingProof_G1 : (aux : Aux) → (Fin (Stmt_Size aux) → F) →
    (k : EqualityChecks) → Pairings k → Proof_G1 → F
  /-- The coefficient the verifier applies to a `G2` proof element in the right half of a pairing. -/
  verificationPairingProof_G2 : (aux : Aux) → (Fin (Stmt_Size aux) → F) →
    (k : EqualityChecks) → Pairings k → Proof_G2 → F

namespace StraightforwardAGMProofSystem

attribute [instance]
  StraightforwardAGMProofSystem.Vars_FinEnum
  StraightforwardAGMProofSystem.Vars_Ord
  StraightforwardAGMProofSystem.Vars_TransOrd
  StraightforwardAGMProofSystem.Vars_LawfulEqOrd
  StraightforwardAGMProofSystem.SRSComponents_G1_FinEnum
  StraightforwardAGMProofSystem.SRSComponents_G2_FinEnum
  StraightforwardAGMProofSystem.Proof_G1_FinEnum
  StraightforwardAGMProofSystem.Proof_G2_FinEnum
  StraightforwardAGMProofSystem.EqualityChecks_FinEnum
  StraightforwardAGMProofSystem.Pairings_FinEnum

/-- Instantiate a straightforward scheme on a concrete auxiliary circuit datum `aux`, producing an
`AGMProofSystemInstantiation`.

The SRS index types are realized as `Sigma` types over the components, which carry `FinEnum`
instances automatically (from the `FinEnum` instances on the component types and on `Fin`). -/
noncomputable def toAGMProofSystem {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (𝓟 : StraightforwardAGMProofSystem F) (aux : 𝓟.Aux) :
    AGMProofSystemInstantiation F where
  Stmt := Fin (𝓟.Stmt_Size aux) → F
  Sample := Option 𝓟.Vars
  SRSElements_G1 := Σ c : 𝓟.SRSComponents_G1, Fin (𝓟.SRSElements_G1_Lengths c aux)
  SRSElements_G2 := Σ c : 𝓟.SRSComponents_G2, Fin (𝓟.SRSElements_G2_Lengths c aux)
  SRSElementValue_G1 := fun srs => 𝓟.SRSElementValue_G1 aux srs.1 srs.2
  SRSElementValue_G2 := fun srs => 𝓟.SRSElementValue_G2 aux srs.1 srs.2
  Proof_G1 := 𝓟.Proof_G1
  Proof_G2 := 𝓟.Proof_G2
  EqualityChecks := 𝓟.EqualityChecks
  Pairings := 𝓟.Pairings
  verificationPairingSRS_G1 := fun stmt k pairing srs =>
    𝓟.verificationPairingSRS_G1 aux stmt k pairing srs.1 srs.2
  verificationPairingSRS_G2 := fun stmt k pairing srs =>
    𝓟.verificationPairingSRS_G2 aux stmt k pairing srs.1 srs.2
  verificationPairingProof_G1 := fun stmt k pairing pf =>
    𝓟.verificationPairingProof_G1 aux stmt k pairing pf
  verificationPairingProof_G2 := fun stmt k pairing pf =>
    𝓟.verificationPairingProof_G2 aux stmt k pairing pf
  Identified_Proof_Elems := []

/-- Knowledge-soundness of a straightforward scheme on a concrete instance, defined by delegating to
`AGMProofSystemInstantiation.soundness` for the instantiated proof system. -/
def soundness {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (𝓟 : StraightforwardAGMProofSystem F) (aux : 𝓟.Aux)
    (Wit : Type) (relation : (Fin (𝓟.Stmt_Size aux) → F) → Wit → Prop)
    (extractor : AGMProofSystemInstantiation.Prover F (𝓟.toAGMProofSystem aux) → Wit) : Prop :=
  AGMProofSystemInstantiation.soundness F (𝓟.toAGMProofSystem aux) Wit relation extractor

/-- Completeness of a straightforward scheme on a concrete instance, defined by delegating to
`AGMProofSystemInstantiation.completeness` for the instantiated proof system. -/
def completeness {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (𝓟 : StraightforwardAGMProofSystem F) (aux : 𝓟.Aux)
    (Wit : Type) (relation : (Fin (𝓟.Stmt_Size aux) → F) → Wit → Prop)
    (prover : (Fin (𝓟.Stmt_Size aux) → F) → Wit →
      AGMProofSystemInstantiation.Prover F (𝓟.toAGMProofSystem aux)) : Prop :=
  AGMProofSystemInstantiation.completeness F (𝓟.toAGMProofSystem aux) Wit relation prover

end StraightforwardAGMProofSystem

/-!
## Reduction to a polynomial ideal-membership problem

Following the paper, the soundness of a (straightforward) linear PCP SNARK reduces to a polynomial
ideal-membership problem. In the AGM, every proof element is a linear combination of the SRS
elements with *unknown* field coefficients; we make those coefficients formal indeterminates
(`ProverVars`). Each verifier equality check then becomes a multivariate polynomial over the
toxic-waste samples *and* these indeterminates (`sym_check_poly`). By Schwartz–Zippel the check
passes (over random samples) iff this polynomial is identically zero as a polynomial in the samples,
i.e. iff each of its toxic-waste-monomial coefficients — polynomials in the prover indeterminates —
vanishes. These coefficients are the generators of the soundness ideal; soundness holds iff the
polynomial encoding the relation lies in the ideal they generate.
-/

namespace AGMProofSystemInstantiation

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- The prover's unknown linear-combination coefficients, one per `(proof element, SRS element)`
pair in each group. -/
abbrev ProverVars (𝓟 : AGMProofSystemInstantiation F) : Type :=
  (𝓟.Proof_G1 × 𝓟.SRSElements_G1) ⊕ (𝓟.Proof_G2 × 𝓟.SRSElements_G2)

/-- The indeterminates of the soundness ideal-membership problem: the prover's coefficients
(`ProverVars`) together with the statement entries (`StmtIdx`). Treating the statement entries as
indeterminates is what makes the ideal-membership problem *independent of any particular statement*. -/
abbrev IdealVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type) : Type :=
  𝓟.ProverVars ⊕ StmtIdx

/-- Variables of the symbolic verification polynomial: toxic-waste samples, then the ideal
indeterminates (prover coefficients and statement entries). -/
abbrev SymVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type) : Type :=
  𝓟.Sample ⊕ 𝓟.IdealVars StmtIdx

-- Explicit `FinEnum` instances, so synthesis for the (nested) variable types is immediate rather
-- than re-searching the product/sum structure each time.
instance instFinEnumProverVars (𝓟 : AGMProofSystemInstantiation F) : FinEnum 𝓟.ProverVars :=
  inferInstanceAs (FinEnum ((𝓟.Proof_G1 × 𝓟.SRSElements_G1) ⊕ (𝓟.Proof_G2 × 𝓟.SRSElements_G2)))

instance instFinEnumIdealVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type) [FinEnum StmtIdx] :
    FinEnum (𝓟.IdealVars StmtIdx) :=
  inferInstanceAs (FinEnum (𝓟.ProverVars ⊕ StmtIdx))

instance instFinEnumSymVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type) [FinEnum StmtIdx] :
    FinEnum (𝓟.SymVars StmtIdx) :=
  inferInstanceAs (FinEnum (𝓟.Sample ⊕ 𝓟.IdealVars StmtIdx))

/-! The computable polynomials over the (sum-typed) symbolic variable spaces need a lawful
ordering on the variable type; core provides no `Ord` for sum types, so pull one back from the
`FinEnum` enumeration. -/

instance instOrdIdealVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] : Ord (𝓟.IdealVars StmtIdx) := FinEnum.toOrd
instance instTransOrdIdealVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] : Std.TransOrd (𝓟.IdealVars StmtIdx) := FinEnum.toOrd.transOrd
instance instLawfulEqOrdIdealVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] : Std.LawfulEqOrd (𝓟.IdealVars StmtIdx) := FinEnum.toOrd.lawfulEqOrd

instance instOrdSymVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] : Ord (𝓟.SymVars StmtIdx) := FinEnum.toOrd
instance instTransOrdSymVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] : Std.TransOrd (𝓟.SymVars StmtIdx) := FinEnum.toOrd.transOrd
instance instLawfulEqOrdSymVars (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] : Std.LawfulEqOrd (𝓟.SymVars StmtIdx) := FinEnum.toOrd.lawfulEqOrd

/-- Embed an SRS polynomial (over the samples) into the symbolic ring. -/
noncomputable def symEmbed (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type) [FinEnum StmtIdx]
    (p : COrdMvPolynomial 𝓟.Sample F) : COrdMvPolynomial (𝓟.SymVars StmtIdx) F :=
  rename Sum.inl p

/-- A verifier coefficient `g : (StmtIdx → F) → F`, rendered symbolically as a polynomial in the
statement indeterminates. This is exact when `g` is affine in the statement — which holds for
straightforward schemes (their coefficients are constants or single statement entries). The
reconstruction is `g 0 + ∑ᵢ (g eᵢ - g 0) · Xᵢ`. -/
noncomputable def symStmtCoeff (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] [DecidableEq StmtIdx] (g : (StmtIdx → F) → F) :
    COrdMvPolynomial (𝓟.SymVars StmtIdx) F :=
  COrdMvPolynomial.C (g (fun _ => 0))
    + ((FinEnum.toList StmtIdx).map fun i =>
        COrdMvPolynomial.C (g (fun j => if j = i then 1 else 0) - g (fun _ => 0))
          * X (Sum.inr (Sum.inr i))).sum

/-- The symbolic `G1` proof element: the prover's coefficient on each SRS element is a fresh
indeterminate. -/
noncomputable def sym_proof_element_G1 (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] (pf : 𝓟.Proof_G1) : COrdMvPolynomial (𝓟.SymVars StmtIdx) F :=
  ((FinEnum.toList 𝓟.SRSElements_G1).map fun srs =>
    X (Sum.inr (Sum.inl (Sum.inl (pf, srs)))) * 𝓟.symEmbed StmtIdx (𝓟.SRSElementValue_G1 srs)).sum

/-- The symbolic `G2` proof element. -/
noncomputable def sym_proof_element_G2 (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] (pf : 𝓟.Proof_G2) : COrdMvPolynomial (𝓟.SymVars StmtIdx) F :=
  ((FinEnum.toList 𝓟.SRSElements_G2).map fun srs =>
    X (Sum.inr (Sum.inl (Sum.inr (pf, srs)))) * 𝓟.symEmbed StmtIdx (𝓟.SRSElementValue_G2 srs)).sum

/-- The symbolic pairing value, with the prover's proof elements replaced by their symbolic
(indeterminate-coefficient) versions and the verifier's coefficients made symbolic in the statement
via `symStmtCoeff`. `toStmt` recovers the proof system's statement type from a vector of statement
entries (the identity for the straightforward schemes, whose statement is already `StmtIdx → F`). -/
noncomputable def sym_pairing_poly (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] [DecidableEq StmtIdx] (toStmt : (StmtIdx → F) → 𝓟.Stmt)
    (k : 𝓟.EqualityChecks) (pairing : 𝓟.Pairings k) : COrdMvPolynomial (𝓟.SymVars StmtIdx) F :=
  (((FinEnum.toList 𝓟.Proof_G1).map fun pf =>
        𝓟.symStmtCoeff StmtIdx (fun s => 𝓟.verificationPairingProof_G1 (toStmt s) k pairing pf)
          * 𝓟.sym_proof_element_G1 StmtIdx pf).sum
    + ((FinEnum.toList 𝓟.SRSElements_G1).map fun srs =>
        𝓟.symStmtCoeff StmtIdx (fun s => 𝓟.verificationPairingSRS_G1 (toStmt s) k pairing srs)
          * 𝓟.symEmbed StmtIdx (𝓟.SRSElementValue_G1 srs)).sum)
  * (((FinEnum.toList 𝓟.Proof_G2).map fun pf =>
        𝓟.symStmtCoeff StmtIdx (fun s => 𝓟.verificationPairingProof_G2 (toStmt s) k pairing pf)
          * 𝓟.sym_proof_element_G2 StmtIdx pf).sum
    + ((FinEnum.toList 𝓟.SRSElements_G2).map fun srs =>
        𝓟.symStmtCoeff StmtIdx (fun s => 𝓟.verificationPairingSRS_G2 (toStmt s) k pairing srs)
          * 𝓟.symEmbed StmtIdx (𝓟.SRSElementValue_G2 srs)).sum)

/-- The symbolic verification polynomial for one equality check: a polynomial over the toxic-waste
samples and the ideal indeterminates whose vanishing (over random samples) is the verifier check. -/
noncomputable def sym_check_poly (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] [DecidableEq StmtIdx] (toStmt : (StmtIdx → F) → 𝓟.Stmt)
    (k : 𝓟.EqualityChecks) : COrdMvPolynomial (𝓟.SymVars StmtIdx) F :=
  ((FinEnum.toList (𝓟.Pairings k)).map fun pairing =>
    𝓟.sym_pairing_poly StmtIdx toStmt k pairing).sum

/-- Accumulate `(key, value)` pairs into an association list, adding values that share a key. Used to
group the symbolic check polynomial's terms by their toxic-waste monomial. -/
def groupAdd {K V : Type} [DecidableEq K] [Add V] :
    List (K × V) → K → V → List (K × V)
  | [], k, v => [(k, v)]
  | (k', v') :: t, k, v => if k' = k then (k', v' + v) :: t else (k', v') :: groupAdd t k v

/-- The generator polynomials of the soundness ideal for one equality check: the coefficients of the
symbolic check polynomial with respect to the toxic-waste monomials, each a polynomial in the ideal
indeterminates (prover coefficients and statement entries). By Schwartz–Zippel the verifier check
passes (over random samples) iff all of these vanish, so they generate the ideal whose membership
decides soundness. -/
noncomputable def verificationGenerators (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] [DecidableEq StmtIdx] (toStmt : (StmtIdx → F) → 𝓟.Stmt)
    (k : 𝓟.EqualityChecks) : List (COrdMvPolynomial (𝓟.IdealVars StmtIdx) F) :=
  let p := 𝓟.sym_check_poly StmtIdx toStmt k
  -- `COrdMvPolynomial.support` yields the monomials as `Finsupp`s; split each into its toxic-waste and
  -- ideal-indeterminate parts, then group by the toxic-waste part.
  let terms : List ((𝓟.Sample →₀ ℕ) × COrdMvPolynomial (𝓟.IdealVars StmtIdx) F) :=
    p.support.toList.map fun m =>
      let split := Finsupp.sumFinsuppAddEquivProdFinsupp m
      (split.1,
        COrdMvPolynomial.monomial (COrdMvMonomial.ofFinsupp split.2) (p.coeff (COrdMvMonomial.ofFinsupp m)))
  (terms.foldl (fun acc t => groupAdd acc t.1 t.2) []).map (·.2)

/-- A polynomial ideal-membership problem over the variable type `V`: it holds iff `target` lies in
the ideal generated by `generators`. (For the soundness reduction, `V` is `𝓟.IdealVars StmtIdx`.) -/
structure IdealMembershipProblem (V : Type) [FinEnum V] [Ord V] [Std.TransOrd V]
    [Std.LawfulEqOrd V] (R : Type) [Field R] [BEq R] [LawfulBEq R] where
  /-- The generators of the soundness ideal (the toxic-waste coefficients of the verifier checks). -/
  generators : List (COrdMvPolynomial V R)
  /-- The polynomial encoding the relation, whose membership in the ideal is to be decided. -/
  target : COrdMvPolynomial V R

/-- Assemble the soundness ideal-membership problem: the generators collected over every equality
check (statement treated symbolically), paired with the supplied relation `target`. -/
noncomputable def soundnessIdealProblem (𝓟 : AGMProofSystemInstantiation F) (StmtIdx : Type)
    [FinEnum StmtIdx] [DecidableEq StmtIdx] [FinEnum 𝓟.EqualityChecks]
    (toStmt : (StmtIdx → F) → 𝓟.Stmt) (target : COrdMvPolynomial (𝓟.IdealVars StmtIdx) F) :
    IdealMembershipProblem (𝓟.IdealVars StmtIdx) F where
  generators :=
    (FinEnum.toList 𝓟.EqualityChecks).flatMap (𝓟.verificationGenerators StmtIdx toStmt)
  target := target

end AGMProofSystemInstantiation
