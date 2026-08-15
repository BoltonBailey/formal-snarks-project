/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import FormalSnarksProject.Models.StraightforwardAGMProofSystem
public import FormalSnarksProject.ToMathlib.OptionEquivRight
public import FormalSnarksProject.ToMathlib.COrdMvPolynomialRepr
public import FormalSnarksProject.ToMathlib.FinEnumOrd

/-!
# Symbolic straightforward AGM schemes

This file is a rewrite of `StraightforwardAGMProofSystem` in which the SRS element values are
*symbolic*: they are described in terms of an abstract finite set of *polynomial families*
(`PolyFams` — for Groth16: `u_stmt`, `v_wit`, `x^i`, `x^i·t`, …) rather than as concrete
polynomials depending on a circuit datum `aux`. This makes the whole scheme — and, crucially, its
soundness ideal-membership problem — a closed term, independent of any particular circuit.

## The shape being abstracted

In the manual soundness proofs (e.g. `Groth16TypeIII/Soundness.lean`), after extracting the
coefficients of the toxic-waste monomials (`h0012`, `h0021`, …), every equation is `generalize`d
over variables of the shape

  `sum_A_u_wit = ∑ i, C (prover coefficient of proof element A on SRS element (q, i)) * u_wit i`,

i.e. one variable per (proof element, SRS component, polynomial family) triple, together with
per-statement sums `sum_u_stmt = ∑ i, C (stmt i) * u_stmt i` (one per family) and scalar
variables `A_1 = C (prover coefficient of A on the SRS element α)` (one per proof element and
singleton SRS element). The final `linear_combination` step is then a polynomial
ideal-membership certificate over these variables.

This works because in every straightforward scheme the value of the `i`th element of an SRS
component `c` is `∑ f, m_{c,f} · (f i)` where `m_{c,f}` is a polynomial in the (bounded)
toxic-waste samples and `f` ranges over the polynomial families. Grouping the AGM expansion of
each proof element by `(c, f)` produces exactly the `sum_foo_bar` variables.

## Structure of this file

* `SymbolicAGMScheme` — the scheme datatype. SRS elements are split into *singles* (one element,
  fully known toxic-waste value, e.g. `[α]₁ = γδα`) and *components* (`Fin`-indexed at
  instantiation time, symbolic value `SRSComponentValue : Components → PolyFams →
  COrdMvPolynomial Vars F`). Index-size compatibility between components and families is tracked by
  a type `IdxClass` of named size classes (statement size, witness size, …); the statement is a
  vector indexed by the distinguished `stmtClass`.
* `SumVar` — the abstract `sum_foo_bar` variables.
* `symCheckPoly` — the symbolic verification-check polynomial over `Vars ⊕ SumVar 𝓢`, and
  `checkGenerators`/`soundnessGenerators` — its coefficients with respect to the toxic-waste
  monomials, the generators of the soundness ideal.
* `soundnessProblem` — the resulting `IdealMembershipProblem` over `SumVar 𝓢` (the object to
  hand to a solver), for a designer-supplied `target` polynomial encoding relation + extractor.
* `Instantiation`/`toAGMProofSystem` — realizing the scheme on concrete circuit data, giving the
  usual `AGMProofSystemInstantiation` and hence the meaning of soundness.
* `sumValue`/`evalSumsHom` — the semantics of the sum variables for a given instance, statement
  and prover.
* `ChecksImplyGenerators` — the (yet-to-be-proven-generically) bridge: if the verifier's checks
  pass then every generator vanishes under `sumValue`. This is the abstract counterpart of the
  coefficient-extraction step (`h0012` … `h1122`) of the manual proofs.
* `evalSums_target_eq_zero` — *proved*: bridge + membership of the target in the **radical** of
  the generator ideal ⟹ the target's value vanishes for every verifying prover. Radical (rather
  than plain) membership is what the manual proofs' `integral_domain_tactic` case-splitting
  amounts to; it is decidable by Gröbner bases via the Rabinowitsch trick.

The remaining per-SNARK glue — "target value vanishes ⟹ relation holds for the extracted
witness" — is the analogue of the `suffices`/`modByMonic` step of the manual proofs and stays
instance-specific.
-/

@[expose] public section

open CPoly
open CPoly.COrdMvPolynomial

/-- A straightforward linear PCP SNARK scheme with *symbolic* SRS values: the SRS is described
over an abstract set of polynomial families, so the scheme (and its soundness ideal-membership
problem) is a closed term, independent of any concrete circuit. See the module docstring. -/
structure SymbolicAGMScheme (F : Type) [Field F] [BEq F] [LawfulBEq F] where
  /-- Index of the bounded-degree toxic-waste samples. The unbounded sample (in which the
  polynomial families live) is the extra `none` of `Option Vars` at instantiation time. -/
  Vars : Type
  [Vars_FinEnum : FinEnum Vars]
  [Vars_Ord : Ord Vars]
  [Vars_TransOrd : Std.TransOrd Vars]
  [Vars_LawfulEqOrd : Std.LawfulEqOrd Vars]
  /-- Named size classes for the `Fin`-indexed data (statement size, witness size, number of
  gates, …). Instantiation assigns each class a length. -/
  IdxClass : Type
  [IdxClass_DecEq : DecidableEq IdxClass]
  /-- The size class of the statement: statements are `Fin (classLen stmtClass) → F`. -/
  stmtClass : IdxClass
  /-- Abstract polynomial families: named classes of univariate polynomials in the unbounded
  sample, fixed only at instantiation time (e.g. `u_stmt`, `v_wit`, `xⁱ`, `xⁱ·t`). -/
  PolyFams : Type
  [PolyFams_FinEnum : FinEnum PolyFams]
  /-- The size class indexing each family. -/
  famClass : PolyFams → IdxClass

  /-- Singleton SRS elements in `G1` with fully known values (e.g. `[α]₁`). -/
  SRSSingles_G1 : Type
  [SRSSingles_G1_FinEnum : FinEnum SRSSingles_G1]
  /-- Similarly for `G2`. -/
  SRSSingles_G2 : Type
  [SRSSingles_G2_FinEnum : FinEnum SRSSingles_G2]
  /-- The value of a singleton SRS element: a known polynomial in the toxic-waste samples. -/
  SRSSingleValue_G1 : SRSSingles_G1 → COrdMvPolynomial Vars F
  SRSSingleValue_G2 : SRSSingles_G2 → COrdMvPolynomial Vars F

  /-- `Fin`-indexed SRS components in `G1` (e.g. the `[uᵢ(x)β + vᵢ(x)α + wᵢ(x)]₁` column). -/
  SRSComponents_G1 : Type
  [SRSComponents_G1_FinEnum : FinEnum SRSComponents_G1]
  SRSComponents_G2 : Type
  [SRSComponents_G2_FinEnum : FinEnum SRSComponents_G2]
  /-- The size class indexing each component. -/
  compClass_G1 : SRSComponents_G1 → IdxClass
  compClass_G2 : SRSComponents_G2 → IdxClass
  /-- The symbolic value of a component: the `i`th element of component `c` is
  `∑ f, (SRSComponentValue_G1 c f) · (f i)`. Entries for families whose size class differs from
  the component's are ignored at instantiation (keep them `0`). -/
  SRSComponentValue_G1 : SRSComponents_G1 → PolyFams → COrdMvPolynomial Vars F
  SRSComponentValue_G2 : SRSComponents_G2 → PolyFams → COrdMvPolynomial Vars F

  /-- A type indexing proof elements in each group. -/
  Proof_G1 : Type
  [Proof_G1_FinEnum : FinEnum Proof_G1]
  Proof_G2 : Type
  [Proof_G2_FinEnum : FinEnum Proof_G2]
  /-- A type indexing the equality checks the verifier makes. -/
  EqualityChecks : Type
  [EqualityChecks_FinEnum : FinEnum EqualityChecks]
  /-- The pairings summed in each equality check. -/
  Pairings : EqualityChecks → Type
  [Pairings_FinEnum : (k : EqualityChecks) → FinEnum (Pairings k)]
  /-- The (statement-independent) coefficient the verifier applies to each proof element in each
  pairing. In this symbolic setting the verifier's coefficients are constants, except for the
  statement-weighting of components via `verifCoeffComp_G1/G2`. -/
  verifCoeffProof_G1 : (k : EqualityChecks) → Pairings k → Proof_G1 → F
  verifCoeffProof_G2 : (k : EqualityChecks) → Pairings k → Proof_G2 → F
  /-- The constant coefficient the verifier applies to each singleton SRS element. -/
  verifCoeffSingle_G1 : (k : EqualityChecks) → Pairings k → SRSSingles_G1 → F
  verifCoeffSingle_G2 : (k : EqualityChecks) → Pairings k → SRSSingles_G2 → F
  /-- Statement-weighting of an SRS component: `some κ` means the verifier contributes
  `κ · ∑ i, stmt i · (value of element i of the component)` to the pairing input (requires the
  component's size class to be `stmtClass`; otherwise ignored), `none` means no contribution. -/
  verifCoeffComp_G1 : (k : EqualityChecks) → Pairings k → SRSComponents_G1 → Option F
  verifCoeffComp_G2 : (k : EqualityChecks) → Pairings k → SRSComponents_G2 → Option F

namespace SymbolicAGMScheme

attribute [instance]
  SymbolicAGMScheme.Vars_FinEnum
  SymbolicAGMScheme.Vars_Ord
  SymbolicAGMScheme.Vars_TransOrd
  SymbolicAGMScheme.Vars_LawfulEqOrd
  SymbolicAGMScheme.IdxClass_DecEq
  SymbolicAGMScheme.PolyFams_FinEnum
  SymbolicAGMScheme.SRSSingles_G1_FinEnum
  SymbolicAGMScheme.SRSSingles_G2_FinEnum
  SymbolicAGMScheme.SRSComponents_G1_FinEnum
  SymbolicAGMScheme.SRSComponents_G2_FinEnum
  SymbolicAGMScheme.Proof_G1_FinEnum
  SymbolicAGMScheme.Proof_G2_FinEnum
  SymbolicAGMScheme.EqualityChecks_FinEnum
  SymbolicAGMScheme.Pairings_FinEnum

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-! ### The abstract sum variables -/

/-- The indeterminates of the abstract soundness problem — the `sum_foo_bar` variables of the
manual proofs:

* `single_G1/G2 p s`: the prover's scalar coefficient of proof element `p` on the singleton SRS
  element `s` (the `A_1`, `B_3`, `C_1`, … of the manual proofs);
* `comp_G1/G2 p c f`: the sum `∑ i, (coefficient of p on element i of component c) · (f i)`
  (the `sum_A_u_wit`, `sum_C_x_t`, …);
* `stmtSum f`: the statement-weighted family sum `∑ i, stmt i · (f i)`
  (the `sum_u_stmt`, `sum_v_stmt`, …).

Realized as an anonymous sum type, with `FinEnum`/`DecidableEq` transported from that type below;
use the smart constructors below. This is a `def` rather than an `abbrev` so that it keeps its own
head symbol `SumVar` for instance resolution — otherwise a `Repr (SumVar 𝓢)` instance cannot fire
(unfolding to the bare `⊕` type loses `𝓢`, which is only recoverable as a projection). -/
def SumVar (𝓢 : SymbolicAGMScheme F) : Type :=
  (𝓢.Proof_G1 × 𝓢.SRSSingles_G1)
    ⊕ (𝓢.Proof_G2 × 𝓢.SRSSingles_G2)
    ⊕ (𝓢.Proof_G1 × 𝓢.SRSComponents_G1 × 𝓢.PolyFams)
    ⊕ (𝓢.Proof_G2 × 𝓢.SRSComponents_G2 × 𝓢.PolyFams)
    ⊕ 𝓢.PolyFams

instance instDecidableEqSumVar (𝓢 : SymbolicAGMScheme F) [DecidableEq 𝓢.Proof_G1]
    [DecidableEq 𝓢.Proof_G2] [DecidableEq 𝓢.SRSSingles_G1] [DecidableEq 𝓢.SRSSingles_G2]
    [DecidableEq 𝓢.SRSComponents_G1] [DecidableEq 𝓢.SRSComponents_G2] [DecidableEq 𝓢.PolyFams] :
    DecidableEq (SumVar 𝓢) :=
  inferInstanceAs (DecidableEq ((𝓢.Proof_G1 × 𝓢.SRSSingles_G1)
    ⊕ (𝓢.Proof_G2 × 𝓢.SRSSingles_G2)
    ⊕ (𝓢.Proof_G1 × 𝓢.SRSComponents_G1 × 𝓢.PolyFams)
    ⊕ (𝓢.Proof_G2 × 𝓢.SRSComponents_G2 × 𝓢.PolyFams)
    ⊕ 𝓢.PolyFams))

namespace SumVar

variable {𝓢 : SymbolicAGMScheme F}

/-- The prover's coefficient of `G1` proof element `p` on the singleton SRS element `s`. -/
def single_G1 (p : 𝓢.Proof_G1) (s : 𝓢.SRSSingles_G1) : SumVar 𝓢 := Sum.inl (p, s)

/-- The prover's coefficient of `G2` proof element `p` on the singleton SRS element `s`. -/
def single_G2 (p : 𝓢.Proof_G2) (s : 𝓢.SRSSingles_G2) : SumVar 𝓢 := Sum.inr (Sum.inl (p, s))

/-- `∑ i, (coefficient of p on element i of component c) · (f i)`. -/
def comp_G1 (p : 𝓢.Proof_G1) (c : 𝓢.SRSComponents_G1) (f : 𝓢.PolyFams) : SumVar 𝓢 :=
  Sum.inr (Sum.inr (Sum.inl (p, c, f)))

/-- `∑ i, (coefficient of p on element i of component c) · (f i)`. -/
def comp_G2 (p : 𝓢.Proof_G2) (c : 𝓢.SRSComponents_G2) (f : 𝓢.PolyFams) : SumVar 𝓢 :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl (p, c, f))))

/-- The statement-weighted family sum `∑ i, stmt i · (f i)`. -/
def stmtSum (f : 𝓢.PolyFams) : SumVar 𝓢 := Sum.inr (Sum.inr (Sum.inr (Sum.inr f)))

end SumVar

/-- Print a sum variable via the semantics of its smart constructors (`single_G1 p s`,
`comp_G1 p c f`, `stmtSum f`, …) rather than the raw nested `Sum.inr (Sum.inl …)` the underlying
sum type would give. Because `SumVar` is a `def`, this matches on the head symbol `SumVar` (so `𝓢`
is recovered), and there is no competition from the generic `Sum`/`Prod` `Repr`. Supply `Repr`
instances for the scheme's index types (see `Groth16TypeIII/Symbolic.lean`) to make it fire. -/
instance instReprSumVar (𝓢 : SymbolicAGMScheme F)
    [Repr 𝓢.Proof_G1] [Repr 𝓢.Proof_G2] [Repr 𝓢.SRSSingles_G1] [Repr 𝓢.SRSSingles_G2]
    [Repr 𝓢.SRSComponents_G1] [Repr 𝓢.SRSComponents_G2] [Repr 𝓢.PolyFams] :
    Repr (SumVar 𝓢) where
  reprPrec v _ := match v with
    | Sum.inl (p, s) => "single_G1 " ++ repr p ++ " " ++ repr s
    | Sum.inr (Sum.inl (p, s)) => "single_G2 " ++ repr p ++ " " ++ repr s
    | Sum.inr (Sum.inr (Sum.inl (p, c, f))) =>
        "comp_G1 " ++ repr p ++ " " ++ repr c ++ " " ++ repr f
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl (p, c, f)))) =>
        "comp_G2 " ++ repr p ++ " " ++ repr c ++ " " ++ repr f
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr f))) => "stmtSum " ++ repr f

-- Explicit instance so synthesis for the nested sum/product type is immediate.
instance instFinEnumSumVar (𝓢 : SymbolicAGMScheme F) : FinEnum (SumVar 𝓢) :=
  inferInstanceAs (FinEnum ((𝓢.Proof_G1 × 𝓢.SRSSingles_G1)
    ⊕ (𝓢.Proof_G2 × 𝓢.SRSSingles_G2)
    ⊕ (𝓢.Proof_G1 × 𝓢.SRSComponents_G1 × 𝓢.PolyFams)
    ⊕ (𝓢.Proof_G2 × 𝓢.SRSComponents_G2 × 𝓢.PolyFams)
    ⊕ 𝓢.PolyFams))

/-- Variables of the symbolic check polynomial: the (bounded) toxic-waste samples together with
the abstract sum variables. Note that the unbounded sample `x` does not appear: all of its
occurrences live inside the polynomial families, i.e. inside the sum variables. -/
abbrev SymVars (𝓢 : SymbolicAGMScheme F) : Type := 𝓢.Vars ⊕ SumVar 𝓢

instance instFinEnumSymVars (𝓢 : SymbolicAGMScheme F) : FinEnum 𝓢.SymVars :=
  inferInstanceAs (FinEnum (𝓢.Vars ⊕ SumVar 𝓢))

/-! The computable polynomials over `SumVar`/`SymVars` need a lawful ordering on the variable
type. Core provides no `Ord` for sum types, so pull one back from the `FinEnum` enumeration.
Keyed at `SumVar` and at `SymVars` (which unfolds to the sum), these are the unique `Ord`
instances on the symbolic variable types. -/

instance instOrdSumVar (𝓢 : SymbolicAGMScheme F) : Ord (SumVar 𝓢) := FinEnum.toOrd
instance instTransOrdSumVar (𝓢 : SymbolicAGMScheme F) : Std.TransOrd (SumVar 𝓢) :=
  FinEnum.toOrd.transOrd
instance instLawfulEqOrdSumVar (𝓢 : SymbolicAGMScheme F) : Std.LawfulEqOrd (SumVar 𝓢) :=
  FinEnum.toOrd.lawfulEqOrd

instance instOrdSymVars (𝓢 : SymbolicAGMScheme F) : Ord 𝓢.SymVars := FinEnum.toOrd
instance instTransOrdSymVars (𝓢 : SymbolicAGMScheme F) : Std.TransOrd 𝓢.SymVars :=
  FinEnum.toOrd.transOrd
instance instLawfulEqOrdSymVars (𝓢 : SymbolicAGMScheme F) : Std.LawfulEqOrd 𝓢.SymVars :=
  FinEnum.toOrd.lawfulEqOrd

/-! ### The symbolic check polynomial and the soundness generators -/

variable (𝓢 : SymbolicAGMScheme F)

/-- Embed a toxic-waste polynomial into the symbolic ring. -/
def symEmbed (p : COrdMvPolynomial 𝓢.Vars F) : COrdMvPolynomial 𝓢.SymVars F :=
  rename Sum.inl p

/-- The symbolic expansion of a `G1` proof element: the AGM linear combination over the SRS,
grouped by (component, family) so that each group is a single sum variable. -/
def symProof_G1 (p : 𝓢.Proof_G1) : COrdMvPolynomial 𝓢.SymVars F :=
  ((FinEnum.toList 𝓢.SRSSingles_G1).map fun s =>
      X (Sum.inr (SumVar.single_G1 p s)) * 𝓢.symEmbed (𝓢.SRSSingleValue_G1 s)).sum
    + ((FinEnum.toList 𝓢.SRSComponents_G1).map fun c =>
        ((FinEnum.toList 𝓢.PolyFams).map fun f =>
          if 𝓢.famClass f = 𝓢.compClass_G1 c then
            𝓢.symEmbed (𝓢.SRSComponentValue_G1 c f) * X (Sum.inr (SumVar.comp_G1 p c f))
          else 0).sum).sum

/-- The symbolic expansion of a `G2` proof element. -/
def symProof_G2 (p : 𝓢.Proof_G2) : COrdMvPolynomial 𝓢.SymVars F :=
  ((FinEnum.toList 𝓢.SRSSingles_G2).map fun s =>
      X (Sum.inr (SumVar.single_G2 p s)) * 𝓢.symEmbed (𝓢.SRSSingleValue_G2 s)).sum
    + ((FinEnum.toList 𝓢.SRSComponents_G2).map fun c =>
        ((FinEnum.toList 𝓢.PolyFams).map fun f =>
          if 𝓢.famClass f = 𝓢.compClass_G2 c then
            𝓢.symEmbed (𝓢.SRSComponentValue_G2 c f) * X (Sum.inr (SumVar.comp_G2 p c f))
          else 0).sum).sum

/-- The verifier's (non-proof) `G1` contribution to a pairing input: the singleton SRS elements
with their constant coefficients, plus the statement-weighted components, grouped by family into
`stmtSum` variables. -/
def symVerifierInput_G1 (k : 𝓢.EqualityChecks) (pairing : 𝓢.Pairings k) :
    COrdMvPolynomial 𝓢.SymVars F :=
  ((FinEnum.toList 𝓢.SRSSingles_G1).map fun s =>
      C (𝓢.verifCoeffSingle_G1 k pairing s) * 𝓢.symEmbed (𝓢.SRSSingleValue_G1 s)).sum
    + ((FinEnum.toList 𝓢.SRSComponents_G1).map fun c =>
        match 𝓢.verifCoeffComp_G1 k pairing c with
        | none => 0
        | some κ =>
          if 𝓢.compClass_G1 c = 𝓢.stmtClass then
            C κ * ((FinEnum.toList 𝓢.PolyFams).map fun f =>
              if 𝓢.famClass f = 𝓢.compClass_G1 c then
                𝓢.symEmbed (𝓢.SRSComponentValue_G1 c f) * X (Sum.inr (SumVar.stmtSum f))
              else 0).sum
          else 0).sum

/-- The verifier's (non-proof) `G2` contribution to a pairing input. -/
def symVerifierInput_G2 (k : 𝓢.EqualityChecks) (pairing : 𝓢.Pairings k) :
    COrdMvPolynomial 𝓢.SymVars F :=
  ((FinEnum.toList 𝓢.SRSSingles_G2).map fun s =>
      C (𝓢.verifCoeffSingle_G2 k pairing s) * 𝓢.symEmbed (𝓢.SRSSingleValue_G2 s)).sum
    + ((FinEnum.toList 𝓢.SRSComponents_G2).map fun c =>
        match 𝓢.verifCoeffComp_G2 k pairing c with
        | none => 0
        | some κ =>
          if 𝓢.compClass_G2 c = 𝓢.stmtClass then
            C κ * ((FinEnum.toList 𝓢.PolyFams).map fun f =>
              if 𝓢.famClass f = 𝓢.compClass_G2 c then
                𝓢.symEmbed (𝓢.SRSComponentValue_G2 c f) * X (Sum.inr (SumVar.stmtSum f))
              else 0).sum
          else 0).sum

/-- The symbolic value of one pairing of one equality check. -/
def symPairingPoly (k : 𝓢.EqualityChecks) (pairing : 𝓢.Pairings k) :
    COrdMvPolynomial 𝓢.SymVars F :=
  (((FinEnum.toList 𝓢.Proof_G1).map fun p =>
        C (𝓢.verifCoeffProof_G1 k pairing p) * 𝓢.symProof_G1 p).sum
      + 𝓢.symVerifierInput_G1 k pairing)
    * (((FinEnum.toList 𝓢.Proof_G2).map fun p =>
        C (𝓢.verifCoeffProof_G2 k pairing p) * 𝓢.symProof_G2 p).sum
      + 𝓢.symVerifierInput_G2 k pairing)

/-- The symbolic check polynomial of one equality check: a polynomial over the toxic-waste
samples and the sum variables whose vanishing (as a polynomial in the samples) is the check. -/
def symCheckPoly (k : 𝓢.EqualityChecks) : COrdMvPolynomial 𝓢.SymVars F :=
  ((FinEnum.toList (𝓢.Pairings k)).map fun pairing => 𝓢.symPairingPoly k pairing).sum

/-- Split a monomial over a sum of variable types into its two halves. The computable
(`COrdMvMonomial`-level) counterpart of `Finsupp.sumFinsuppAddEquivProdFinsupp`, so that the
generator extraction — and hence the whole abstract soundness problem — is `#eval`-able. -/
def splitSumMonomial {σ τ : Type} [Ord σ] [Std.TransOrd σ] [Ord τ] [Std.TransOrd τ]
    [Ord (σ ⊕ τ)] (m : COrdMvMonomial (σ ⊕ τ)) :
    COrdMvMonomial σ × COrdMvMonomial τ :=
  (COrdMvMonomial.ofList (m.entryList.filterMap fun ve =>
      match ve with | (Sum.inl v, e) => some (v, e) | (Sum.inr _, _) => none),
    COrdMvMonomial.ofList (m.entryList.filterMap fun ve =>
      match ve with | (Sum.inr v, e) => some (v, e) | (Sum.inl _, _) => none))

open AGMProofSystemInstantiation in
/-- The coefficients of a polynomial over a sum `σ ⊕ τ` of variable types with respect to the
monomials in the `σ`-variables, each a polynomial in the `τ`-variables. For a symbolic check
polynomial (`σ` the toxic-waste samples, `τ` the abstract sum variables) these are the
generators of the soundness ideal. Split each monomial into its two halves, then group by the
`σ`-part (as in `AGMProofSystemInstantiation.verificationGenerators`, but staying at the
computable `COrdMvMonomial` level rather than passing through `Finsupp`). Also used directly by the
SNARKs that do not fit `SymbolicAGMScheme` (`ToySnark`, `BabySnark`, …), on their hand-built
symbolic check polynomials. -/
def coeffGenerators {σ τ : Type} [Ord σ] [Std.TransOrd σ] [Std.LawfulEqOrd σ]
    [Ord τ] [Std.TransOrd τ] [Std.LawfulEqOrd τ]
    [Ord (σ ⊕ τ)] [Std.TransOrd (σ ⊕ τ)] [Std.LawfulEqOrd (σ ⊕ τ)]
    (p : COrdMvPolynomial (σ ⊕ τ) F) : List (COrdMvPolynomial τ F) :=
  let terms : List (COrdMvMonomial σ × COrdMvPolynomial τ F) :=
    (OrdLawful.monomials p).map fun m =>
      let split := splitSumMonomial m
      (split.1, COrdMvPolynomial.monomial split.2 (p.coeff m))
  (terms.foldl (fun acc t => groupAdd acc t.1 t.2) []).map (·.2)

/-- The generators of the soundness ideal contributed by one equality check: the coefficients of
the symbolic check polynomial with respect to the toxic-waste monomials, each a polynomial in the
sum variables. These are the abstract counterparts of the `h0012`, …, `h1122` equations of the
manual proofs. -/
def checkGenerators (k : 𝓢.EqualityChecks) :
    List (COrdMvPolynomial (SumVar 𝓢) F) :=
  coeffGenerators (𝓢.symCheckPoly k)

/-- All generators of the soundness ideal, collected over the equality checks. -/
def soundnessGenerators : List (COrdMvPolynomial (SumVar 𝓢) F) :=
  (FinEnum.toList 𝓢.EqualityChecks).flatMap 𝓢.checkGenerators

/-- The abstract soundness problem of the scheme: is the designer-supplied `target` (encoding
relation + extractor over the sum variables) a member of (the radical of) the ideal generated by
`soundnessGenerators`? This is the closed, circuit-independent object to hand to a solver. -/
def soundnessProblem (target : COrdMvPolynomial (SumVar 𝓢) F) :
    AGMProofSystemInstantiation.IdealMembershipProblem (SumVar 𝓢) F where
  generators := 𝓢.soundnessGenerators
  target := target

/-! ### Instantiation on concrete circuit data -/

/-- Concrete circuit data for a symbolic scheme: a length for each size class, and a concrete
univariate polynomial for each element of each family. -/
structure Instantiation (𝓢 : SymbolicAGMScheme F) where
  /-- The length assigned to each size class (statement size, witness size, …). -/
  classLen : 𝓢.IdxClass → ℕ
  /-- The concrete polynomials of each family. -/
  famPolys : (f : 𝓢.PolyFams) → Fin (classLen (𝓢.famClass f)) → CompPoly.CPolynomial F

/-- Realize a symbolic scheme on concrete circuit data, producing an
`AGMProofSystemInstantiation`. The SRS index of each group is `singles ⊕ Σ component, Fin len`. -/
@[reducible] noncomputable def toAGMProofSystem (inst : 𝓢.Instantiation) :
    AGMProofSystemInstantiation F where
  Stmt := Fin (inst.classLen 𝓢.stmtClass) → F
  Sample := Option 𝓢.Vars
  SRSElements_G1 :=
    𝓢.SRSSingles_G1 ⊕ Σ c : 𝓢.SRSComponents_G1, Fin (inst.classLen (𝓢.compClass_G1 c))
  SRSElements_G2 :=
    𝓢.SRSSingles_G2 ⊕ Σ c : 𝓢.SRSComponents_G2, Fin (inst.classLen (𝓢.compClass_G2 c))
  SRSElementValue_G1 := fun srs => match srs with
    | Sum.inl s => rename some (𝓢.SRSSingleValue_G1 s)
    | Sum.inr ⟨c, i⟩ =>
      ((FinEnum.toList 𝓢.PolyFams).map fun f =>
        if h : 𝓢.famClass f = 𝓢.compClass_G1 c then
          rename some (𝓢.SRSComponentValue_G1 c f)
            * to_COrdMvPolynomial_Option 𝓢.Vars
                (inst.famPolys f (Fin.cast (congrArg inst.classLen h).symm i))
        else 0).sum
  SRSElementValue_G2 := fun srs => match srs with
    | Sum.inl s => rename some (𝓢.SRSSingleValue_G2 s)
    | Sum.inr ⟨c, i⟩ =>
      ((FinEnum.toList 𝓢.PolyFams).map fun f =>
        if h : 𝓢.famClass f = 𝓢.compClass_G2 c then
          rename some (𝓢.SRSComponentValue_G2 c f)
            * to_COrdMvPolynomial_Option 𝓢.Vars
                (inst.famPolys f (Fin.cast (congrArg inst.classLen h).symm i))
        else 0).sum
  Proof_G1 := 𝓢.Proof_G1
  Proof_G2 := 𝓢.Proof_G2
  EqualityChecks := 𝓢.EqualityChecks
  Pairings := 𝓢.Pairings
  verificationPairingSRS_G1 := fun stmt k pairing srs => match srs with
    | Sum.inl s => 𝓢.verifCoeffSingle_G1 k pairing s
    | Sum.inr ⟨c, i⟩ =>
      match 𝓢.verifCoeffComp_G1 k pairing c with
      | none => 0
      | some κ =>
        if h : 𝓢.compClass_G1 c = 𝓢.stmtClass then
          κ * stmt (Fin.cast (congrArg inst.classLen h) i)
        else 0
  verificationPairingSRS_G2 := fun stmt k pairing srs => match srs with
    | Sum.inl s => 𝓢.verifCoeffSingle_G2 k pairing s
    | Sum.inr ⟨c, i⟩ =>
      match 𝓢.verifCoeffComp_G2 k pairing c with
      | none => 0
      | some κ =>
        if h : 𝓢.compClass_G2 c = 𝓢.stmtClass then
          κ * stmt (Fin.cast (congrArg inst.classLen h) i)
        else 0
  verificationPairingProof_G1 := fun _stmt k pairing p => 𝓢.verifCoeffProof_G1 k pairing p
  verificationPairingProof_G2 := fun _stmt k pairing p => 𝓢.verifCoeffProof_G2 k pairing p
  Identified_Proof_Elems := []

/-! ### Semantics of the sum variables -/

/-- The actual (mathlib `Polynomial`) value of each sum variable, for a given instance, statement
and AGM prover. This is what the `generalize` steps of the manual proofs abstract over. -/
noncomputable def sumValue (inst : 𝓢.Instantiation)
    (stmt : Fin (inst.classLen 𝓢.stmtClass) → F)
    (prover : AGMProofSystemInstantiation.Prover F (𝓢.toAGMProofSystem inst)) :
    SumVar 𝓢 → Polynomial F
  | Sum.inl (p, s) => Polynomial.C (prover.1 p (Sum.inl s))
  | Sum.inr (Sum.inl (p, s)) => Polynomial.C (prover.2 p (Sum.inl s))
  | Sum.inr (Sum.inr (Sum.inl (p, c, f))) =>
    if h : 𝓢.famClass f = 𝓢.compClass_G1 c then
      ((List.finRange (inst.classLen (𝓢.compClass_G1 c))).map fun i =>
        Polynomial.C (prover.1 p (Sum.inr ⟨c, i⟩))
          * (inst.famPolys f (Fin.cast (congrArg inst.classLen h).symm i)).toPoly).sum
    else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (p, c, f)))) =>
    if h : 𝓢.famClass f = 𝓢.compClass_G2 c then
      ((List.finRange (inst.classLen (𝓢.compClass_G2 c))).map fun i =>
        Polynomial.C (prover.2 p (Sum.inr ⟨c, i⟩))
          * (inst.famPolys f (Fin.cast (congrArg inst.classLen h).symm i)).toPoly).sum
    else 0
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr f))) =>
    if h : 𝓢.famClass f = 𝓢.stmtClass then
      ((List.finRange (inst.classLen 𝓢.stmtClass)).map fun i =>
        Polynomial.C (stmt i)
          * (inst.famPolys f (Fin.cast (congrArg inst.classLen h).symm i)).toPoly).sum
    else 0

/-- Evaluation of an abstract polynomial over the sum variables at their actual values, as a ring
homomorphism (through `CPoly.COrdMvPolynomial.ordPolyRingEquiv` and `MvPolynomial.aeval`). -/
noncomputable def evalSumsHom (vals : SumVar 𝓢 → Polynomial F) :
    COrdMvPolynomial (SumVar 𝓢) F →+* Polynomial F :=
  (MvPolynomial.aeval (R := F) vals).toRingHom.comp
    (CPoly.COrdMvPolynomial.ordPolyRingEquiv (σ := SumVar 𝓢) (R := F)).toRingHom

/-! ### The soundness reduction -/

/-- The bridge between verification and the generators — the abstract counterpart of the
coefficient-extraction step (`h0012` … `h1122`) of the manual soundness proofs: if the verifier's
checks pass, then every generator of the soundness ideal vanishes when the sum variables take
their actual values.

For straightforward schemes this should hold *always* (it is the main theorem of the
Bailey–Miller paper); proving it generically over `SymbolicAGMScheme` is future work, so for now
it is a named hypothesis. -/
def ChecksImplyGenerators : Prop :=
  ∀ (inst : 𝓢.Instantiation)
    (stmt : Fin (inst.classLen 𝓢.stmtClass) → F)
    (prover : AGMProofSystemInstantiation.Prover F (𝓢.toAGMProofSystem inst)),
    (𝓢.toAGMProofSystem inst).verify prover stmt →
    ∀ g ∈ 𝓢.soundnessGenerators, 𝓢.evalSumsHom (𝓢.sumValue inst stmt prover) g = 0

/-- Generic algebra fact underlying the soundness reduction: a ring homomorphism into an integral
domain kills every element of the *radical* of an ideal whose generators it kills. Radical (as
opposed to plain) membership is exactly what the `integral_domain_tactic` case-splitting of the
manual proofs buys, and it is decidable by Gröbner bases via the Rabinowitsch trick. -/
theorem eval_eq_zero_of_mem_radical {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (gens : List R) (target : R)
    (hmem : target ∈ (Ideal.span {g | g ∈ gens}).radical)
    (hvanish : ∀ g ∈ gens, φ g = 0) :
    φ target = 0 := by
  have hker : Ideal.span {g | g ∈ gens} ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    intro g hg
    exact RingHom.mem_ker.mpr (hvanish g hg)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hmem
  have h0 : φ target ^ n = 0 := by
    rw [← map_pow]
    exact RingHom.mem_ker.mp (hker hn)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [pow_zero] at h0
    exact absurd h0 one_ne_zero
  · exact (pow_eq_zero_iff hpos.ne').mp h0

/-- **The soundness reduction.** If

* the checks imply the generators (`ChecksImplyGenerators`, the generic bridge), and
* the target lies in the radical of the soundness ideal (the abstract problem, checkable by a
  Gröbner-basis solver once and for all — no circuit data involved),

then for every instance, statement and verifying AGM prover the target polynomial evaluates to
zero at the actual sum values. The per-SNARK step from this to the relation (e.g. Groth16's
`modByMonic` argument) remains instance-specific. -/
theorem evalSums_target_eq_zero
    (target : COrdMvPolynomial (SumVar 𝓢) F)
    (hbridge : 𝓢.ChecksImplyGenerators)
    (hmem : target ∈ (Ideal.span {g | g ∈ 𝓢.soundnessGenerators}).radical)
    (inst : 𝓢.Instantiation)
    (stmt : Fin (inst.classLen 𝓢.stmtClass) → F)
    (prover : AGMProofSystemInstantiation.Prover F (𝓢.toAGMProofSystem inst))
    (hverify : (𝓢.toAGMProofSystem inst).verify prover stmt) :
    𝓢.evalSumsHom (𝓢.sumValue inst stmt prover) target = 0 :=
  eval_eq_zero_of_mem_radical _ _ _ hmem
    (fun g hg => hbridge inst stmt prover hverify g hg)

end SymbolicAGMScheme
