/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import FormalSnarksProject.Models.SymbolicAGMScheme
public import FormalSnarksProject.SNARKs.Groth16TypeIII.Defs
public import FormalSnarksProject.ToMathlib.FinEnumOrd

/-!
# Groth16TypeIII, symbolically

This file represents the Type III Groth16 SNARK as a `SymbolicAGMScheme` — a closed term making
no reference to any concrete circuit polynomials `u`, `v`, `w` (nor to the sizes
`n_stmt`/`n_wit`/`n_var`). From it we obtain the abstract soundness ideal-membership problem
(`soundnessProblem`), whose variables are the `sum_foo_bar` quantities of the manual proof in
`Groth16TypeIII/Soundness.lean`:

| manual proof variable | abstract sum variable                         |
| --------------------- | --------------------------------------------- |
| `A_1`, `A_2`, `A_3`   | `single_G1 .A .α/.β/.δ`                       |
| `B_1`, `B_2`, `B_3`   | `single_G2 .B .β/.γ/.δ`                       |
| `C_1`, `C_2`, `C_3`   | `single_G1 .C .α/.β/.δ`                       |
| `sum_A_x`             | `comp_G1 .A .x_pow .x_pows`                   |
| `sum_A_x_t`           | `comp_G1 .A .x_pow_times_t .x_pows_t`         |
| `sum_A_u_stmt` etc.   | `comp_G1 .A .y .u_stmt` etc.                  |
| `sum_A_u_wit` etc.    | `comp_G1 .A .q .u_wit` etc.                   |
| `sum_B_x`             | `comp_G2 .B .x_pow .x_pows`                   |
| `sum_C_u_wit` etc.    | `comp_G1 .C .q .u_wit` etc.                   |
| `sum_C_x_t`           | `comp_G1 .C .x_pow_times_t .x_pows_t`         |
| `sum_u_stmt` etc.     | `stmtSum .u_stmt` etc.                        |

The `target` polynomial encodes the QAP relation with the witness extracted from proof element
`C`'s coefficients on the `q` component (matching the extractor of the manual proof); the manual
proof's final `linear_combination` steps are an (integral-domain / radical) ideal-membership
certificate for it.

The concrete SNARK of `Groth16TypeIII/Defs.lean` corresponds to instantiating this scheme with
`instantiation u_stmt v_stmt w_stmt u_wit v_wit w_wit r` (see `toAGMProofSystem`); the existing
definition is left untouched.
-/

@[expose] public section

open scoped BigOperators

open CPoly CPoly.COrdMvPolynomial
open CompPoly

namespace Groth16TypeIII

namespace Symbolic

/-- The size classes of Groth16: statement size `n_stmt`, witness size `n_wit`, number of
variables `n_var`, and `n_var - 1` (the length of the `xⁱ·t` column). -/
inductive IdxClass : Type where
  | stmt : IdxClass
  | wit : IdxClass
  | var : IdxClass
  | varSub1 : IdxClass
deriving DecidableEq

/-- The abstract polynomial families of Groth16: the QAP columns `u`, `v`, `w` (split into
statement and witness parts), the powers of `x`, and the powers of `x` times the vanishing
polynomial `t`. -/
inductive PolyFam : Type where
  | u_stmt : PolyFam
  | v_stmt : PolyFam
  | w_stmt : PolyFam
  | u_wit : PolyFam
  | v_wit : PolyFam
  | w_wit : PolyFam
  | x_pows : PolyFam
  | x_pows_t : PolyFam
deriving DecidableEq

instance : FinEnum PolyFam :=
  .ofList [.u_stmt, .v_stmt, .w_stmt, .u_wit, .v_wit, .w_wit, .x_pows, .x_pows_t]
    (fun x => by cases x <;> simp)

/-- The size class of each family. -/
def famClass : PolyFam → IdxClass
  | .u_stmt => .stmt
  | .v_stmt => .stmt
  | .w_stmt => .stmt
  | .u_wit => .wit
  | .v_wit => .wit
  | .w_wit => .wit
  | .x_pows => .var
  | .x_pows_t => .varSub1

/-- The singleton `G1` SRS elements. -/
inductive SRSSingle_G1 : Type where
  | α : SRSSingle_G1
  | β : SRSSingle_G1
  | δ : SRSSingle_G1
deriving DecidableEq

instance : FinEnum SRSSingle_G1 := .ofList [.α, .β, .δ] (fun x => by cases x <;> simp)

/-- The singleton `G2` SRS elements. -/
inductive SRSSingle_G2 : Type where
  | β : SRSSingle_G2
  | γ : SRSSingle_G2
  | δ : SRSSingle_G2
deriving DecidableEq

instance : FinEnum SRSSingle_G2 := .ofList [.β, .γ, .δ] (fun x => by cases x <;> simp)

/-- The `Fin`-indexed `G1` SRS components. -/
inductive SRSComp_G1 : Type where
  | x_pow : SRSComp_G1
  | x_pow_times_t : SRSComp_G1
  | y : SRSComp_G1
  | q : SRSComp_G1
deriving DecidableEq

instance : FinEnum SRSComp_G1 :=
  .ofList [.x_pow, .x_pow_times_t, .y, .q] (fun x => by cases x <;> simp)

/-- The size class of each `G1` component. -/
def compClass_G1 : SRSComp_G1 → IdxClass
  | .x_pow => .var
  | .x_pow_times_t => .varSub1
  | .y => .stmt
  | .q => .wit

/-- The `Fin`-indexed `G2` SRS components. -/
inductive SRSComp_G2 : Type where
  | x_pow : SRSComp_G2
deriving DecidableEq

instance : FinEnum SRSComp_G2 := .ofList [.x_pow] (fun x => by cases x <;> simp)

/-- The size class of each `G2` component. -/
def compClass_G2 : SRSComp_G2 → IdxClass
  | .x_pow => .var

/-! ### Short `Repr` instances for readable output

These give the index types single-token names (`A`, `q`, `u_wit`, …) so that, together with the
generic `Repr (SumVar 𝓢)` and `Repr (COrdMvPolynomial σ R)`, the abstract generators print as e.g.
`comp_G1 C q u_wit + stmtSum v_stmt` rather than positional `X8^1 * X27^1` or nested `Sum.inr …`.
The proof-element index types `Proof_G1_Idx`/`Proof_G2_Idx` live in `Defs.lean` (which only derives
`DecidableEq`); we add their `Repr` here to leave that file untouched. -/

instance : Repr Proof_G1_Idx := ⟨fun p _ => match p with | .A => "A" | .C => "C"⟩
instance : Repr Proof_G2_Idx := ⟨fun _ _ => "B"⟩

instance : Repr PolyFam := ⟨fun f _ => match f with
  | .u_stmt => "u_stmt" | .v_stmt => "v_stmt" | .w_stmt => "w_stmt"
  | .u_wit => "u_wit" | .v_wit => "v_wit" | .w_wit => "w_wit"
  | .x_pows => "x_pows" | .x_pows_t => "x_pows_t"⟩

instance : Repr SRSSingle_G1 := ⟨fun s _ => match s with | .α => "α" | .β => "β" | .δ => "δ"⟩
instance : Repr SRSSingle_G2 := ⟨fun s _ => match s with | .β => "β" | .γ => "γ" | .δ => "δ"⟩

instance : Repr SRSComp_G1 := ⟨fun c _ => match c with
  | .x_pow => "x_pow" | .x_pow_times_t => "x_pow_times_t" | .y => "y" | .q => "q"⟩
instance : Repr SRSComp_G2 := ⟨fun c _ => match c with | .x_pow => "x_pow"⟩

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- Groth16 (Type III) as a symbolic scheme: a closed term, with no circuit polynomials in
sight. The values mirror `Groth16TypeIII/Defs.lean` exactly (all multiplied through by `γδ`),
with the toxic-waste monomials over `Vars` (no `Option`: the unbounded sample `x` lives inside
the families). -/
@[reducible] def scheme (F : Type) [Field F] [BEq F] [LawfulBEq F] :
    SymbolicAGMScheme F where
  Vars := Vars
  IdxClass := IdxClass
  stmtClass := .stmt
  PolyFams := PolyFam
  famClass := famClass
  SRSSingles_G1 := SRSSingle_G1
  SRSSingles_G2 := SRSSingle_G2
  SRSSingleValue_G1 := fun s => match s with
    | .α => X Vars.γ * X Vars.δ * X Vars.α
    | .β => X Vars.γ * X Vars.δ * X Vars.β
    | .δ => X Vars.γ * X Vars.δ * X Vars.δ
  SRSSingleValue_G2 := fun s => match s with
    | .β => X Vars.γ * X Vars.δ * X Vars.β
    | .γ => X Vars.γ * X Vars.δ * X Vars.γ
    | .δ => X Vars.γ * X Vars.δ * X Vars.δ
  SRSComponents_G1 := SRSComp_G1
  SRSComponents_G2 := SRSComp_G2
  compClass_G1 := compClass_G1
  compClass_G2 := compClass_G2
  SRSComponentValue_G1 := fun c f => match c, f with
    | .x_pow, .x_pows => X Vars.γ * X Vars.δ
    | .x_pow_times_t, .x_pows_t => X Vars.γ
    | .y, .u_stmt => X Vars.β * X Vars.δ
    | .y, .v_stmt => X Vars.α * X Vars.δ
    | .y, .w_stmt => X Vars.δ
    | .q, .u_wit => X Vars.β * X Vars.γ
    | .q, .v_wit => X Vars.α * X Vars.γ
    | .q, .w_wit => X Vars.γ
    | _, _ => 0
  SRSComponentValue_G2 := fun c f => match c, f with
    | .x_pow, .x_pows => X Vars.γ * X Vars.δ
    | _, _ => 0
  Proof_G1 := Proof_G1_Idx
  Proof_G2 := Proof_G2_Idx
  EqualityChecks := Unit
  Pairings := fun _ => PairingsIdx
  Pairings_FinEnum := fun _ => inferInstance
  verifCoeffProof_G1 := fun _ i p => match i, p with
    | .ab, .A => 1
    | .cδ, .C => 1
    | _, _ => 0
  verifCoeffProof_G2 := fun _ i p => match i, p with
    | .ab, .B => -1
    | _, _ => 0
  verifCoeffSingle_G1 := fun _ i s => match i, s with
    | .αβ, .α => 1
    | _, _ => 0
  verifCoeffSingle_G2 := fun _ i s => match i, s with
    | .αβ, .β => 1
    | .stmtγ, .γ => 1
    | .cδ, .δ => 1
    | _, _ => 0
  verifCoeffComp_G1 := fun _ i c => match i, c with
    | .stmtγ, .y => some 1
    | _, _ => none
  verifCoeffComp_G2 := fun _ _ _ => none

open SymbolicAGMScheme

/-- The target polynomial of the soundness problem, over the abstract sum variables: the QAP
relation `(∑ aᵢuᵢ)·(∑ aᵢvᵢ) − ∑ aᵢwᵢ − h·t = 0` with the witness read off proof element `C`'s
coefficients on the `q` component and the quotient `h·t` read off `C`'s coefficients on the
`xⁱ·t` column — matching the extractor and the `suffices` step of the manual soundness proof. -/
def target (F : Type) [Field F] [BEq F] [LawfulBEq F] :
    COrdMvPolynomial (SumVar (scheme F)) F :=
  (X (SumVar.stmtSum PolyFam.u_stmt)
      + X (SumVar.comp_G1 Proof_G1_Idx.C SRSComp_G1.q PolyFam.u_wit))
    * (X (SumVar.stmtSum PolyFam.v_stmt)
      + X (SumVar.comp_G1 Proof_G1_Idx.C SRSComp_G1.q PolyFam.v_wit))
  - (X (SumVar.stmtSum PolyFam.w_stmt)
      + X (SumVar.comp_G1 Proof_G1_Idx.C SRSComp_G1.q PolyFam.w_wit))
  - X (SumVar.comp_G1 Proof_G1_Idx.C SRSComp_G1.x_pow_times_t PolyFam.x_pows_t)

/-- **The abstract soundness problem of Groth16 (Type III)**: a polynomial ideal-membership
problem over the sum variables, fully circuit-independent. Its generators are the toxic-waste
coefficients of the symbolic verification equation (the abstract `h0012` … `h1122`), its target
the extracted QAP relation. Soundness of Groth16 on *every* circuit reduces to the target lying
in the radical of the ideal spanned by the generators (see
`SymbolicAGMScheme.evalSums_target_eq_zero`), which a Gröbner-basis solver can check once and
for all. -/
def soundnessProblem (F : Type) [Field F] [BEq F] [LawfulBEq F] :
    AGMProofSystemInstantiation.IdealMembershipProblem (SumVar (scheme F)) F :=
  (scheme F).soundnessProblem (target F)

/-- Concrete circuit data (QAP polynomials and vanishing-polynomial roots) as an instantiation
of the symbolic scheme. `(scheme F).toAGMProofSystem (instantiation …)` is then the concrete
Groth16 proof system for that circuit, corresponding to `Groth16TypeIII` of `Defs.lean`. -/
def instantiation {n_stmt n_wit n_var : ℕ}
    (u_stmt : Fin n_stmt → CPolynomial F) (v_stmt : Fin n_stmt → CPolynomial F)
    (w_stmt : Fin n_stmt → CPolynomial F)
    (u_wit : Fin n_wit → CPolynomial F) (v_wit : Fin n_wit → CPolynomial F)
    (w_wit : Fin n_wit → CPolynomial F)
    (r : Fin n_wit → F) :
    (scheme F).Instantiation where
  classLen := fun c => match c with
    | .stmt => n_stmt
    | .wit => n_wit
    | .var => n_var
    | .varSub1 => n_var - 1
  famPolys := fun f => match f with
    | .u_stmt => u_stmt
    | .v_stmt => v_stmt
    | .w_stmt => w_stmt
    | .u_wit => u_wit
    | .v_wit => v_wit
    | .w_wit => w_wit
    | .x_pows => fun i => CPolynomial.X ^ (i : ℕ)
    | .x_pows_t => fun i => CPolynomial.X ^ (i : ℕ)
        * ∏ j ∈ (Finset.univ : Finset (Fin n_wit)), (CPolynomial.X - CPolynomial.C (r j))

end Symbolic

end Groth16TypeIII
