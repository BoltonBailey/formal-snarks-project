/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import FormalSnarksProject.Models.SymbolicAGMScheme
public import FormalSnarksProject.SNARKs.ToySnark.Defs
public import FormalSnarksProject.ToMathlib.FinEnumOrd

/-!
# ToySnark, symbolically

This file expresses the soundness of the toy SNARK of `Defs.lean` as a polynomial
ideal-membership problem over a closed variable type, in the same spirit as
`Groth16TypeIII/Symbolic.lean` — ending in a `soundnessProblem : IdealMembershipProblem` to hand
to a solver.

Unlike Groth16, ToySnark is *not* an instance of `SymbolicAGMScheme`: its verifier weights the
**singleton** SRS elements `[α]`, `[β]` by the statement entries `x`, `y`, `z` directly, whereas
`SymbolicAGMScheme` only supports statement-weighting on `Fin`-indexed component columns (and
ToySnark has no polynomial families at all — it is already circuit-independent as written). So
instead of going through a scheme structure, this file builds the symbolic check polynomial
directly over

    toxic waste (`Vars` = α, β)  ⊕  ideal variables (`Var` = prover coefficients + statement),

exactly the `IdealVars` split of the generic reduction in `StraightforwardAGMProofSystem.lean`
(where the statement entries are indeterminates, making the problem statement-independent), and
extracts the generators with `SymbolicAGMScheme.coeffGenerators`.

Correspondence with the manual proof in `Soundness.lean`:

| manual proof object | here                                              |
| ------------------- | ------------------------------------------------- |
| `prover.fst Pf .α`  | `Var.Pf_α` (also the extracted witness `A`)       |
| `prover.fst Pf .β`  | `Var.Pf_β` (also the extracted witness `B`)       |
| `stmt x/y/z`        | `Var.x` / `Var.y` / `Var.z`                       |
| `h20`, `h11`, `h02` | the three `generators`                            |
| the relation `A·y = z ∨ B·x = z` | `target = (Pf_α·y − z)·(Pf_β·x − z)`             |

(the disjunction is encoded as a product: over a field, a product is zero iff a factor is).
-/

@[expose] public section

open CPoly CPoly.COrdMvPolynomial

namespace ToySnark

namespace Symbolic

/-- The ideal variables of the abstract soundness problem: the prover's coefficients of the
single proof element `Pf` on the two SRS elements (which are also the extracted witness entries
`A`, `B`), and the statement entries treated as indeterminates. -/
inductive Var : Type where
  | Pf_α : Var
  | Pf_β : Var
  | x : Var
  | y : Var
  | z : Var
deriving DecidableEq

instance : FinEnum Var := .ofList [.Pf_α, .Pf_β, .x, .y, .z] (fun v => by cases v <;> simp)

instance : Ord Var := FinEnum.toOrd
instance : Std.TransOrd Var := FinEnum.toOrd.transOrd
instance : Std.LawfulEqOrd Var := FinEnum.toOrd.lawfulEqOrd

instance : Repr Var := ⟨fun v _ => match v with
  | .Pf_α => "Pf_α" | .Pf_β => "Pf_β" | .x => "x" | .y => "y" | .z => "z"⟩

/-- Variables of the symbolic check polynomial: the toxic-waste samples and the ideal
variables. -/
abbrev SymVars : Type := Vars ⊕ Var

instance : Ord SymVars := FinEnum.toOrd
instance : Std.TransOrd SymVars := FinEnum.toOrd.transOrd
instance : Std.LawfulEqOrd SymVars := FinEnum.toOrd.lawfulEqOrd

variable (F : Type) [Field F] [BEq F] [LawfulBEq F]

/-- The symbolic verification-check polynomial, mirroring the verifier of `Defs.lean` exactly:
the `lhs` pairing is `e(Pf, x·[α] + y·[β])` with `Pf = Pf_α·α + Pf_β·β` its AGM expansion, the
`rhs` pairing is `e(z·[α], −[β])`. -/
def symCheckPoly : COrdMvPolynomial (SymVars) F :=
  (X (Sum.inr Var.Pf_α) * X (Sum.inl Vars.α) + X (Sum.inr Var.Pf_β) * X (Sum.inl Vars.β))
      * (X (Sum.inr Var.x) * X (Sum.inl Vars.α) + X (Sum.inr Var.y) * X (Sum.inl Vars.β))
    + (X (Sum.inr Var.z) * X (Sum.inl Vars.α)) * (- X (Sum.inl Vars.β))

/-- The generators of the soundness ideal: the coefficients of the symbolic check polynomial with
respect to the toxic-waste monomials (`α²`, `αβ`, `β²`), each a polynomial in the ideal
variables. These are the abstract counterparts of the `h20`, `h11`, `h02` equations of the manual
soundness proof. -/
def generators : List (COrdMvPolynomial Var F) :=
  SymbolicAGMScheme.coeffGenerators (symCheckPoly F)

/-- The target polynomial of the soundness problem: the relation
`A·y = z ∨ B·x = z` of `Soundness.lean`, with the witness `(A, B)` read off the prover's
coefficients `(Pf_α, Pf_β)` (matching the extractor of the manual proof) and the disjunction
encoded as a product (zero iff one of the factors is, over a field). -/
def target : COrdMvPolynomial Var F :=
  (X Var.Pf_α * X Var.y - X Var.z) * (X Var.Pf_β * X Var.x - X Var.z)

/-- **The abstract soundness problem of ToySnark**: a polynomial ideal-membership problem over
the prover-coefficient and statement variables. Soundness reduces to the target lying in the
radical of the ideal spanned by the generators; the manual proof's `integral_domain_tactic` step
is an implicit certificate of exactly this membership. -/
def soundnessProblem : AGMProofSystemInstantiation.IdealMembershipProblem Var F where
  generators := generators F
  target := target F

end Symbolic

end ToySnark
