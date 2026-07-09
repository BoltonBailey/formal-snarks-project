import FormalSnarksProject.Models.SymbolicAGMScheme
import FormalSnarksProject.SNARKs.Groth16TypeI.Defs

/-!
# Groth16TypeI, symbolically

This file expresses the soundness of the Type I (symmetric pairing) Groth16 of `Defs.lean` as a
polynomial ideal-membership problem over a closed variable type, ending in a
`soundnessProblem : IdealMembershipProblem` to hand to a solver.

`SymbolicAGMScheme` models the Type III setting (two groups, `Identified_Proof_Elems := []`),
so, as with `ToySnark`, we build the symbolic check polynomial directly over

    toxic waste (`Vars` = α, β, γ, δ)  ⊕  ideal variables (`Var` below).

There is a single SRS, and each of the proof elements `A`, `B`, `C` decomposes over all eight
kinds of SRS elements. The `y` and `q` QAP columns are *bundled*: one prover coefficient `cᵢ`
multiplies `βδ·u_stmt i + αδ·v_stmt i + δ·w_stmt i` (resp. the `βγ/αγ/γ`-weighted witness
columns), so each contributes three abstract family-combination variables sharing the same
underlying coefficients — abstracted independently, exactly as the `generalize` step of the
manual proof does. Slots of each proof element (`Var.pf` below):

| slot     | SRS element(s)  | variable means                                     |
| -------- | --------------- | -------------------------------------------------- |
| `.a/.b/.c/.d` | `α`,`β`,`γ`,`δ` | the scalar coefficient on that element        |
| `.x`     | `x^i`           | `∑ cᵢ·x^i`                                         |
| `.xt`    | `x^i·t`         | `∑ cᵢ·x^i·t`   (the quotient slots)                |
| `.y_u/.y_v/.y_w` | `y i`   | `∑ cᵢ·u_stmt i`, `∑ cᵢ·v_stmt i`, `∑ cᵢ·w_stmt i`  |
| `.q_u/.q_v/.q_w` | `q i`   | `∑ cᵢ·u_wit i`, `∑ cᵢ·v_wit i`, `∑ cᵢ·w_wit i`     |

plus the statement sums `∑ stmt i · u_stmt i` etc. (`Var.S_u/S_v/S_w`).

The target encodes the QAP relation with the witness read off `C`'s coefficients on the `q`
elements and the quotient off `C`'s `x^i·t` slots, matching the extractor of the manual proof.
Note that the manual proof genuinely needs *radical* (not plain) ideal membership: its case
analysis starts from `A_α·B_α = 0` and resolves squares with `mul_self_eq_zero`. The
Nullstellensatz-style SMT encoding of `SMT/Export.lean` decides exactly radical membership, so
this is covered.
-/

open CPoly CPoly.CMvPolynomial

namespace Groth16TypeI

namespace Symbolic

instance : Repr Proof_Idx := ⟨fun p _ => match p with | .A => "A" | .B => "B" | .C => "C"⟩

/-- The SRS-class slots of a proof element (see the module docstring). -/
inductive Slot : Type where
  | a : Slot
  | b : Slot
  | c : Slot
  | d : Slot
  | x : Slot
  | xt : Slot
  | y_u : Slot
  | y_v : Slot
  | y_w : Slot
  | q_u : Slot
  | q_v : Slot
  | q_w : Slot
deriving DecidableEq

instance : FinEnum Slot :=
  .ofList [.a, .b, .c, .d, .x, .xt, .y_u, .y_v, .y_w, .q_u, .q_v, .q_w]
    (fun x => by cases x <;> simp)
instance : Repr Slot := ⟨fun s _ => match s with
  | .a => "alpha" | .b => "beta" | .c => "gamma" | .d => "delta"
  | .x => "x_pow" | .xt => "x_pow_times_t"
  | .y_u => "y_u_stmt" | .y_v => "y_v_stmt" | .y_w => "y_w_stmt"
  | .q_u => "q_u_wit" | .q_v => "q_v_wit" | .q_w => "q_w_wit"⟩

/-- The statement-weighted family sums. -/
inductive StmtVar : Type where
  | S_u : StmtVar
  | S_v : StmtVar
  | S_w : StmtVar
deriving DecidableEq

instance : FinEnum StmtVar := .ofList [.S_u, .S_v, .S_w] (fun x => by cases x <;> simp)

/-- The ideal variables of the abstract soundness problem. -/
def Var : Type := (Proof_Idx × Slot) ⊕ StmtVar

instance : DecidableEq Var := inferInstanceAs (DecidableEq ((Proof_Idx × Slot) ⊕ StmtVar))
instance : FinEnum Var := inferInstanceAs (FinEnum ((Proof_Idx × Slot) ⊕ StmtVar))

/-- The prover's sum variable for slot `s` of proof element `p`. -/
def Var.pf (p : Proof_Idx) (s : Slot) : Var := Sum.inl (p, s)

/-- The statement sum `∑ i, stmt i · u_stmt i`. -/
def Var.S_u : Var := Sum.inr .S_u
/-- The statement sum `∑ i, stmt i · v_stmt i`. -/
def Var.S_v : Var := Sum.inr .S_v
/-- The statement sum `∑ i, stmt i · w_stmt i`. -/
def Var.S_w : Var := Sum.inr .S_w

instance : Repr Var := ⟨fun v _ => match v with
  | Sum.inl (p, s) => repr p ++ "_" ++ repr s
  | Sum.inr .S_u => "u_io"
  | Sum.inr .S_v => "v_io"
  | Sum.inr .S_w => "w_io"⟩

/-- Variables of the symbolic check polynomial. -/
abbrev SymVars : Type := Vars ⊕ Var

variable (F : Type) [Field F] [BEq F] [LawfulBEq F]

/-- Shorthand for a toxic-waste sample inside the symbolic ring. -/
private def tox (v : Vars) : CMvPolynomial SymVars F := X (Sum.inl v)

/-- The symbolic AGM expansion of a proof element over the single SRS, transcribing the
(`γδ`-multiplied) SRS values of `Defs.lean`. -/
def pfPoly (p : Proof_Idx) : CMvPolynomial SymVars F :=
  tox F .γ * tox F .δ * tox F .α * X (Sum.inr (Var.pf p .a))
    + tox F .γ * tox F .δ * tox F .β * X (Sum.inr (Var.pf p .b))
    + tox F .γ * tox F .δ * tox F .γ * X (Sum.inr (Var.pf p .c))
    + tox F .γ * tox F .δ * tox F .δ * X (Sum.inr (Var.pf p .d))
    + tox F .γ * tox F .δ * X (Sum.inr (Var.pf p .x))
    + tox F .γ * X (Sum.inr (Var.pf p .xt))
    + tox F .β * tox F .δ * X (Sum.inr (Var.pf p .y_u))
    + tox F .α * tox F .δ * X (Sum.inr (Var.pf p .y_v))
    + tox F .δ * X (Sum.inr (Var.pf p .y_w))
    + tox F .β * tox F .γ * X (Sum.inr (Var.pf p .q_u))
    + tox F .α * tox F .γ * X (Sum.inr (Var.pf p .q_v))
    + tox F .γ * X (Sum.inr (Var.pf p .q_w))

/-- The symbolic verification-check polynomial, mirroring the verifier of `Defs.lean`:
`−A·B + (γδα)·(γδβ) + (∑ stmt i · y i)·(γδγ) + C·(γδδ)`. -/
def symCheckPoly : CMvPolynomial SymVars F :=
  - (pfPoly F .A * pfPoly F .B)
    + (tox F .γ * tox F .δ * tox F .α) * (tox F .γ * tox F .δ * tox F .β)
    + (tox F .β * tox F .δ * X (Sum.inr Var.S_u)
        + tox F .α * tox F .δ * X (Sum.inr Var.S_v)
        + tox F .δ * X (Sum.inr Var.S_w))
      * (tox F .γ * tox F .δ * tox F .γ)
    + pfPoly F .C * (tox F .γ * tox F .δ * tox F .δ)

/-- The generators of the soundness ideal: the coefficients of the symbolic check polynomial
with respect to the toxic-waste monomials. -/
def generators : List (CMvPolynomial Var F) :=
  SymbolicAGMScheme.coeffGenerators (symCheckPoly F)

/-- The target polynomial: the QAP relation with the witness read off `C`'s `q` slots and the
quotient off `C`'s `x^i·t` slots, matching the extractor and the `suffices` step of the manual
soundness proof. -/
def target : CMvPolynomial Var F :=
  (X Var.S_u + X (Var.pf .C .q_u)) * (X Var.S_v + X (Var.pf .C .q_v))
    - (X Var.S_w + X (Var.pf .C .q_w))
    - X (Var.pf .C .xt)

/-- **The abstract soundness problem of Groth16 (Type I)**: a polynomial ideal-membership
problem over the sum variables, fully circuit-independent. The manual proof's case analysis
(`A_α·B_α = 0`, squares killed by `mul_self_eq_zero`) means the target lies in the *radical* of
the generator ideal, not necessarily the ideal itself. -/
def soundnessProblem : AGMProofSystemInstantiation.IdealMembershipProblem Var F where
  generators := generators F
  target := target F

end Symbolic

end Groth16TypeI
