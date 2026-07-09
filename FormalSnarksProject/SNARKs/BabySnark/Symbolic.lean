import FormalSnarksProject.Models.SymbolicAGMScheme
import FormalSnarksProject.SNARKs.BabySnark.Defs

/-!
# BabySNARK, symbolically

This file expresses the soundness of BabySNARK as a polynomial ideal-membership problem over a
closed variable type, in the same spirit as `ToySnark/Symbolic.lean` — ending in a
`soundnessProblem : IdealMembershipProblem` to hand to a solver.

BabySNARK does not fit `SymbolicAGMScheme`: it is a Type I SNARK whose proof elements come in
two identified copies (one per pairing side), and its verifier assembles `t(τ)`, the constant
`1` and the statement polynomial `u_io(τ)` out of the `τ^i` SRS elements. So we build the
symbolic check polynomials directly over

    toxic waste (`Vars` = β, γ)  ⊕  ideal variables (`Var` below),

and extract the generators with `SymbolicAGMScheme.coeffGenerators`.

Each copy of each proof element decomposes over the four SRS classes, giving the sum variables
(`Var.pf` below; `g` marks the pairing side):

| slot   | SRS elements    | variable means                                        |
| ------ | --------------- | ----------------------------------------------------- |
| `.tau` | `τ^i`           | `∑ i, cᵢ · τ^i`   (a polynomial in `τ`)               |
| `.gm`  | `γ`             | the scalar coefficient on `γ`                         |
| `.gmb` | `γβ`            | the scalar coefficient on `γβ`                        |
| `.u`   | `β·u_wit i`     | `∑ i, cᵢ · u_wit i`   (a witness-family combination)  |

together with the two verifier-side quantities `t` (the vanishing polynomial, which the
verifier encodes faithfully in the `τ^i` elements by the degree hypotheses of the manual proof)
and `u_io` (the statement-weighted `∑ i, stmt i · u_stmt i`).

The generators are the toxic-waste-monomial coefficients of check I (the square span check),
check II (`B·γ = γβ·V`), and the three Type I identification equations (G1 copy = G2 copy, one
per proof element). The target encodes the square span relation `(u_io + ∑ wit i · u_wit i)² − 1
≡ 0 mod t` with the witness read off `B`'s `β·u_wit` slots and the quotient
`t + (H's τ-part)` — matching the extractor and `suffices` step of the manual proof in
`Soundness.lean`.
-/

open CPoly CPoly.CMvPolynomial

namespace BabySNARK

namespace Symbolic

/-- The pairing side a proof-element copy lives on (BabySNARK is Type I, so the model keeps a
copy of each proof element per side, related by the identification equations). -/
inductive Grp : Type where
  | g1 : Grp
  | g2 : Grp
deriving DecidableEq

instance : FinEnum Grp := .ofList [.g1, .g2] (fun x => by cases x <;> simp)
instance : Repr Grp := ⟨fun g _ => match g with | .g1 => "G1" | .g2 => "G2"⟩

instance : Repr Proof_Idx := ⟨fun p _ => match p with | .H => "H" | .V => "V" | .B => "B"⟩

/-- The SRS-class slots of a proof-element copy (see the module docstring). -/
inductive Slot : Type where
  | tau : Slot
  | gm : Slot
  | gmb : Slot
  | u : Slot
deriving DecidableEq

instance : FinEnum Slot := .ofList [.tau, .gm, .gmb, .u] (fun x => by cases x <;> simp)
instance : Repr Slot := ⟨fun s _ => match s with
  | .tau => "tau" | .gm => "gamma" | .gmb => "gammabeta" | .u => "u"⟩

/-- The verifier-side quantities appearing in the checks and the target. -/
inductive VerifierVar : Type where
  | t : VerifierVar
  | u_io : VerifierVar
deriving DecidableEq

instance : FinEnum VerifierVar := .ofList [.t, .u_io] (fun x => by cases x <;> simp)

/-- The ideal variables of the abstract soundness problem. A `def` (not `abbrev`) so that the
`Repr` instance below keeps its own head symbol, as with `SymbolicAGMScheme.SumVar`. -/
def Var : Type := (Grp × Proof_Idx × Slot) ⊕ VerifierVar

instance : DecidableEq Var :=
  inferInstanceAs (DecidableEq ((Grp × Proof_Idx × Slot) ⊕ VerifierVar))
instance : FinEnum Var := inferInstanceAs (FinEnum ((Grp × Proof_Idx × Slot) ⊕ VerifierVar))

/-- The prover's sum variable for slot `s` of the side-`g` copy of proof element `p`. -/
def Var.pf (g : Grp) (p : Proof_Idx) (s : Slot) : Var := Sum.inl (g, p, s)

/-- The vanishing polynomial `t`, as an abstract indeterminate. -/
def Var.t : Var := Sum.inr .t

/-- The statement polynomial `u_io = ∑ i, stmt i · u_stmt i`, as an abstract indeterminate. -/
def Var.u_io : Var := Sum.inr .u_io

instance : Repr Var := ⟨fun v _ => match v with
  | Sum.inl (g, p, s) => repr p ++ "_" ++ repr g ++ "_" ++ repr s
  | Sum.inr .t => "t"
  | Sum.inr .u_io => "u_io"⟩

/-- Variables of the symbolic check polynomials: the toxic-waste samples and the ideal
variables. -/
abbrev SymVars : Type := Vars ⊕ Var

variable (F : Type) [Field F] [BEq F] [LawfulBEq F]

/-- The symbolic AGM expansion of the side-`g` copy of proof element `p` over the SRS classes:
`τ-part + γ-slot·γ + γβ-slot·γβ + β·(u_wit-part)`. -/
def pfPoly (g : Grp) (p : Proof_Idx) : CMvPolynomial SymVars F :=
  X (Sum.inr (Var.pf g p .tau))
    + X (Sum.inr (Var.pf g p .gm)) * X (Sum.inl Vars.γ)
    + X (Sum.inr (Var.pf g p .gmb)) * (X (Sum.inl Vars.γ) * X (Sum.inl Vars.β))
    + X (Sum.inl Vars.β) * X (Sum.inr (Var.pf g p .u))

/-- Check I of the verifier (the square span check), mirroring `Defs.lean`:
`(H + t)·t + 1 − (V₁ + u_io)·(V₂ + u_io)`, with `t` and `u_io` the verifier's (faithful)
`τ^i`-encodings of the vanishing and statement polynomials. -/
def checkI : CMvPolynomial SymVars F :=
  (pfPoly F .g1 .H + X (Sum.inr Var.t)) * X (Sum.inr Var.t)
    + 1
    - (pfPoly F .g1 .V + X (Sum.inr Var.u_io)) * (pfPoly F .g2 .V + X (Sum.inr Var.u_io))

/-- Check II of the verifier: `B·γ − γβ·V₂`. -/
def checkII : CMvPolynomial SymVars F :=
  pfPoly F .g1 .B * X (Sum.inl Vars.γ)
    - (X (Sum.inl Vars.γ) * X (Sum.inl Vars.β)) * pfPoly F .g2 .V

/-- The Type I identification of the two copies of proof element `p`: their AGM expansions
agree as polynomials. -/
def identPoly (p : Proof_Idx) : CMvPolynomial SymVars F :=
  pfPoly F .g1 p - pfPoly F .g2 p

/-- The generators of the soundness ideal: the coefficients of the two check polynomials and the
three identification polynomials with respect to the toxic-waste monomials, each a polynomial in
the ideal variables. These are the abstract counterparts of the `h1eqnI`, `h2eqnII`, `h3eqnV`
(and unused siblings) of the manual soundness proof. -/
def generators : List (CMvPolynomial Var F) :=
  ([checkI F, checkII F, identPoly F .H, identPoly F .V, identPoly F .B]).flatMap
    SymbolicAGMScheme.coeffGenerators

/-- The target polynomial of the soundness problem: the square span relation
`(u_io + ∑ wit i · u_wit i)² − 1 = (t + H's τ-part)·t`, with the witness read off `B`'s
`β·u_wit` slots (matching the extractor of the manual proof) and the quotient from the
`suffices` step. -/
def target : CMvPolynomial Var F :=
  (X Var.u_io + X (Var.pf .g1 .B .u)) * (X Var.u_io + X (Var.pf .g1 .B .u))
    - 1
    - (X Var.t + X (Var.pf .g1 .H .tau)) * X Var.t

/-- **The abstract soundness problem of BabySNARK**: a polynomial ideal-membership problem over
the sum variables. Soundness reduces to the target lying in the radical of the ideal spanned by
the generators; the manual proof's `linear_combination` certificate is a (plain) membership
certificate for exactly this problem. -/
def soundnessProblem : AGMProofSystemInstantiation.IdealMembershipProblem Var F where
  generators := generators F
  target := target F

end Symbolic

end BabySNARK
