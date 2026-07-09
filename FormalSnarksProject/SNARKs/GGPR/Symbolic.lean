import FormalSnarksProject.Models.SymbolicAGMScheme
import FormalSnarksProject.SNARKs.GGPR.Defs

/-!
# GGPR, symbolically

This file expresses the soundness of the GGPR SNARK of `Defs.lean` as a polynomial
ideal-membership problem over a closed variable type, ending in a
`soundnessProblem : IdealMembershipProblem` to hand to a solver.

GGPR does not fit `SymbolicAGMScheme`: several *singleton* SRS elements (`VK_v_0`, `VK_w_0`,
`VK_t`) carry fixed circuit polynomials in the unbounded sample `s`, and the verifier both
statement-weights the `VK_v_stmt` column and uses those polynomial-valued singles directly. So,
as with `ToySnark`, we build the five symbolic check polynomials directly over

    toxic waste (`Vars` = α, β_v, β_w, β_y, γ)  ⊕  ideal variables (`Var` below),

and extract the generators with `SymbolicAGMScheme.coeffGenerators`.

Each proof element (indexed by `PfElem := Proof_G1_Idx ⊕ Proof_G2_Idx`; GGPR keeps both SRS
copies equal, so the expansion is the same on either side) decomposes over the SRS classes,
giving the sum variables (`Var.pf` below):

| slot     | SRS element(s)   | variable means                          |
| -------- | ---------------- | --------------------------------------- |
| `.s`     | `s^i`            | `∑ cᵢ·s^i`                              |
| `.αs`    | `α·s^i`          | `∑ cᵢ·s^i`  (the `α`-shadowed copy)     |
| `.v/.w`  | `v_wit i`,`w_wit i` | `∑ cᵢ·v_wit i`, `∑ cᵢ·w_wit i`       |
| `.αv/.αw`| `α·v_wit i`, …   | their `α`-shadowed copies               |
| `.βv/.βw`| `β_v·v_wit i`, … | their `β`-shadowed copies               |
| `.one/.α/.γ/.βvγ/.βwγ` | `VK_1`,`VK_α`,`VK_γ`,`VK_βv_γ`,`VK_βw_γ` | scalar coefficients |
| `.v0/.w0/.t` | `VK_v_0`, …  | scalar coefficients (times the fixed polynomials `v_0`,`w_0`,`t`) |
| `.vstmt` | `VK_v_stmt i`    | `∑ cᵢ·v_stmt i`                         |

plus the verifier-side quantities `v_0`, `w_0`, `t` (fixed circuit polynomials as abstract
indeterminates) and `v_io = ∑ stmt i · v_stmt i`.

The target encodes the QSP relation with the witness read off `Y`'s `β_v`/`β_w` slots and the
quotient off `H`'s full toxic-waste-free combination, matching the extractor and `suffices`
step of the manual proof in `Soundness.lean` (only checks I and V are needed there; we include
all five checks' generators for faithfulness).
-/

open CPoly CPoly.CMvPolynomial

namespace GGPR

namespace Symbolic

instance : Repr Proof_G1_Idx := ⟨fun p _ => match p with
  | .V_mid => "V_mid" | .V_mid' => "V_mid_p" | .W' => "W_p" | .Y => "Y" | .H' => "H_p"⟩
instance : Repr Proof_G2_Idx := ⟨fun p _ => match p with | .W => "W" | .H => "H"⟩

/-- The proof elements, both groups together. -/
abbrev PfElem : Type := Proof_G1_Idx ⊕ Proof_G2_Idx

/-- The SRS-class slots of a proof element (see the module docstring). -/
inductive Slot : Type where
  | s : Slot
  | αs : Slot
  | v : Slot
  | w : Slot
  | αv : Slot
  | αw : Slot
  | βv : Slot
  | βw : Slot
  | one : Slot
  | α : Slot
  | γ : Slot
  | βvγ : Slot
  | βwγ : Slot
  | v0 : Slot
  | w0 : Slot
  | t : Slot
  | vstmt : Slot
deriving DecidableEq

instance : FinEnum Slot :=
  .ofList [.s, .αs, .v, .w, .αv, .αw, .βv, .βw, .one, .α, .γ, .βvγ, .βwγ, .v0, .w0, .t, .vstmt]
    (fun x => by cases x <;> simp)
instance : Repr Slot := ⟨fun s _ => match s with
  | .s => "s_pow" | .αs => "alpha_s_pow"
  | .v => "v_wit" | .w => "w_wit" | .αv => "alpha_v_wit" | .αw => "alpha_w_wit"
  | .βv => "beta_v_wit" | .βw => "beta_w_wit"
  | .one => "one" | .α => "alpha" | .γ => "gamma" | .βvγ => "beta_v_gamma"
  | .βwγ => "beta_w_gamma"
  | .v0 => "v_0" | .w0 => "w_0" | .t => "t" | .vstmt => "v_stmt"⟩

/-- The verifier-side quantities appearing in the checks and the target. -/
inductive VerifierVar : Type where
  | v0 : VerifierVar
  | w0 : VerifierVar
  | t : VerifierVar
  | v_io : VerifierVar
deriving DecidableEq

instance : FinEnum VerifierVar := .ofList [.v0, .w0, .t, .v_io] (fun x => by cases x <;> simp)

/-- The ideal variables of the abstract soundness problem. -/
def Var : Type := (PfElem × Slot) ⊕ VerifierVar

instance : DecidableEq Var := inferInstanceAs (DecidableEq ((PfElem × Slot) ⊕ VerifierVar))
instance : FinEnum Var := inferInstanceAs (FinEnum ((PfElem × Slot) ⊕ VerifierVar))

/-- The prover's sum variable for slot `s` of proof element `p`. -/
def Var.pf (p : PfElem) (s : Slot) : Var := Sum.inl (p, s)

/-- The fixed circuit polynomial `v_0`, as an abstract indeterminate. -/
def Var.v0 : Var := Sum.inr .v0
/-- The fixed circuit polynomial `w_0`, as an abstract indeterminate. -/
def Var.w0 : Var := Sum.inr .w0
/-- The vanishing polynomial `t`, as an abstract indeterminate. -/
def Var.t : Var := Sum.inr .t
/-- The statement polynomial `v_io = ∑ i, stmt i · v_stmt i`. -/
def Var.v_io : Var := Sum.inr .v_io

instance : Repr Var := ⟨fun v _ => match v with
  | Sum.inl (Sum.inl p, s) => repr p ++ "_" ++ repr s
  | Sum.inl (Sum.inr p, s) => repr p ++ "_" ++ repr s
  | Sum.inr .v0 => "v_0"
  | Sum.inr .w0 => "w_0"
  | Sum.inr .t => "t"
  | Sum.inr .v_io => "v_io"⟩

/-- Variables of the symbolic check polynomials. -/
abbrev SymVars : Type := Vars ⊕ Var

variable (F : Type) [Field F] [BEq F] [LawfulBEq F]

/-- Shorthand for a toxic-waste sample inside the symbolic ring. -/
private def tox (v : Vars) : CMvPolynomial SymVars F := X (Sum.inl v)

/-- Shorthand for an ideal variable inside the symbolic ring. -/
private def idl (v : Var) : CMvPolynomial SymVars F := X (Sum.inr v)

/-- The symbolic AGM expansion of a proof element over the SRS, transcribing the SRS values of
`Defs.lean`. -/
def pfPoly (p : PfElem) : CMvPolynomial SymVars F :=
  idl F (Var.pf p .s)
    + tox F .α * idl F (Var.pf p .αs)
    + idl F (Var.pf p .v)
    + idl F (Var.pf p .w)
    + tox F .α * idl F (Var.pf p .αv)
    + tox F .α * idl F (Var.pf p .αw)
    + tox F .β_v * idl F (Var.pf p .βv)
    + tox F .β_w * idl F (Var.pf p .βw)
    + idl F (Var.pf p .one)
    + tox F .α * idl F (Var.pf p .α)
    + tox F .γ * idl F (Var.pf p .γ)
    + tox F .β_v * tox F .γ * idl F (Var.pf p .βvγ)
    + tox F .β_w * tox F .γ * idl F (Var.pf p .βwγ)
    + idl F (Var.pf p .v0) * idl F Var.v0
    + idl F (Var.pf p .w0) * idl F Var.w0
    + idl F (Var.pf p .t) * idl F Var.t
    + idl F (Var.pf p .vstmt)

/-- Check I of the verifier: `(V_mid + v_0 + v_io)·(W + w_0) − t·H`. -/
def checkI : CMvPolynomial SymVars F :=
  (pfPoly F (Sum.inl .V_mid) + idl F Var.v0 + idl F Var.v_io)
      * (pfPoly F (Sum.inr .W) + idl F Var.w0)
    - idl F Var.t * pfPoly F (Sum.inr .H)

/-- Check II of the verifier: `V_mid' − α·V_mid`. -/
def checkII : CMvPolynomial SymVars F :=
  pfPoly F (Sum.inl .V_mid') - tox F .α * pfPoly F (Sum.inl .V_mid)

/-- Check III of the verifier: `W' − α·W`. -/
def checkIII : CMvPolynomial SymVars F :=
  pfPoly F (Sum.inl .W') - tox F .α * pfPoly F (Sum.inr .W)

/-- Check IV of the verifier: `H' − α·H`. -/
def checkIV : CMvPolynomial SymVars F :=
  pfPoly F (Sum.inl .H') - tox F .α * pfPoly F (Sum.inr .H)

/-- Check V of the verifier: `Y·γ − β_v γ·V_mid − β_w γ·W`. -/
def checkV : CMvPolynomial SymVars F :=
  pfPoly F (Sum.inl .Y) * tox F .γ
    - tox F .β_v * tox F .γ * pfPoly F (Sum.inl .V_mid)
    - tox F .β_w * tox F .γ * pfPoly F (Sum.inr .W)

/-- The generators of the soundness ideal: the coefficients of the five check polynomials with
respect to the toxic-waste monomials, each a polynomial in the ideal variables. -/
def generators : List (CMvPolynomial Var F) :=
  ([checkI F, checkII F, checkIII F, checkIV F, checkV F]).flatMap
    SymbolicAGMScheme.coeffGenerators

/-- The target polynomial of the soundness problem: the QSP relation
`(v_0 + v_io + V)·(w_0 + W) = h·t` with the witness read off `Y`'s `β_v`/`β_w` slots (matching
the extractor of the manual proof) and the quotient `h` read off `H`'s full toxic-waste-free
combination (its `s`-powers, `v_wit`/`w_wit`/`v_stmt` parts, `VK_1` constant, and
`v_0`/`w_0`/`t`-multiplied scalars — the `suffices` step of the manual proof). -/
def target : CMvPolynomial Var F :=
  (X Var.v0 + X Var.v_io + X (Var.pf (Sum.inl .Y) .βv))
      * (X Var.w0 + X (Var.pf (Sum.inl .Y) .βw))
    - (X (Var.pf (Sum.inr .H) .s)
        + X (Var.pf (Sum.inr .H) .v)
        + X (Var.pf (Sum.inr .H) .w)
        + X (Var.pf (Sum.inr .H) .one)
        + X (Var.pf (Sum.inr .H) .v0) * X Var.v0
        + X (Var.pf (Sum.inr .H) .w0) * X Var.w0
        + X (Var.pf (Sum.inr .H) .t) * X Var.t
        + X (Var.pf (Sum.inr .H) .vstmt))
      * X Var.t

/-- **The abstract soundness problem of GGPR**: a polynomial ideal-membership problem over the
sum variables, fully circuit-independent. -/
def soundnessProblem : AGMProofSystemInstantiation.IdealMembershipProblem Var F where
  generators := generators F
  target := target F

end Symbolic

end GGPR
