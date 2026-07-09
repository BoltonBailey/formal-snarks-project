import FormalSnarksProject.Models.SymbolicAGMScheme
import FormalSnarksProject.SNARKs.Pinocchio.Defs

/-!
# Pinocchio, symbolically

This file expresses the soundness of the Pinocchio SNARK of `Defs.lean` as a polynomial
ideal-membership problem over a closed variable type, ending in a
`soundnessProblem : IdealMembershipProblem` to hand to a solver.

Pinocchio does not fit `SymbolicAGMScheme`: it is a Type I SNARK with an identified proof
element (`W_mid` appears on both pairing sides and the verifier requires the two copies to
agree), several singleton SRS elements carry fixed circuit polynomials (`VK_t`, `VK_v_0`, …),
and the `EK_β_v_w_y` column is *bundled* (one prover coefficient `cᵢ` multiplies
`β(r_v·v_wit i + r_w·w_wit i + r_v r_w·y_wit i)`). So, as with `ToySnark`, we build the five
symbolic check polynomials and the identification polynomial directly over

    toxic waste (`Vars` = r_v, r_w, α_v, α_w, α_y, β, γ)  ⊕  ideal variables (`Var` below),

and extract the generators with `SymbolicAGMScheme.coeffGenerators`.

Each proof element (indexed by `PfElem := Proof_G1_Idx ⊕ Proof_G2_Idx`; the two SRS copies are
equal) decomposes over the SRS classes, giving the sum variables (`Var.pf` below), exactly the
quantities the `generalize` step of the manual proof abstracts over:

| slot            | SRS element(s)      | variable means                                  |
| --------------- | ------------------- | ----------------------------------------------- |
| `.v/.w/.y`      | `EK_v/w/y i`        | `∑ cᵢ·v_wit i`, `∑ cᵢ·w_wit i`, `∑ cᵢ·y_wit i`  |
| `.αv/.αw/.αy`   | `EK_α_v/w/y i`      | their `α`-shadowed copies                       |
| `.s`            | `EK_s_pow i`        | `∑ cᵢ·s^i`                                      |
| `.βv/.βw/.βy`   | `EK_β_v_w_y i`      | as `.v/.w/.y` (shared `cᵢ`, abstracted independently) |
| `.one/.cαv/.cαw/.cαy/.cγ/.cβγ` | `VK_1`, `VK_α_v`, …, `VK_βγ` | scalar coefficients  |
| `.ct/.cv0/.cw0/.cy0` | `VK_t`, `VK_v_0`, … | scalar coefficients (times the fixed polynomials) |
| `.vs/.ws/.ys`   | `VK_v/w/y_stmt i`   | `∑ cᵢ·v_stmt i`, etc.                           |

plus the verifier-side quantities `t`, `v_0`, `w_0`, `y_0` (fixed circuit polynomials as
abstract indeterminates) and the statement sums `v_io`, `w_io`, `y_io`.

The generators are the toxic-waste-monomial coefficients of checks I–V and of the `W_mid`
identification (G1 copy = G2 copy). The target encodes the QAP relation with the witness read
off `Z`'s `EK_β_v_w_y` slots and the quotient `H_1 + H_s` — matching the extractor and
`suffices` step of the manual proof in `Soundness.lean` (which genuinely needs the
identification and the `VK_1` quotient term).
-/

open CPoly CPoly.CMvPolynomial

namespace Pinocchio

namespace Symbolic

instance : Repr Proof_G1_Idx := ⟨fun p _ => match p with
  | .V_mid => "V_mid" | .V_mid' => "V_mid_p"
  | .W_mid => "W_mid_G1" | .W_mid' => "W_mid_p"
  | .Y_mid => "Y_mid" | .Y_mid' => "Y_mid_p" | .Z => "Z"⟩
instance : Repr Proof_G2_Idx := ⟨fun p _ => match p with
  | .W_mid => "W_mid_G2" | .H => "H"⟩

/-- The proof elements, both groups together. -/
abbrev PfElem : Type := Proof_G1_Idx ⊕ Proof_G2_Idx

/-- The SRS-class slots of a proof element (see the module docstring). -/
inductive Slot : Type where
  | v : Slot
  | w : Slot
  | y : Slot
  | αv : Slot
  | αw : Slot
  | αy : Slot
  | s : Slot
  | βv : Slot
  | βw : Slot
  | βy : Slot
  | one : Slot
  | cαv : Slot
  | cαw : Slot
  | cαy : Slot
  | cγ : Slot
  | cβγ : Slot
  | ct : Slot
  | cv0 : Slot
  | cw0 : Slot
  | cy0 : Slot
  | vs : Slot
  | ws : Slot
  | ys : Slot
deriving DecidableEq

instance : FinEnum Slot :=
  .ofList [.v, .w, .y, .αv, .αw, .αy, .s, .βv, .βw, .βy, .one, .cαv, .cαw, .cαy, .cγ, .cβγ,
      .ct, .cv0, .cw0, .cy0, .vs, .ws, .ys]
    (fun x => by cases x <;> simp)
instance : Repr Slot := ⟨fun sl _ => match sl with
  | .v => "v_wit" | .w => "w_wit" | .y => "y_wit"
  | .αv => "alpha_v_wit" | .αw => "alpha_w_wit" | .αy => "alpha_y_wit"
  | .s => "s_pow"
  | .βv => "beta_v_wit" | .βw => "beta_w_wit" | .βy => "beta_y_wit"
  | .one => "one" | .cαv => "alpha_v" | .cαw => "alpha_w" | .cαy => "alpha_y"
  | .cγ => "gamma" | .cβγ => "beta_gamma"
  | .ct => "t" | .cv0 => "v_0" | .cw0 => "w_0" | .cy0 => "y_0"
  | .vs => "v_stmt" | .ws => "w_stmt" | .ys => "y_stmt"⟩

/-- The verifier-side quantities appearing in the checks and the target. -/
inductive VerifierVar : Type where
  | t : VerifierVar
  | v0 : VerifierVar
  | w0 : VerifierVar
  | y0 : VerifierVar
  | v_io : VerifierVar
  | w_io : VerifierVar
  | y_io : VerifierVar
deriving DecidableEq

instance : FinEnum VerifierVar :=
  .ofList [.t, .v0, .w0, .y0, .v_io, .w_io, .y_io] (fun x => by cases x <;> simp)

/-- The ideal variables of the abstract soundness problem. -/
def Var : Type := (PfElem × Slot) ⊕ VerifierVar

instance : DecidableEq Var := inferInstanceAs (DecidableEq ((PfElem × Slot) ⊕ VerifierVar))
instance : FinEnum Var := inferInstanceAs (FinEnum ((PfElem × Slot) ⊕ VerifierVar))

/-- The prover's sum variable for slot `sl` of proof element `p`. -/
def Var.pf (p : PfElem) (sl : Slot) : Var := Sum.inl (p, sl)

/-- The vanishing polynomial `t`, as an abstract indeterminate. -/
def Var.t : Var := Sum.inr .t
/-- The fixed circuit polynomial `v_0`. -/
def Var.v0 : Var := Sum.inr .v0
/-- The fixed circuit polynomial `w_0`. -/
def Var.w0 : Var := Sum.inr .w0
/-- The fixed circuit polynomial `y_0`. -/
def Var.y0 : Var := Sum.inr .y0
/-- The statement sum `∑ i, stmt i · v_stmt i`. -/
def Var.v_io : Var := Sum.inr .v_io
/-- The statement sum `∑ i, stmt i · w_stmt i`. -/
def Var.w_io : Var := Sum.inr .w_io
/-- The statement sum `∑ i, stmt i · y_stmt i`. -/
def Var.y_io : Var := Sum.inr .y_io

instance : Repr Var := ⟨fun v _ => match v with
  | Sum.inl (Sum.inl p, sl) => repr p ++ "_" ++ repr sl
  | Sum.inl (Sum.inr p, sl) => repr p ++ "_" ++ repr sl
  | Sum.inr .t => "t"
  | Sum.inr .v0 => "v_0"
  | Sum.inr .w0 => "w_0"
  | Sum.inr .y0 => "y_0"
  | Sum.inr .v_io => "v_io"
  | Sum.inr .w_io => "w_io"
  | Sum.inr .y_io => "y_io"⟩

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
  tox F .r_v * idl F (Var.pf p .v)
    + tox F .r_w * idl F (Var.pf p .w)
    + tox F .r_v * tox F .r_w * idl F (Var.pf p .y)
    + tox F .r_v * tox F .α_v * idl F (Var.pf p .αv)
    + tox F .r_w * tox F .α_w * idl F (Var.pf p .αw)
    + tox F .r_v * tox F .r_w * tox F .α_y * idl F (Var.pf p .αy)
    + idl F (Var.pf p .s)
    + tox F .β * (tox F .r_v * idl F (Var.pf p .βv)
        + tox F .r_w * idl F (Var.pf p .βw)
        + tox F .r_v * tox F .r_w * idl F (Var.pf p .βy))
    + idl F (Var.pf p .one)
    + tox F .α_v * idl F (Var.pf p .cαv)
    + tox F .α_w * idl F (Var.pf p .cαw)
    + tox F .α_y * idl F (Var.pf p .cαy)
    + tox F .γ * idl F (Var.pf p .cγ)
    + tox F .β * tox F .γ * idl F (Var.pf p .cβγ)
    + tox F .r_v * tox F .r_w * idl F (Var.pf p .ct) * idl F Var.t
    + tox F .r_v * idl F (Var.pf p .cv0) * idl F Var.v0
    + tox F .r_w * idl F (Var.pf p .cw0) * idl F Var.w0
    + tox F .r_v * tox F .r_w * idl F (Var.pf p .cy0) * idl F Var.y0
    + tox F .r_v * idl F (Var.pf p .vs)
    + tox F .r_w * idl F (Var.pf p .ws)
    + tox F .r_v * tox F .r_w * idl F (Var.pf p .ys)

/-- Check I of the verifier: `(V_mid + r_v(v_0 + v_io))·(W_mid^G2 + r_w(w_0 + w_io))
− (r_v r_w t)·H − (Y_mid + r_v r_w(y_0 + y_io))`. -/
def checkI : CMvPolynomial SymVars F :=
  (pfPoly F (Sum.inl .V_mid) + tox F .r_v * (idl F Var.v0 + idl F Var.v_io))
      * (pfPoly F (Sum.inr .W_mid) + tox F .r_w * (idl F Var.w0 + idl F Var.w_io))
    - (tox F .r_v * tox F .r_w * idl F Var.t) * pfPoly F (Sum.inr .H)
    - (pfPoly F (Sum.inl .Y_mid) + tox F .r_v * tox F .r_w * (idl F Var.y0 + idl F Var.y_io))

/-- Check II of the verifier: `V_mid' − α_v·V_mid`. -/
def checkII : CMvPolynomial SymVars F :=
  pfPoly F (Sum.inl .V_mid') - tox F .α_v * pfPoly F (Sum.inl .V_mid)

/-- Check III of the verifier: `W_mid' − α_w·W_mid^G1`. -/
def checkIII : CMvPolynomial SymVars F :=
  pfPoly F (Sum.inl .W_mid') - tox F .α_w * pfPoly F (Sum.inl .W_mid)

/-- Check IV of the verifier: `Y_mid' − α_y·Y_mid`. -/
def checkIV : CMvPolynomial SymVars F :=
  pfPoly F (Sum.inl .Y_mid') - tox F .α_y * pfPoly F (Sum.inl .Y_mid)

/-- Check V of the verifier: `Z·γ − βγ·(V_mid + W_mid^G1 + Y_mid)`. -/
def checkV : CMvPolynomial SymVars F :=
  pfPoly F (Sum.inl .Z) * tox F .γ
    - tox F .β * tox F .γ
      * (pfPoly F (Sum.inl .V_mid) + pfPoly F (Sum.inl .W_mid) + pfPoly F (Sum.inl .Y_mid))

/-- The Type I identification of the two copies of `W_mid`: their AGM expansions agree. -/
def identW : CMvPolynomial SymVars F :=
  pfPoly F (Sum.inl .W_mid) - pfPoly F (Sum.inr .W_mid)

/-- The generators of the soundness ideal: the coefficients of the five check polynomials and
the `W_mid` identification with respect to the toxic-waste monomials, each a polynomial in the
ideal variables. These are the abstract counterparts of the 13 coefficient equations of the
manual soundness proof (and their unused siblings). -/
def generators : List (CMvPolynomial Var F) :=
  ([checkI F, checkII F, checkIII F, checkIV F, checkV F, identW F]).flatMap
    SymbolicAGMScheme.coeffGenerators

/-- The target polynomial of the soundness problem: the QAP relation
`(v_0 + v_io + V)·(w_0 + w_io + W) − (y_0 + y_io + Y) = h·t` with the witness read off `Z`'s
`EK_β_v_w_y` slots (matching the extractor of the manual proof) and the quotient `H_1 + H_s`
from the `suffices` step (including the `VK_1` constant term the discarded proof omitted). -/
def target : CMvPolynomial Var F :=
  (X Var.v0 + X Var.v_io + X (Var.pf (Sum.inl .Z) .βv))
      * (X Var.w0 + X Var.w_io + X (Var.pf (Sum.inl .Z) .βw))
    - (X Var.y0 + X Var.y_io + X (Var.pf (Sum.inl .Z) .βy))
    - (X (Var.pf (Sum.inr .H) .one) + X (Var.pf (Sum.inr .H) .s)) * X Var.t

/-- **The abstract soundness problem of Pinocchio**: a polynomial ideal-membership problem over
the sum variables, fully circuit-independent. -/
def soundnessProblem : AGMProofSystemInstantiation.IdealMembershipProblem Var F where
  generators := generators F
  target := target F

end Symbolic

end Pinocchio
