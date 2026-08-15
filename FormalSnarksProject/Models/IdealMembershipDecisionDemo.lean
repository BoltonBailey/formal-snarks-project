module

meta import FormalSnarksProject.Models.IdealMembershipDecision
meta import FormalSnarksProject.SNARKs.ToySnark.Symbolic
meta import FormalSnarksProject.SNARKs.BabySnark.Symbolic
meta import FormalSnarksProject.SNARKs.Groth16TypeIII.Symbolic
meta import FormalSnarksProject.SNARKs.Lipmaa.Symbolic
meta import FormalSnarksProject.SNARKs.Groth16TypeI.Symbolic
meta import FormalSnarksProject.SNARKs.GGPR.Symbolic
meta import FormalSnarksProject.SNARKs.Pinocchio.Symbolic
meta import FormalSnarksProject.SMT.Export

/-!
# Running the soundness decision on the SNARK ideal-membership problems

This script runs the computable soundness decision of
`FormalSnarksProject/Models/IdealMembershipDecision.lean` on the abstract soundness
ideal-membership problems of the SNARKs in this repository (their `Symbolic.lean` files),
computed over `ZMod 101` (`SMT.F`, as in the SMT export). Each `#eval` prints `true` when the
Buchberger-based search finds — and the verified checker confirms — a radical-membership
certificate for the target in the generator ideal, i.e. when the SNARK's verification
equations force the extracted relation.

Run with `lake env lean` on this file (it is intentionally **not** imported by the
`FormalSnarksProject` root library). Only the searches that finish within a few minutes in
the interpreter are left live; the slower ones are commented out, with their observed
outcomes noted (times are on an M-series laptop).

Results (2026-07-11): ToySnark, BabySnark, Groth16TypeIII and Lipmaa all decide `true` with a
degree-1 certificate (plain ideal membership — interestingly, the case analysis of the manual
proofs is not needed at the certificate level).
-/

meta section

open AGMProofSystemInstantiation SymbolicAGMScheme

/-! ### ToySnark (3 generators, 5 variables) — `true` in seconds -/

def toySnarkProblem : IdealMembershipProblem ToySnark.Symbolic.Var SMT.F :=
  ToySnark.Symbolic.soundnessProblem SMT.F

#eval toySnarkProblem.decideMembership 100 3

/-! ### BabySNARK (27 generators, 26 variables) — `true` in seconds -/

def babySnarkProblem : IdealMembershipProblem BabySNARK.Symbolic.Var SMT.F :=
  BabySNARK.Symbolic.soundnessProblem SMT.F

#eval babySnarkProblem.decideMembership 400 3

/-! ### Groth16, Type III (29 generators, 29 variables)

Decides `true` (degree-1 certificate, fuel 1000), but takes ~7 min in the interpreter, so the
`#eval` is commented out. Note that with the tree map's plain lexicographic order (instead of
grevlex + the normal selection strategy) this search *fails* at the same fuel. -/

set_option maxRecDepth 8000 in
def groth16TypeIIIProblem :
    IdealMembershipProblem (SumVar (Groth16TypeIII.Symbolic.scheme SMT.F)) SMT.F :=
  Groth16TypeIII.Symbolic.soundnessProblem SMT.F

-- #eval groth16TypeIIIProblem.decideMembership 1000 3  -- `true`, ~7 min

/-! ### Lipmaa (29 generators, 29 variables)

Decides `true` (degree-1 certificate, fuel 1000) in ~7 min; commented out like Groth16III. -/

set_option maxRecDepth 8000 in
def lipmaaProblem :
    IdealMembershipProblem (SumVar (Lipmaa.Symbolic.scheme SMT.F)) SMT.F :=
  Lipmaa.Symbolic.soundnessProblem SMT.F

-- #eval lipmaaProblem.decideMembership 1000 3  -- `true`, ~7 min

/-! ### Groth16, Type I (51 generators, 39 variables)

Times out (the combined run of this and the two searches below was aborted after ~35 min in
the interpreter without producing an answer). Deciding this one may also genuinely need a
radical power `k ≥ 2` (the manual proof case-splits on `A_α·B_α = 0`). -/

def groth16TypeIProblem : IdealMembershipProblem Groth16TypeI.Symbolic.Var SMT.F :=
  Groth16TypeI.Symbolic.soundnessProblem SMT.F

-- #eval groth16TypeIProblem.decideMembership 2000 3  -- times out (> 35 min)

/-! ### GGPR (79 generators, 123 variables)

Times out (see the Groth16 Type I section). -/

def ggprProblem : IdealMembershipProblem GGPR.Symbolic.Var SMT.F :=
  GGPR.Symbolic.soundnessProblem SMT.F

-- #eval ggprProblem.decideMembership 2000 3  -- times out (> 35 min)

/-! ### Pinocchio (230 generators, 214 variables)

Times out (see the Groth16 Type I section). -/

def pinocchioProblem : IdealMembershipProblem Pinocchio.Symbolic.Var SMT.F :=
  Pinocchio.Symbolic.soundnessProblem SMT.F

-- #eval pinocchioProblem.decideMembership 4000 3  -- times out (> 35 min)
