module

meta import FormalSnarksProject.SNARKs.Pinocchio.Symbolic
meta import FormalSnarksProject.SMT.Export

/-!
# Exporting the abstract Pinocchio soundness problem to SMT-LIB

This script turns the circuit-independent soundness ideal-membership problem
`Pinocchio.Symbolic.soundnessProblem` into an SMT-LIB 2.6 file in the finite-field theory
(`QF_FF`), via the shared machinery of `FormalSnarksProject/SMT/Export.lean` (see that file for
the encoding: the query hunts for a cheating assignment, so **`unsat` = sound**).

Run with

    lake env lean FormalSnarksProject/SNARKs/Pinocchio/SMTExport.lean

from the repository root, which writes `benchmarks/pinocchio_soundness.smt2`. It is
intentionally **not** imported by the `FormalSnarksProject` root library (it is a runnable
script, not library content).
-/

meta section

namespace Pinocchio.SMTExport

/-- The abstract soundness problem, computed concretely over `ZMod 101`. -/
def prob : AGMProofSystemInstantiation.IdealMembershipProblem Symbolic.Var SMT.F :=
  Symbolic.soundnessProblem SMT.F

set_option maxRecDepth 8000 in
#eval SMT.writeProblem prob "benchmarks/pinocchio_soundness.smt2"
  ("Abstract Pinocchio SNARK soundness, from the FormalSnarksProject Lean development.\n" ++
   "Query: does a cheating assignment exist that satisfies every verifier coefficient\n" ++
   "equation (checks I-V and the W_mid Type I identification) while falsifying the\n" ++
   "extracted QAP relation? unsat = sound.")
  "the extracted QAP relation must be violated for a break"

end Pinocchio.SMTExport
