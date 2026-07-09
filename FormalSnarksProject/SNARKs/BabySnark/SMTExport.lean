import FormalSnarksProject.SNARKs.BabySnark.Symbolic
import FormalSnarksProject.SMT.Export

/-!
# Exporting the abstract BabySNARK soundness problem to SMT-LIB

This script turns the circuit-independent soundness ideal-membership problem
`BabySNARK.Symbolic.soundnessProblem` into an SMT-LIB 2.6 file in the finite-field theory
(`QF_FF`), via the shared machinery of `FormalSnarksProject/SMT/Export.lean` (see that file for
the encoding: the query hunts for a cheating assignment, so **`unsat` = sound**).

Run with

    lake env lean FormalSnarksProject/SNARKs/BabySnark/SMTExport.lean

from the repository root, which writes `benchmarks/babysnark_soundness.smt2`. It is
intentionally **not** imported by the `FormalSnarksProject` root library (it is a runnable
script, not library content).
-/

namespace BabySNARK.SMTExport

/-- The abstract soundness problem, computed concretely over `ZMod 101`. -/
def prob : AGMProofSystemInstantiation.IdealMembershipProblem Symbolic.Var SMT.F :=
  Symbolic.soundnessProblem SMT.F

set_option maxRecDepth 4000 in
#eval SMT.writeProblem prob "benchmarks/babysnark_soundness.smt2"
  ("Abstract BabySNARK soundness, from the FormalSnarksProject Lean development.\n" ++
   "Query: does a cheating assignment exist that satisfies every verifier coefficient\n" ++
   "equation (checks I, II and the Type I identifications) while falsifying the extracted\n" ++
   "square span relation? unsat = sound.")
  "the extracted square span relation must be violated for a break"

end BabySNARK.SMTExport
