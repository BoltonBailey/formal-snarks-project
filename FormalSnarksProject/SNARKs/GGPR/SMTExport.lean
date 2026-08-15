module

meta import FormalSnarksProject.SNARKs.GGPR.Symbolic
meta import FormalSnarksProject.SMT.Export

/-!
# Exporting the abstract GGPR soundness problem to SMT-LIB

This script turns the circuit-independent soundness ideal-membership problem
`GGPR.Symbolic.soundnessProblem` into an SMT-LIB 2.6 file in the finite-field theory (`QF_FF`),
via the shared machinery of `FormalSnarksProject/SMT/Export.lean` (see that file for the
encoding: the query hunts for a cheating assignment, so **`unsat` = sound**).

Run with

    lake env lean FormalSnarksProject/SNARKs/GGPR/SMTExport.lean

from the repository root, which writes `benchmarks/ggpr_soundness.smt2`. It is intentionally
**not** imported by the `FormalSnarksProject` root library (it is a runnable script, not
library content).
-/

meta section

namespace GGPR.SMTExport

/-- The abstract soundness problem, computed concretely over `ZMod 101`. -/
def prob : AGMProofSystemInstantiation.IdealMembershipProblem Symbolic.Var SMT.F :=
  Symbolic.soundnessProblem SMT.F

set_option maxRecDepth 8000 in
#eval SMT.writeProblem prob "benchmarks/ggpr_soundness.smt2"
  ("Abstract GGPR SNARK soundness, from the FormalSnarksProject Lean development.\n" ++
   "Query: does a cheating assignment exist that satisfies every verifier coefficient\n" ++
   "equation (checks I-V) while falsifying the extracted QSP relation? unsat = sound.")
  "the extracted QSP relation must be violated for a break"

end GGPR.SMTExport
