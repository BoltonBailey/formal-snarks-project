import FormalSnarksProject.SNARKs.ToySnark.Symbolic
import FormalSnarksProject.SMT.Export

/-!
# Exporting the abstract ToySnark soundness problem to SMT-LIB

This script turns the soundness ideal-membership problem `ToySnark.Symbolic.soundnessProblem`
into an SMT-LIB 2.6 file in the finite-field theory (`QF_FF`), via the shared machinery of
`FormalSnarksProject/SMT/Export.lean` (see that file for the encoding: the query hunts for a
cheating assignment, so **`unsat` = sound**).

Run with

    lake env lean FormalSnarksProject/SNARKs/ToySnark/SMTExport.lean

from the repository root, which writes `benchmarks/toysnark_soundness.smt2`. It is intentionally
**not** imported by the `FormalSnarksProject` root library (it is a runnable script, not library
content).
-/

namespace ToySnark.SMTExport

/-- The abstract soundness problem, computed concretely over `ZMod 101`. -/
def prob : AGMProofSystemInstantiation.IdealMembershipProblem Symbolic.Var SMT.F :=
  Symbolic.soundnessProblem SMT.F

#eval SMT.writeProblem prob "benchmarks/toysnark_soundness.smt2"
  ("Abstract ToySnark soundness, from the FormalSnarksProject Lean development.\n" ++
   "Query: does a cheating assignment exist that satisfies every verifier coefficient\n" ++
   "equation while falsifying the extracted relation? unsat = sound.")
  "the extracted relation (A*y = z or B*x = z, as a product) must be violated for a break"

end ToySnark.SMTExport
