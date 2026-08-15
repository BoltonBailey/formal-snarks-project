module

meta import FormalSnarksProject.SNARKs.Lipmaa.Symbolic
meta import FormalSnarksProject.SMT.Export

/-!
# Exporting the abstract Lipmaa soundness problem to SMT-LIB

This script turns the circuit-independent soundness ideal-membership problem
`Lipmaa.Symbolic.soundnessProblem` into an SMT-LIB 2.6 file in the finite-field theory
(`QF_FF`), via the shared machinery of `FormalSnarksProject/SMT/Export.lean` (see that file for
the encoding: the query hunts for a cheating assignment, so **`unsat` = sound**).

Run with

    lake env lean FormalSnarksProject/SNARKs/Lipmaa/SMTExport.lean

from the repository root, which writes `benchmarks/lipmaa_soundness.smt2`. It is intentionally
**not** imported by the `FormalSnarksProject` root library (it is a runnable script, not
library content).
-/

meta section

open Lipmaa.Symbolic
open SymbolicAGMScheme

namespace Lipmaa.SMTExport

/-- The abstract soundness problem, computed concretely over `ZMod 101`. -/
def prob : AGMProofSystemInstantiation.IdealMembershipProblem (SumVar (scheme SMT.F)) SMT.F :=
  soundnessProblem SMT.F

set_option maxRecDepth 8000 in
#eval SMT.writeProblem prob "benchmarks/lipmaa_soundness.smt2"
  ("Abstract Lipmaa SNARK soundness, from the FormalSnarksProject Lean development.\n" ++
   "Query: does a cheating assignment exist that satisfies every verifier coefficient\n" ++
   "equation while falsifying the extracted QAP relation? unsat = sound.")
  "the extracted QAP relation must be violated for a break"

end Lipmaa.SMTExport
