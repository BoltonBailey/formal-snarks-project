import FormalSnarksProject.SNARKs.Groth16TypeI.Symbolic
import FormalSnarksProject.SMT.Export

/-!
# Exporting the abstract Groth16 (Type I) soundness problem to SMT-LIB

This script turns the circuit-independent soundness ideal-membership problem
`Groth16TypeI.Symbolic.soundnessProblem` into an SMT-LIB 2.6 file in the finite-field theory
(`QF_FF`), via the shared machinery of `FormalSnarksProject/SMT/Export.lean` (see that file for
the encoding: the query hunts for a cheating assignment, so **`unsat` = sound**). Note that the
manual soundness proof needs *radical* ideal membership (its case analysis kills squares with
`mul_self_eq_zero`); the Nullstellensatz-style encoding decides exactly that.

Run with

    lake env lean FormalSnarksProject/SNARKs/Groth16TypeI/SMTExport.lean

from the repository root, which writes `benchmarks/groth16_typeI_soundness.smt2`. It is
intentionally **not** imported by the `FormalSnarksProject` root library (it is a runnable
script, not library content).
-/

namespace Groth16TypeI.SMTExport

/-- The abstract soundness problem, computed concretely over `ZMod 101`. -/
def prob : AGMProofSystemInstantiation.IdealMembershipProblem Symbolic.Var SMT.F :=
  Symbolic.soundnessProblem SMT.F

set_option maxRecDepth 8000 in
#eval SMT.writeProblem prob "benchmarks/groth16_typeI_soundness.smt2"
  ("Abstract Groth16 (Type I / symmetric pairing) SNARK soundness, from the\n" ++
   "FormalSnarksProject Lean development. Query: does a cheating assignment exist that\n" ++
   "satisfies every verifier coefficient equation while falsifying the extracted QAP\n" ++
   "relation? unsat = sound.")
  "the extracted QAP relation must be violated for a break"

end Groth16TypeI.SMTExport
