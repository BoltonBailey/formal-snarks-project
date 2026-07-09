# SMT benchmarks

SMT-LIB 2.6 benchmarks in the finite-field theory (`QF_FF`, over the BN254 scalar field),
generated from the abstract SNARK soundness ideal-membership problems of this repository
(the `Symbolic.lean` file of each SNARK). See `FormalSnarksProject/SMT/Export.lean` for the
encoding: each query hunts for a *cheating assignment* — an assignment satisfying every
verifier coefficient equation while falsifying the extracted relation — so **`unsat` means the
SNARK is sound** (the target lies in the radical of the generator ideal, by the
Nullstellensatz).

Each file is written by the corresponding runnable script, from the repository root:

    lake env lean FormalSnarksProject/SNARKs/<Snark>/SMTExport.lean

| file | SNARK | script |
| ---- | ----- | ------ |
| `babysnark_soundness.smt2` | BabySNARK | `SNARKs/BabySnark/SMTExport.lean` |
| `ggpr_soundness.smt2` | GGPR | `SNARKs/GGPR/SMTExport.lean` |
| `groth16_typeI_soundness.smt2` | Groth16, Type I (symmetric) | `SNARKs/Groth16TypeI/SMTExport.lean` |
| `groth16_typeIII_soundness.smt2` | Groth16, Type III | `SNARKs/Groth16TypeIII/SMTExport.lean` |
| `lipmaa_soundness.smt2` | Lipmaa | `SNARKs/Lipmaa/SMTExport.lean` |
| `pinocchio_soundness.smt2` | Pinocchio | `SNARKs/Pinocchio/SMTExport.lean` |
| `toysnark_soundness.smt2` | ToySnark | `SNARKs/ToySnark/SMTExport.lean` |

`QF_FF` needs a solver with finite-field support (cvc5 built with CoCoALib). Lacking one, a
quick sanity check is to mechanically rewrite `ff.add/ff.mul/ff.neg/(as ffN F)` into a `QF_NRA`
twin over the reals and run z3 — all coefficients here are 0/±1, so the instances are
meaningful over any field.
