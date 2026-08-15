module

meta import FormalSnarksProject.SNARKs.Groth16TypeIII.Symbolic

/-!
# Demo: the abstract Groth16 (Type III) soundness problem, evaluated

This file `#eval`s the circuit-independent soundness ideal-membership problem produced by
`Groth16TypeIII.Symbolic.soundnessProblem` (defined in `Symbolic.lean`). Everything on the
solver-facing path is computable, so the generators and target print concretely — over a small
prime field `ZMod 101` chosen only so the coefficients are printable.

Run it with

    lake env lean FormalSnarksProject/SNARKs/Groth16TypeIII/SymbolicDemo.lean

or open it in the editor and read the `#eval` output in the InfoView. It is intentionally **not**
imported by the `FormalSnarksProject` root library (it is a runnable demo, not library content),
so a normal `lake build` does not execute these `#eval`s.

Output is via the readable `Repr` instances (`ToMathlib/COrdMvPolynomialRepr.lean` for the polynomial,
plus the smart-constructor `Repr (SumVar 𝓢)` and the short leaf-name instances in `Symbolic.lean`):
sum variables print as `comp_G1 C q u_wit`, `single_G2 B δ`, `stmtSum v_stmt`, and a coefficient of
`100` is `-1` in `ZMod 101`.

Notes:
* `set_option maxRecDepth` is needed at each `#eval` because the `@[reducible] scheme` unfolds deep.
* Printing all `generators` at once is slow; take a slice.
-/

meta section

open Groth16TypeIII.Symbolic CPoly

namespace Groth16TypeIII.SymbolicDemo

-- `ZMod 101` is a field (needed for the `COrdMvPolynomial` coefficient operations).
instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩

-- The abstract problem for Groth16 (Type III) over `ZMod 101`.
abbrev prob := soundnessProblem (ZMod 101)

-- How many generators the soundness ideal has (the toxic-waste-monomial coefficients of the
-- verifier check).
#eval prob.generators.length

-- The target: the extracted QAP relation `(∑aᵢuᵢ)(∑aᵢvᵢ) − ∑aᵢwᵢ − h·t`, over the sum variables
-- (`100 = −1`). Soundness reduces to this lying in the radical of the ideal below.
set_option maxRecDepth 8000 in
#eval prob.target

-- The first five generators of the soundness ideal, printed via the readable `Repr`.
set_option maxRecDepth 8000 in
#eval prob.generators.take 5

end Groth16TypeIII.SymbolicDemo
