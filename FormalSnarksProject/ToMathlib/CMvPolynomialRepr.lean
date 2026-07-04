import CompPoly.Multivariate.CMvPolynomial
import Mathlib.Data.FinEnum

/-!
# A readable `Repr` for computable multivariate polynomials

CompPoly ships a `Repr (CMvMonomial σ)` that prints every variable by its **positional** index and
including zero exponents (`X0^0 * X1^0 * … * X27^1 * …`), and no `Repr` for `CMvPolynomial σ R` at
all. That is unreadable for schemes whose variable type `σ` is a rich sum/product (e.g. the
`SumVar` of `SymbolicAGMScheme`).

This file adds a `Repr (CMvPolynomial σ R)` that

* names each variable through a `Repr σ` instance rather than by position, and
* drops variables with exponent `0`, printing `1` for the constant monomial and `0` for the zero
  polynomial,

so a polynomial prints as `c₁ * v * w^2 + c₂ * u + …` in terms of the actual variable names. The
coefficient is suppressed when it is `1`. Provide a `Repr σ` for the variable type (derived, or a
short hand-written one — see `Groth16TypeIII/Symbolic.lean`) to get legible output.
-/

namespace CPoly.CMvPolynomial

open Std

/-- The nonzero-exponent factors of a monomial, each rendered as `v` or `v^e` using the `Repr σ`
instance for the variable name. Variables with exponent `0` are dropped, so the constant monomial
yields `[]`. -/
def monomialFactors {σ : Type*} [FinEnum σ] [Repr σ] (m : CMvMonomial σ) : List Format :=
  (FinEnum.toList σ).filterMap fun v =>
    match CMvMonomial.degreeOf m v with
    | 0 => none
    | 1 => some (repr v)
    | (e + 2) => some (repr v ++ "^" ++ repr (e + 2))

section

variable {σ : Type*} [FinEnum σ] [Repr σ] {R : Type*} [Zero R] [One R] [BEq R] [Repr R]

/-- Render a single term `c · m`: the bare coefficient for the constant monomial, the bare
monomial when `c = 1`, and `c * m` otherwise. -/
private def reprTerm (m : CMvMonomial σ) (c : R) : Format :=
  match monomialFactors m with
  | [] => repr c
  | factors =>
    let mono := Format.joinSep factors " * "
    if c == 1 then mono else repr c ++ " * " ++ mono

/-- Print a computable multivariate polynomial as a sum of terms, naming variables through
`Repr σ` and omitting zero exponents. See the module docstring. -/
instance instRepr : Repr (CMvPolynomial σ R) where
  reprPrec p _ :=
    match (Lawful.monomials p).map fun m => reprTerm m (coeff m p) with
    | [] => "0"
    | terms => Format.joinSep terms " + "

end

end CPoly.CMvPolynomial
