/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import CompPoly.OrdMultivariate.COrdMvPolynomial

/-!
# A readable `Repr` for computable multivariate polynomials

CompPoly ships no `Repr` for `COrdMvPolynomial σ R`. This file adds one that

* names each variable through a `Repr σ` instance,
* drops variables with exponent `0`, printing `1` for the constant monomial and `0` for the zero
  polynomial,

so a polynomial prints as `c₁ * v * w^2 + c₂ * u + …` in terms of the actual variable names. The
coefficient is suppressed when it is `1`. Provide a `Repr σ` for the variable type (derived, or a
short hand-written one — see `Groth16TypeIII/Symbolic.lean`) to get legible output.

Since the ordered sparse representation stores each monomial as a sorted entry list, the factors
are read directly off `COrdMvMonomial.entryList` — no enumeration of the variable type is needed.
-/

public section

namespace CPoly.COrdMvPolynomial

open Std

/-- The nonzero-exponent factors of a monomial, each rendered as `v` or `v^e` using the `Repr σ`
instance for the variable name. Variables with exponent `0` are dropped, so the constant monomial
yields `[]`. -/
def monomialFactors {σ : Type*} [Ord σ] [Repr σ] (m : COrdMvMonomial σ) : List Format :=
  m.entryList.filterMap fun ve =>
    match ve.2 with
    | 0 => none
    | 1 => some (repr ve.1)
    | (e + 2) => some (repr ve.1 ++ "^" ++ repr (e + 2))

section

variable {σ : Type*} [Ord σ] [Std.TransOrd σ] [Repr σ] {R : Type*} [Zero R] [One R] [BEq R]
  [Repr R]

/-- Render a single term `c · m`: the bare coefficient for the constant monomial, the bare
monomial when `c = 1`, and `c * m` otherwise. -/
private def reprTerm (m : COrdMvMonomial σ) (c : R) : Format :=
  match monomialFactors m with
  | [] => repr c
  | factors =>
    let mono := Format.joinSep factors " * "
    if c == 1 then mono else repr c ++ " * " ++ mono

/-- Print a computable multivariate polynomial as a sum of terms, naming variables through
`Repr σ` and omitting zero exponents. See the module docstring. -/
@[no_expose]
instance instRepr : Repr (COrdMvPolynomial σ R) where
  reprPrec p _ :=
    match (OrdLawful.monomials p).map fun m => reprTerm m (coeff m p) with
    | [] => "0"
    | terms => Format.joinSep terms " + "

end

end CPoly.COrdMvPolynomial
