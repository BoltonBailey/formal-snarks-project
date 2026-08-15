/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Lean.Meta.Tactic.Simp

/-!
# Soundness tactic attributes

Declares the `integral_domain_simp` simp-set attribute used by the soundness tactic.
-/

public section

open Lean Meta

/-- `@[integral_domain_simp]` is an attribute for lemmas that are used in the conversion of MvPolynomial
expressions to a normal form consisting of adds of sums of muls of MvPolynomials -/
initialize integralDOmainSimpExt : SimpExtension ←
  registerSimpAttr `integral_domain_simp
    "lemmas that are used in the conversion of MvPolynomial expressions to a normal form consisting of adds of sums of muls of MvPolynomials"


/-- `@[polynomial_nf]` is an attribute for lemmas that are used in the conversion of MvPolynomial
expressions to a normal form consisting of adds of sums of muls of MvPolynomials -/
initialize polynomialNfExt : SimpExtension ←
  registerSimpAttr `polynomial_nf
    "lemmas that are used in the conversion of MvPolynomial expressions to a normal form consisting of adds of sums of muls of MvPolynomials"
