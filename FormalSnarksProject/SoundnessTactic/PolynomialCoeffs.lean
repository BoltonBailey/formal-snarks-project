
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.ComputeDegree

section Tactic

open Lean Elab Tactic Meta Expr

-- Tactic draft
/-- Determines all nonzero coefficients of a polynomial equation and converts them into -/

syntax (name := polynomialEquation) "polynomial_equation" term : tactic

elab_rules : tactic | `(tactic| polynomial_equation $h) => focus <| withMainContext do
  let goal ← getMainGoal
  -- let ctx ← getLCtx

  let fvarId <- getFVarId h
  let decl ← fvarId.getDecl
  let type ← inferType decl.type
  -- Ensure type is an equality of polynomials
  let val := type.appFn!.appArg!
  goal.assert
  -- clear r



  -- type <- get type of hypothesis
  -- -- If hypothesis is not equation of mv_polynomials, fail
  -- if type not equality of mv_polynomials
  --   then fail "Hypothesis is not an equality of polynomials"
  -- -- RHS may not be zero, so simplify
  -- rw [eq_iff_sub_zero] at hypothesis_name

  -- -- Polynomial is zero iff all coeffs are zero
  -- rw [Polynomial.ext_iff] at hypothesis_name

  -- -- Invoke the total_degree tactic to find the degrees of lhs
  -- let degrees := foo

  -- -- get a list of all nonzero monomials
  -- monomials := foob degrees

  -- -- extract a new hypothesis for each nonzero value
  -- for monomial in monomials
  --   monomial_name <- barbaz
  --   have hypothesis_name_cat_monomial_name := hypothesis_name monomials

  MVarId.clear hypothesis_name
