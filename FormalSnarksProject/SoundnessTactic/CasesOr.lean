/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean

/-!
# `cases_or`

An in-progress modification of `cases_type` that allows splitting Ors while keeping the name

-/

namespace Lean.MVarId

/--
Core tactic for `casesm` and `cases_type`. Calls `cases` on all fvars in `g` for which
`matcher ldecl.type` returns true.
* `recursive`: if true, it calls itself repeatedly on the resulting subgoals
* `allowSplit`: if false, it will skip any hypotheses where `cases` returns more than one subgoal.
* `throwOnNoMatch`: if true, then throws an error if no match is found
-/
partial def casesMatchingOr (matcher : Expr → MetaM Bool) (recursive := false) (allowSplit := true)
    (throwOnNoMatch := true) (g : MVarId) : MetaM (List MVarId) := do
  let result := (← go g).toList
  if throwOnNoMatch && result == [g] then
    throwError "no match"
  else
    return result
  where
  /-- Auxiliary for `casesMatchingOr`. Accumulates generated subgoals in `acc`. -/
  go (g : MVarId) (acc : Array MVarId := #[]) : MetaM (Array MVarId) :=
    g.withContext do
      for ldecl in ← getLCtx do
        let name := ldecl.userName --
        if ldecl.isImplementationDetail then continue
        if ← matcher ldecl.type then
          let mut acc := acc
          let subgoals ← if allowSplit then
            g.cases ldecl.fvarId (givenNames := #[{varNames := [name]}, {varNames := [name]}])
          else
            let s ← saveState
            let subgoals ← g.cases ldecl.fvarId
            if subgoals.size > 1 then
              s.restore
              continue
            else
              pure subgoals
          for subgoal in subgoals do
            if recursive then
              acc ← go subgoal.mvarId acc
            else
              acc := acc.push subgoal.mvarId
          return acc
      return (acc.push g)

-- def casesType (heads : Array Name) (recursive := false) (allowSplit := true) :
--     MVarId → MetaM (List MVarId) :=
--   let matcher ty := pure <|
--     if let .const n .. := ty.headBeta.getAppFn then heads.contains n else false
--   casesMatchingOr matcher recursive allowSplit

end Lean.MVarId

namespace Mathlib.Tactic
open Lean Meta Elab Tactic MVarId

/-- Elaborate a list of terms with holes into a list of patterns. -/
def elabPatterns_Or (pats : Array Term) : TermElabM (Array AbstractMVarsResult) :=
  withTheReader Term.Context (fun ctx ↦ { ctx with ignoreTCFailures := true }) <|
  Term.withoutErrToSorry <|
  pats.mapM fun p ↦ Term.withoutModifyingElabMetaStateWithInfo do
    withRef p <| abstractMVars (← Term.elabTerm p none)

/-- Returns true if any of the patterns match the expression. -/
-- TODO nake this only match or
def matchPatterns_Or (pats : Array AbstractMVarsResult) (e : Expr) : MetaM Bool := do
  let e ← instantiateMVars e
  pats.anyM fun p ↦ return (← Conv.matchPattern? p e) matches some (_, #[])

/--
* `casesm p` applies the `cases` tactic to a hypothesis `h : type`
  if `type` matches the pattern `p`.
* `casesm p_1, ..., p_n` applies the `cases` tactic to a hypothesis `h : type`
  if `type` matches one of the given patterns.
* `casesm* p` is a more efficient and compact version of `· repeat casesm p`.
  It is more efficient because the pattern is compiled once.

Example: The following tactic destructs all conjunctions and disjunctions in the current context.
```
casesm* _ ∨ _, _ ∧ _
```
-/
elab (name := casesOr) "cases_or" recursive:"*"? ppSpace pats:term,+ : tactic => do
  let pats ← elabPatterns_Or pats.getElems
  liftMetaTactic (casesMatchingOr (matchPatterns_Or pats) recursive.isSome)

-- /-- Common implementation of `cases_type` and `cases_type!`. -/
-- def elabCasesType (heads : Array Ident)
--     (recursive := false) (allowSplit := true) : TacticM Unit := do
--   let heads ← heads.mapM resolveGlobalConstNoOverloadWithInfo
--   liftMetaTactic (casesType heads recursive allowSplit)


section test

example (p q r : Prop) (h1 : p ∨ q) (h2 : q ∨ r) : q ∨ p := by
  cases_or* _ ∨ _
  sorry
  sorry
  sorry
  have h3 : q := by
    exact h1
  sorry
