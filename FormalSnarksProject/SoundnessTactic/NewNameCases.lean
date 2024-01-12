import Lean
import Std.Tactic.OpenPrivate
import Std.Data.List.Basic
import Mathlib.Lean.Expr.Basic

/-!

Defines a variant of cases' that assigns names automatically.

-/

namespace Mathlib.Tactic
open Lean Meta Elab Elab.Tactic

open private getAltNumFields in evalCases ElimApp.evalAlts.go in
def ElimApp.evalNames_add (elimInfo : ElimInfo) (alts : Array ElimApp.Alt) (withArg : Syntax)
    (numEqs := 0) (numGeneralized := 0) (toClear : Array FVarId := #[]) :
    TermElabM (Array MVarId) := do
  let mut names : List Syntax := withArg[1].getArgs |>.toList
  let mut subgoals := #[]
  for { name := altName, mvarId := g, .. } in alts do
    let numFields ← getAltNumFields elimInfo altName
    let (altVarNames, names') := names.splitAtD numFields (Unhygienic.run `(_))
    names := names'
    let (fvars, g) ← g.introN numFields <| altVarNames.map ((fun n => (Name.str n "foo")) ∘ (getNameOfIdent' ·[0]))
    let some (g, subst) ← Cases.unifyEqs? numEqs g {} | pure ()
    let (_, g) ← g.introNP numGeneralized
    let g ← liftM $ toClear.foldlM (·.tryClear) g
    for fvar in fvars, stx in altVarNames do
      g.withContext <| (subst.apply <| .fvar fvar).addLocalVarInfoForBinderIdent ⟨stx⟩
    subgoals := subgoals.push g
  pure subgoals

open private getElimNameInfo generalizeTargets generalizeVars from Lean.Elab.Tactic.Induction

elab (name := new_name_cases) "new_name_cases " tgts:(Parser.Tactic.casesTarget,+) usingArg:((" using " ident)?)
  withArg:((" with" (ppSpace colGt binderIdent)+)?) : tactic => do
  let targets ← elabCasesTargets tgts.1.getSepArgs
  let g :: gs ← getUnsolvedGoals | throwNoGoalsToBeSolved
  g.withContext do
    let elimInfo ← getElimNameInfo usingArg targets (induction := false)
    let targets ← addImplicitTargets elimInfo targets
    let result ← withRef tgts <| ElimApp.mkElimApp elimInfo targets (← g.getTag)
    let elimArgs := result.elimApp.getAppArgs
    let targets ← elimInfo.targetsPos.mapM (instantiateMVars elimArgs[·]!)
    let motive := elimArgs[elimInfo.motivePos]!
    let g ← generalizeTargetsEq g (← inferType motive) targets
    let (targetsNew, g) ← g.introN targets.size
    g.withContext do
      ElimApp.setMotiveArg g motive.mvarId! targetsNew
      g.assign result.elimApp
      let subgoals ← ElimApp.evalNames_add elimInfo result.alts withArg
         (numEqs := targets.size) (toClear := targetsNew)
      setGoals <| subgoals.toList ++ gs
