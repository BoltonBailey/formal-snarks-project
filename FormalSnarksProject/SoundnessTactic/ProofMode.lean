import Lean
open Lean

-- Mario's proof mode tactic for speed recompilation

structure ProofState where
  tacCtx : Elab.Tactic.Context
  tacState : Elab.Tactic.State
  termCtx : Elab.Term.Context
  termState : Elab.Term.State
  metaCtx : Meta.Context
  metaState : Meta.State

def ProofState.get : Elab.Tactic.TacticM ProofState :=
  fun tacCtx tacState termCtx termState metaCtx metaState => do
    let tacState ← tacState.get
    let termState ← termState.get
    let metaState ← metaState.get
    return { tacCtx, tacState, termCtx, termState, metaCtx, metaState }

def ProofState.with : ProofState → Elab.Tactic.TacticM α → CoreM α :=
  fun { tacCtx, tacState, termCtx, termState, metaCtx, metaState } x => do
    let tacState ← IO.mkRef tacState
    let termState ← IO.mkRef termState
    let metaState ← IO.mkRef metaState
    x tacCtx tacState termCtx termState metaCtx metaState

initialize proofStateExt : EnvExtension (List ProofState) ← registerEnvExtension (pure [])

elab "start_proof" : tactic => do
  let state ← ProofState.get
  modifyEnv (proofStateExt.modifyState · (state :: ·))
  Elab.Tactic.evalTactic (← `(tactic| repeat sorry))

elab tk:"##" tac:(tacticSeq)? : command => do
  let state :: rest := proofStateExt.getState (← getEnv)
    | throwError "proof mode not started, use `start_proof`"
  Elab.Command.liftTermElabM do
    state.with do
      Elab.Tactic.withTacticInfoContext tk do
        if let some tac := tac then
          Elab.Tactic.evalTactic tac
      if (← Elab.Tactic.getUnsolvedGoals).isEmpty then
        logInfoAt tk "Goals accomplished 🎉"
        modifyEnv (proofStateExt.setState · rest)
      else
        modifyEnv (proofStateExt.setState · ((← ProofState.get) :: rest))
