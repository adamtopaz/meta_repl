import MetaRepl.Command
import MetaRepl.History

open Lean

namespace MetaRepl

inductive ReplErrorKind where
  | failedInput
  | unknownCmd
  | failedCmd
  | invalidIdx

structure ReplError (ε : Type) where
  kind : ReplErrorKind
  idx? : Option Nat
  input? : Option Input
  error : ε

structure Repl [STWorld w m] [MonadBacktrack σ m] [MonadExcept ε m] 
    (cmds : Commands m) where
  /-- This runs before the main REPL loop. -/
  init : HistoryT Input Output m Unit
  /-- This runs after the main REPL loop. -/
  term : HistoryT Input Output m Unit
  /-- This checks whether to terminate the loop. -/
  finished : HistoryT Input Output m Bool
  /-- Obtain the next state index and input for the REPL. -/
  getInput : HistoryT Input Output m (Nat × Input)
  /-- Return an unknown command error. 
    Parameters are the state index and input. -/
  unknownCmd : Nat → Input → HistoryT Input Output m ε
  /-- Return an invalid index error. 
    Parameters are the state index and input. -/
  invalidIdx : Nat → Input → HistoryT Input Output m ε
  /-- The REPL tags errors with a kind and possibly an index and input.
    This function is meant to use such a tagged error to create an 
    error message to send. -/
  mkError : ReplError ε → HistoryT Input Output m Error
  /-- Send an output. 
    Parameters are the state index at the output and the output itself. -/
  sendOutput : Nat → Output → HistoryT Input Output m Unit

partial
def Repl.run 
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m] 
    [MonadExcept ε m] [MonadBacktrack σ m]
    {cmds : Commands m} (repl : Repl cmds) : m (History Input Output σ) := do
  let s ← saveState
  Prod.snd <$> go.run { head := 0, states := #[s], history := #[] }
where 
step : ExceptT (ReplError ε) (HistoryT Input Output m) (Option Input × Result) := 
    commitIfNoEx do
  let (idx, input) ← .adapt (.mk .failedInput none none) <| .mk <| observing <| repl.getInput
  let state : σ ← .adapt (.mk .invalidIdx idx input) <| .mk <| observing <| do 
    let states := (← get).states
    match states[idx]? with 
    | some state => return state
    | none => throw <| ← repl.invalidIdx idx input
  let cmd : Command m ← .adapt (.mk .unknownCmd idx input) <| .mk <| observing <| do 
    match cmds.get input.method with
    | some cmd => return cmd
    | none => throw <| ← repl.unknownCmd idx input
  restoreState state
  let out : Result ← .adapt (.mk .failedCmd idx input) <| .mk <| observing <| 
    cmd.run input.param
  return (input, out)
loop : HistoryT Input Output m Unit := do 
  if ← repl.finished then return
  match ← step with
  | .ok (inpt,res) => 
    recordHistory inpt (.result res) (← saveState)
    repl.sendOutput (← get).head <| .result res
  | .error err =>
    let error : Error ← repl.mkError err
    recordHistory err.input? (.error error) none
    repl.sendOutput (← get).head <| .error error
  loop
go : HistoryT Input Output m Unit := do
  repl.init ; loop ; repl.term

end MetaRepl
