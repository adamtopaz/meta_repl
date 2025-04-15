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
  input? : Option Input
  error : ε

structure Repl [STWorld w m] [MonadBacktrack σ m] [MonadExcept ε m] 
    (cmds : Commands m) where
  init : HistoryT Input Output m Unit
  term : HistoryT Input Output m Unit
  finished : HistoryT Input Output m Bool
  getInput : HistoryT Input Output m (Nat × Input)
  unknownCmd : Nat → Input → HistoryT Input Output m ε
  invalidIdx : Nat → Input → HistoryT Input Output m ε
  mkError : ReplErrorKind → ε → HistoryT Input Output m Error
  sendOutput : Output → HistoryT Input Output m Unit

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
  let (idx, input) ← .adapt (.mk .failedInput none) <| .mk <| observing <| repl.getInput
  let state : σ ← .adapt (.mk .invalidIdx input) <| .mk <| observing <| do 
    let states := (← get).states
    match states[idx]? with 
    | some state => return state
    | none => throw <| ← repl.invalidIdx idx input
  let cmd : Command m ← .adapt (.mk .unknownCmd input) <| .mk <| observing <| do 
    match cmds.get input.method with
    | some cmd => return cmd
    | none => throw <| ← repl.unknownCmd idx input
  restoreState state
  let out : Result ← .adapt (.mk .failedCmd input) <| .mk <| observing <| 
    cmd.run input.param
  return (input, out)
loop : HistoryT Input Output m Unit := do 
  if ← repl.finished then return
  match ← step with
  | .ok (inpt,res) => 
    recordHistory inpt (.result res) (← saveState)
    repl.sendOutput <| .result res
  | .error err => 
    let error : Error ← repl.mkError err.kind err.error
    recordHistory err.input? (.error error) none
    repl.sendOutput <| .error error
  loop
go : HistoryT Input Output m Unit := do
  repl.init ; loop ; repl.term

end MetaRepl
