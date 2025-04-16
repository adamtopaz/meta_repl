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

inductive ReplSignal where
  | default
  | close

abbrev ReplT (m : Type → Type) 
    [STWorld w m] [MonadBacktrack σ m] := 
  StateRefT ReplSignal (HistoryT Input Output m)

instance [Monad m] [STWorld w m] [MonadBacktrack σ m] : 
    MonadBacktrack σ (ReplT m) where
  saveState := show m _ from saveState
  restoreState s := show m _ from restoreState s

instance [Monad m] [STWorld w m] [MonadBacktrack σ m] [MonadExcept ε m] : 
    MonadExcept ε (ReplT m) where 
  throw e _ _ := throw e
  tryCatch e f s₁ s₂ := tryCatch (e s₁ s₂) (fun err => f err s₁ s₂)

structure Repl 
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m] 
    [MonadBacktrack σ m] [MonadExcept ε m]
    --[STWorld w m] [MonadBacktrack σ m] [MonadExcept ε m] 
    (cmds : Commands (ReplT m)) where
  /-- This runs before the main REPL loop. -/
  init : ReplT m Unit
  /-- This runs after the main REPL loop. -/
  term : ReplT m Unit
  /-- This checks whether to terminate the loop. -/
  finished : ReplT m Bool
  /-- Obtain the next state index and input for the REPL. -/
  getInput : ReplT m (Option Nat × Input)
  /-- Return an unknown command error. 
    Parameters are the state index and input. -/
  unknownCmd : Option Nat → Input → ReplT m ε
  /-- Return an invalid index error. 
    Parameters are the state index and input. -/
  invalidIdx : Option Nat → Input → ReplT m ε
  /-- The REPL tags errors with a kind and possibly an index and input.
    This function is meant to use such a tagged error to create an 
    error message to send. -/
  mkError : ReplError ε → ReplT m Error
  /-- Send an output. 
    Parameters are the state index at the output and the output itself. -/
  sendOutput : Nat → Output → ReplT m Unit

partial
def Repl.run 
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m] 
    [MonadBacktrack σ m] [MonadExcept ε m]
    {cmds : Commands (ReplT m)} (repl : Repl cmds) : m (History Input Output σ) := do
  let s ← saveState
  Prod.snd <$> (go.run' .default |>.run { head := 0, states := #[s], history := #[] })
where 
step : ExceptT (ReplError ε) (ReplT m) (Option σ × Option Input × Result) := 
    commitIfNoEx do
  let (idx, input) ← .adapt (.mk .failedInput none none) <| .mk <| observing <| repl.getInput
  let state : σ ← .adapt (.mk .invalidIdx idx input) <| .mk <| observing <| do 
    let states := (← getThe (History Input Output σ)).states
    let idx! := idx.getD <| ← show HistoryT Input Output m Nat from getHead
    match states[idx!]? with 
    | some state => return state
    | none => throw <| ← repl.invalidIdx idx input
  let cmd : Command (ReplT m) ← .adapt (.mk .unknownCmd idx input) <| .mk <| observing <| do 
    match cmds.get input.method with
    | some cmd => return cmd
    | none => throw <| ← repl.unknownCmd idx input
  restoreState state
  let out : Result ← .adapt (.mk .failedCmd idx input) <| .mk <| observing <| do
    let preCmdState ← saveState
    let out ← cmd.run input.param
    if cmd.passive then restoreState preCmdState
    return out
  let newState : Option σ ← match cmd.passive with
    | true => pure none
    | false => saveState
  return (newState, input, out)
loop : ReplT m Unit := do 
  if ← repl.finished then return
  if (← getThe ReplSignal) matches .close then return
  match ← step with
  | .ok (st,inpt,res) => 
    show HistoryT Input Output m Unit from 
      recordHistory inpt (.result res) st
    repl.sendOutput (← getThe <| History Input Output σ).head <| .result res
  | .error err =>
    let error : Error ← repl.mkError err
    show HistoryT Input Output m Unit from 
      recordHistory err.input? (.error error) none
    repl.sendOutput (← getThe <| History Input Output σ).head <| .error error
  loop
go : ReplT m Unit := do
  repl.init ; loop ; repl.term

structure UserRepl 
    [STWorld w m] [MonadBacktrack σ m] [MonadExcept ε m]
    (cmds : Commands (ReplT m)) where
  /-- This runs before the main REPL loop. -/
  init : ReplT m Unit
  /-- This runs after the main REPL loop. -/
  term : ReplT m Unit
  /-- This checks whether to terminate the loop. -/
  finished : ReplT m Bool
  /-- Obtain the next state index and input for the REPL. -/
  unknownCmd : Option Nat → Input → ReplT m ε
  /-- Return an invalid index error. 
    Parameters are the state index and input. -/
  invalidIdx : Option Nat → Input → ReplT m ε
  /-- The REPL tags errors with a kind and possibly an index and input.
    This function is meant to use such a tagged error to create an 
    error message to send. -/
  invalidInputIdx : String → ReplT m ε
  invalidInputParam : String → ReplT m ε
  mkError : ReplError ε → ReplT m Error

def UserRepl.repl 
    [Monad m] 
    [STWorld IO.RealWorld m] [MonadLiftT (ST IO.RealWorld) m] 
    [MonadLiftT IO m]
    [MonadBacktrack σ m] [MonadExcept ε m]
    {cmds : Commands (ReplT m)} (repl : UserRepl cmds) : 
    Repl cmds where
  init := repl.init
  term := repl.term
  finished := repl.finished
  unknownCmd := repl.unknownCmd
  invalidIdx := repl.invalidIdx
  mkError := repl.mkError
  getInput := do
    let stdin ← show IO _ from IO.getStdin
    IO.print "idx> "
    let line ← stdin.getLine
    let idx := line.trim.toNat? 
    IO.print "method> "
    let line ← stdin.getLine
    let method := line.trim
    IO.print "param> "
    let line ← stdin.getLine
    let param : Json := 
      match Lean.Json.parse line.trim with
      | .ok j => j
      | _ => .null
    return ⟨idx, method, param⟩
  sendOutput idx output := do
    println! s!"idx: {idx}"
    println! s!"out: {toJson output}"

end MetaRepl
