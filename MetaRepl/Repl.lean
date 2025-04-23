import MetaRepl.Command
import MetaRepl.History

open Lean

namespace MetaRepl

inductive ReplErrorTag where
  | failedInput
  | invalidIdx
  | cmdsError
deriving ToJson, FromJson

inductive ReplError (ε : Type) where
  | cmdError : CommandsError ε → ReplError ε
  | failedInput : ReplError ε
  | invalidIdx : Nat → ReplError ε

inductive ReplSignal where
  | default
  | close

abbrev ReplT (m : Type → Type) 
    [STWorld w m] [MonadBacktrack σ m] := 
  StateRefT ReplSignal (HistoryT Input m)

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
    {cmds : Commands (ReplT m)} (repl : Repl cmds) : m (History Input σ) := do
  let s ← saveState
  Prod.snd <$> (go.run' .default |>.run { head := 0, states := #[s], parent := {} })
where 
step : ExceptT (ReplError ε) (ReplT m) (Input × Result) := 
    commitIfNoEx do
  let (idx, input) ← .adapt (fun _ => .failedInput) <| .mk <| observing <| repl.getInput
--  let state : σ ← .adapt (fun _ => .invalidIdx) <| .mk <| observing <| do 
  let states := (← getThe (History Input σ)).states
  let idx! := idx.getD <| ← show HistoryT Input m Nat from getHead
  let state : σ ← show ExceptT (ReplError ε) (ReplT m) σ from match states[idx!]? with 
    | some state => return state
    | none => throw <| .invalidIdx idx!
  restoreState state
  match ← cmds.run input |>.run with
  | .ok res => return (input, res)
  | .error e => throw <| .cmdError e
loop : ReplT m Unit := do 
  if ← repl.finished then return
  if (← getThe ReplSignal) matches .close then return
  match ← step with
  | .ok (inpt,res) => 
    show HistoryT Input m Unit from 
      recordHistory inpt (← saveState)
    repl.sendOutput (← getThe <| History Input σ).head <| .result res
  | .error err =>
    let error : Error ← repl.mkError err
    repl.sendOutput (← getThe <| History Input σ).head <| .error error
  loop
go : ReplT m Unit := do
  repl.init ; loop ; repl.term

structure ReplStruct 
    [STWorld w m] [MonadBacktrack σ m] [MonadExcept ε m]
    (cmds : Commands (ReplT m)) where
  /-- This runs before the main REPL loop. -/
  init : ReplT m Unit
  /-- This runs after the main REPL loop. -/
  term : ReplT m Unit
  /-- This checks whether to terminate the loop. -/
  finished : ReplT m Bool
  strToErr : String → ReplT m ε
  errToStr : ε → ReplT m String

def ReplStruct.userRepl 
    [Monad m] 
    [STWorld IO.RealWorld m] [MonadLiftT (ST IO.RealWorld) m] 
    [MonadLiftT IO m]
    [MonadBacktrack σ m] [MonadExcept ε m]
    {cmds : Commands (ReplT m)} (repl : ReplStruct cmds) : 
    Repl cmds where
  init := repl.init
  term := repl.term
  finished := repl.finished
  mkError err := match err with 
    | .failedInput => return .mk "Failed input" .null
    | .invalidIdx idx => return .mk "Invalid index" idx
    | .cmdError (.unknownCmd s) => return .mk "Unknown command" s
    | .cmdError (.failedCmd e) => return .mk "Failed command" (← repl.errToStr e)
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

def ReplStruct.jsonRepl 
    [Monad m] 
    [STWorld IO.RealWorld m] [MonadLiftT (ST IO.RealWorld) m] 
    [MonadLiftT IO m] [MonadBacktrack σ m] [MonadExcept ε m]
    {cmds : Commands (ReplT m)} (repl : ReplStruct cmds) : 
    Repl cmds where
  init := repl.init
  term := repl.term
  finished := repl.finished
  getInput := do
    let stdout ← show IO _ from IO.getStdout
    stdout.putStr ">>> "
    stdout.flush
    let stdin ← show IO _ from IO.getStdin
    let line ← stdin.getLine
    let json ← show ReplT m Json from match Lean.Json.parse line.trim with
      | .ok j => return j
      | .error e => do 
        throw <| ← repl.strToErr s!"Failed to parse\n{line.trim}\nas JSON:\n{e}"
    let idx : Option Nat := 
      match json.getObjValAs? Nat "idx" with
      | .ok n => n
      | .error _ => none
    let input ← show ReplT m Input from match json.getObjValAs? Input "input" with
      | .ok input => return input
      | .error e => do 
        throw <| ← repl.strToErr s!"Failed to get input:\n{e}"
    return (idx, input)
  sendOutput idx output := do
    let j : Json := json% {
      idx : $(idx),
      output : $(output)
    }
    let stdout ← show IO _ from IO.getStdout
    stdout.putStrLn s!"<<< {j.compress}"
    stdout.flush
  mkError err := match err with 
    | .failedInput => return .mk "Failed input" .null
    | .invalidIdx idx => return .mk "Invalid index" idx
    | .cmdError (.unknownCmd s) => return .mk "Unknown command" s
    | .cmdError (.failedCmd e) => return .mk "Failed command" (← repl.errToStr e)

end MetaRepl
