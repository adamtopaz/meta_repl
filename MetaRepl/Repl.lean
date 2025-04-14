import MetaRepl.Command
import MetaRepl.History

open Lean

namespace MetaRepl

inductive ReplErrorKind where
  | failedInput
  | unknownCmd
  | failedCmd
  | invalidIdx
  | other

structure ReplInput where
  idx : Nat
  input : Input

structure ReplOutput where
  idx : Nat
  output : Output

structure Repl [MonadExcept ε m] (cmds : Commands m) where
  init : m Unit
  term : m Unit
  finished : m Bool
  getInput : m ReplInput
  unknownCmd : m ε
  invalidIdx : m ε
  mkError : ReplErrorKind → ε → m Error
  sendOutput : ReplOutput → m Unit

partial
def Repl.run 
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m] 
    [MonadExcept ε m] [MonadBacktrack σ m]
    {cmds : Commands m} (repl : Repl cmds) : m (History Input Output σ) := do
  let s ← saveState
  Prod.snd <$> go.run { head := 0, states := #[s], history := #[] }
where 
step : HistoryT Input Output m Unit := do
  let mut errKind : ReplErrorKind := .other
  let mut input? : Option Input := none
  let initialState ← saveState
  try 
    let ⟨idx,input⟩ ← try repl.getInput 
      catch e => errKind := .failedInput ; throw e
    input? := input
    let some s := (← get).states[idx]?
      | errKind := .invalidIdx ; throw <| ← repl.invalidIdx
    modify fun h => { h with head := idx }
    restoreState s
    let some cmd := cmds.get input.method
      | errKind := .unknownCmd ; throw <| ← repl.unknownCmd
    let out ← try cmd.run input.param
      catch e => errKind := .failedCmd ; throw e
    let s ← saveState
    let output : Output := .result out
    modify fun h => {
      head := h.states.size
      states := h.states.push s
      history := h.history.push { 
        startIdx := h.head, 
        endIdx := h.states.size, 
        action := input, 
        result := output 
      }
    }
    repl.sendOutput ⟨(← get).head, output⟩
  catch e => 
    restoreState initialState
    let err ← repl.mkError errKind e
    let output : Output := .error err
    modify fun h => {
      head := h.head
      states := h.states
      history := h.history.push { 
        startIdx := h.head, 
        endIdx := h.head, 
        action := input?, 
        result := .error err
      }
    }
    repl.sendOutput ⟨(← get).head, output⟩
loop : HistoryT Input Output m Unit := do 
  if ← repl.finished then return
  step 
  loop
go : HistoryT Input Output m Unit := do
  repl.init ; loop ; repl.term

end MetaRepl
