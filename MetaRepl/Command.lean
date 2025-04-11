import MetaRepl.Server
import Lean

open Lean

namespace MetaRepl

structure Command (m : Type → Type) where
  description : Option String := none
  paramsSchema : Json := json% { type : "object" }
  outputSchema : Json := json% { type : "object" }
  run (params : Json) : m Json

structure Commands (m : Type → Type) where
  data : Std.HashMap String <| Command m

def Commands.get (cmds : Commands m) (trigger : String) : Option <| Command m := 
  cmds.data.get? trigger

def Commands.empty : Commands m where data := {}

def Commands.insert (cmds : Commands m) (trigger : String) (cmd : Command m) : 
    Commands m where
  data := cmds.data.insert trigger cmd

def Commands.run [Monad m] [MonadExcept ε m] [MonadBacktrack σ m] 
    (cmds : Commands m) (trigger : String) (params : Json) 
    (unknownCmd : ErrorObj) (failedCmd : ε → ErrorObj) :
    m Output := do
  let some cmd := cmds.get trigger | return .error unknownCmd
  let state ← saveState
  try 
    let out ← cmd.run params
    return .response out
  catch e => 
    restoreState state
    return .error <| failedCmd e

initialize commandsExt : 
    PersistentEnvExtension 
      (String × Name) (String × Name) (Std.HashMap String Name) ← 
    registerPersistentEnvExtension {
  mkInitial := return {}
  addImportedFn as := do 
    let mut out := {}
    for bs in as do for (a,b) in bs do out := out.insert a b
    return out
  addEntryFn := fun m (a,b) => m.insert a b
  exportEntriesFn m := m.toArray
}

end MetaRepl
