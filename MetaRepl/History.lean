import MetaRepl.Command
import MetaRepl.Notification
import MetaRepl.Repl

open Lean

namespace MetaRepl

structure History (σ : Type) where
  states : Array σ 

abbrev HistoryT (m : Type → Type) 
    [MonadBacktrack σ m] [STWorld w m] :=
  StateRefT (History σ) m

instance [MonadBacktrack σ m] [STWorld w m] : 
    MonadBacktrack σ (HistoryT m) where
  saveState := show m _ from saveState
  restoreState s := show m _ from restoreState s

instance [MonadExcept ε m] [MonadBacktrack σ m] [STWorld w m] :
    MonadExcept ε (HistoryT m) where
  throw e := show m _ from throw e
  tryCatch e f s := tryCatch (e s) (fun err => f err s)

def Command.withHistory 
    [Monad m] [MonadExcept ε m] 
    [MonadBacktrack σ m] [MonadState (History σ) m]
    (cmd : Command m) (err : String → m ε) : Command m where
  description := cmd.description
  paramSchema := json% {
    state : "int",
    param : $(cmd.paramSchema)
  }
  outputSchema := json% {
    state  : "int",
    output : $(cmd.outputSchema)
  }
  run j := do 
    let .ok stateIdx := j.getObjValAs? Nat "state" 
      | throw <| ← err s!"Failed to find state:\n{j}"
    let hist ← get
    let some s := hist.states[stateIdx]?
      | throw <| ← err s!"State {stateIdx} is not a valid state index"
    let .ok param := j.getObjValAs? Json "param"
      | throw <| ← err s!"Failed to find param:\n{j}"
    restoreState s
    let out ← cmd.run param
    let new ← saveState
    modify fun h => { states := h.states.push new }
    return json% {
      state : $(hist.states.size),
      output : $(out)
    }

def Command.addHistory 
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m]
    [MonadExcept ε m] [MonadBacktrack σ m] 
    (cmd : Command m) (err : String → m ε) : Command (HistoryT m) :=
  cmd.liftM |>.withHistory fun s => err s

def Notification.withHistory
    [Monad m] [MonadExcept ε m] 
    [MonadBacktrack σ m] [MonadState (History σ) m]
    (cmd : Notification m) (err : String → m ε) : Notification m where
  description := cmd.description
  paramSchema := json% {
    state : "int",
    param : $(cmd.paramSchema)
  }
  run j := do 
    let .ok stateIdx := j.getObjValAs? Nat "state" 
      | throw <| ← err s!"Failed to find state:\n{j}"
    let hist ← get
    let some s := hist.states[stateIdx]?
      | throw <| ← err s!"State {stateIdx} is not a valid state index"
    let .ok param := j.getObjValAs? Json "param"
      | throw <| ← err s!"Failed to find param:\n{j}"
    restoreState s
    cmd.run param
    let new ← saveState
    modify fun h => { states := h.states.push new }

def Notification.addHistory
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m]
    [MonadExcept ε m] [MonadBacktrack σ m] 
    (cmd : Notification m) (err : String → m ε) : Notification (HistoryT m) :=
  cmd.liftM |>.withHistory fun s => err s

def ReplStruct.withHistory 
    [Monad m] [MonadExcept ε m] 
    [MonadBacktrack σ m] [MonadState (History σ) m]
    (err : String → m ε) (struct : ReplStruct m) : 
    ReplStruct m where
  cmds := { data := struct.cmds.data.map fun _ c => c.withHistory err }
  notifs := { data := struct.notifs.data.map fun _ c => c.withHistory err }
  finished := struct.finished
  unknownCmd := struct.unknownCmd
  failedCmd := struct.failedCmd

def ReplStruct.addHistory 
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m]
    [MonadExcept ε m] [MonadBacktrack σ m] 
    (err : String → m ε) (struct : ReplStruct m) : 
    ReplStruct (HistoryT m) :=
  struct.liftM |>.withHistory fun s => err s

def ReplStruct.runWithHistory 
    [Monad m] [STWorld IO.RealWorld m] [MonadLiftT (ST IO.RealWorld) m]
    [MonadLiftT IO m] [MonadExcept ε m] [MonadBacktrack σ m] 
    (err : String → m ε) (struct : ReplStruct m) : m (History σ) := 
  ((struct.addHistory err).run |>.run <| .mk #[]) <&> Prod.snd

def ReplStruct.runWithHistory' 
    [Monad m] [STWorld IO.RealWorld m] [MonadLiftT (ST IO.RealWorld) m]
    [MonadLiftT IO m] [MonadExcept ε m] [MonadBacktrack σ m] 
    (err : String → m ε) (struct : ReplStruct m) : m Unit := 
  (struct.addHistory err).run |>.run' <| .mk #[]

end MetaRepl
