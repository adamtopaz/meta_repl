import MetaRepl.Server
import MetaRepl.Command
import MetaRepl.Notification
import MetaRepl.History

open Lean

namespace MetaRepl

structure ReplStruct (m : Type → Type) [MonadExcept ε m] where
  notifs : Notifications m
  cmds : Commands m
  finished : m Bool
  unknownCmd : String → Json → ErrorObj
  failedCmd : String → Json → ε → ErrorObj

def ReplStruct.liftM [MonadLiftT m n] [MonadExcept ε m] [MonadExcept ε n]
    (struct : ReplStruct m) : ReplStruct n where
  notifs := struct.notifs.liftM
  cmds := struct.cmds.liftM
  finished := struct.finished
  unknownCmd := struct.unknownCmd
  failedCmd := struct.failedCmd

def ReplStruct.stdServer 
    [Monad m] [MonadLiftT IO m] [MonadExcept ε m] 
    [MonadBacktrack σ m] (repl : ReplStruct m) :
    StdServer m where
  init := do 
    let cmdsArr : Array Json := repl.cmds.data.toArray.map fun (trigger, cmd) => 
      json% {
        method : $(trigger),
        paramSchema : $(cmd.paramSchema),
        outputSchema : $(cmd.outputSchema)
      }
    let notifsArr : Array Json := repl.notifs.data.toArray.map fun (trigger, cmd) => 
      json% {
        method : $(trigger),
        paramSchema : $(cmd.paramSchema)
      }
    let configObj : Json := json% {
      commands : $(cmdsArr),
      notifications : $(notifsArr)
    }
    let stdout ← show IO _ from IO.getStdout
    stdout.putStrLn s!"CONFIG {Json.compress <| configObj}"
    stdout.flush
  term := do 
    let stdout ← show IO _ from IO.getStdout
    stdout.putStrLn s!"TERM"
    stdout.flush
  finished := repl.finished
  notify method param := repl.notifs.run method param 
  getOutput method param := 
    repl.cmds.run method param 
      (repl.unknownCmd method param) 
      (repl.failedCmd method param)

def ReplStruct.run 
    [Monad m] [MonadLiftT IO m] [MonadExcept ε m] 
    [MonadBacktrack σ m] (repl : ReplStruct m) :
    m Unit := do
  repl.stdServer.run

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

