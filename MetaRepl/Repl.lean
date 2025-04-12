import MetaRepl.Server
import MetaRepl.Command
import MetaRepl.Notification

open Lean

namespace MetaRepl

structure ReplStruct (m : Type → Type) [MonadExcept ε m] where
  notifs : Notifications m
  cmds : Commands m
  finished : m Bool
  unknownCmd : String → Json → ErrorObj
  failedCmd : String → Json → ε → ErrorObj

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
    stdout.putStrLn <| Json.compress <| configObj
    stdout.flush
  term := return 
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

  repl.stdServer.run
