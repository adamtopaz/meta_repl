import MetaRepl.Server
import MetaRepl.Command
import MetaRepl.Notification

open Lean

namespace MetaRepl

structure ReplStruct (m : Type → Type) [MonadExcept ε m] where
  notifs : Notifications m
  cmds : Commands m
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
        paramSchema : $(cmd.paramsSchema),
        outputSchema : $(cmd.outputSchema)
      }
    let notifsArr : Array Json := repl.notifs.data.toArray.map fun (trigger, cmd) => 
      json% {
        method : $(trigger),
        paramsSchema : $(cmd.paramsSchema)
      }
    let configObj : Json := json% {
      commands : $(cmdsArr),
      notifications : $(notifsArr)
    }
    let stdout ← show IO _ from IO.getStdout
    stdout.putStrLn <| Json.compress <| configObj
    stdout.flush
  term := return 
  notify method params := repl.notifs.run method params 
  getOutput method params := 
    repl.cmds.run method params 
      (repl.unknownCmd method params) 
      (repl.failedCmd method params)

def ReplStruct.run 
    [Monad m] [MonadLiftT IO m] [MonadExcept ε m] 
    [MonadBacktrack σ m] (repl : ReplStruct m) :
    m Unit := do
  -- notifications
  -- cmds
  repl.stdServer.run
