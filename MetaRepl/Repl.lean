import MetaRepl.Command
import MetaRepl.Notification
import MetaRepl.History

open Lean

namespace MetaRepl

structure ReplStruct (m : Type → Type) [MonadExcept ε m] where
  notifs : Notifications m
  cmds : Commands m
  finished : m Bool
  unknownCmd : String → Option Json.Structured → JsonRpc.Message
  unknownNotif : String → Option Json.Structured → JsonRpc.Message 
  failedCmd : String → Option Json.Structured → ε → JsonRpc.Message

def ReplStruct.liftM [MonadLiftT m n] [MonadExcept ε m] [MonadExcept ε n]
    (struct : ReplStruct m) : ReplStruct n where
  notifs := struct.notifs.liftM
  cmds := struct.cmds.liftM
  finished := struct.finished
  unknownCmd := struct.unknownCmd
  unknownNotif := struct.unknownNotif
  failedCmd := struct.failedCmd

end MetaRepl
