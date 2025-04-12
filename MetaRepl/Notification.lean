import MetaRepl.Server
import Lean

open Lean

namespace MetaRepl

structure Notification (m : Type → Type) where
  description : Option String := none
  paramSchema : Json := json% { type : ["object", "array", "string", "number", "boolean", "null"] }
  run (param : Json) : m Unit

def Notification.liftM [MonadLiftT m n] (cmd : Notification m) : Notification n := 
  { cmd with run param := cmd.run param }

structure Notifications (m : Type → Type) where
  data : Std.HashMap String <| Notification m

def Notifications.liftM [MonadLiftT m n] (notifs : Notifications m) : 
    Notifications n where
  data := notifs.data.map fun _ x => x.liftM

def Notifications.get (cmds : Notifications m) (trigger : String) : 
    Option <| Notification m := 
  cmds.data.get? trigger

def Notifications.empty : Notifications m where data := {}

def Notification.insert (cmds : Notifications m) (trigger : String) 
    (cmd : Notification m) : 
    Notifications m where
  data := cmds.data.insert trigger cmd

def Notifications.run [Monad m] [MonadExcept ε m] [MonadBacktrack σ m] 
    (cmds : Notifications m) (trigger : String) (param : Json) :
    m Unit := do
  let some cmd := cmds.get trigger | return
  let state ← saveState
  try cmd.run param
  catch _ => restoreState state

initialize notificationsExt : 
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

open Lean Elab Term 

syntax (name := notificationAttrStx) "notification" ident : attr

initialize registerBuiltinAttribute {
  name := `notificationAttrStx
  descr := "Register a notification"
  add nm stx _ := match stx with 
    | `(attr|notification $id:ident) => Meta.MetaM.run' do 
      let cinfo ← getConstInfo nm
      let (_, _, body) ← Meta.forallMetaTelescope cinfo.type
      let_expr Notification _ := body | throwError "{nm} is not a valid notification"
      modifyEnv fun e => notificationsExt.addEntry e (id.getId.toString, nm)
    | _ => throwUnsupportedSyntax
}

def elabNotificationForMonadViaLift (cmd m : Expr) : TermElabM Expr := do
  Meta.mkAppOptM ``Notification.liftM #[none, m, none, cmd]

def elabNotificationForMonadViaEval (cmd m : Expr) : TermElabM Expr := do
  let (args, binders, body) ← Meta.forallMetaTelescope <| ← Meta.inferType cmd
  let_expr Notification n := body 
    | throwError "{← Meta.ppExpr cmd} is not a function that outputs a notification."
  unless ← Meta.isDefEq m n do 
    throwError "{← Meta.ppExpr n} is not defeq to {← Meta.ppExpr m}"
  for (arg,binder) in args.zip binders do
    if binder.isInstImplicit then 
      arg.mvarId!.assign <| ← Meta.synthInstance <| ← Meta.inferType arg
  instantiateMVars <| mkAppN cmd args

def elabNotificationForMonad (cmd m : Expr) : TermElabM Expr := do
  try elabNotificationForMonadViaLift cmd m
  catch _ => try elabNotificationForMonadViaEval cmd m
  catch _ => throwError "Failed to elaborate {← Meta.ppExpr cmd} for monad {← Meta.ppExpr m}"

def elabNotification (trigger : String) (m : Expr) : TermElabM Expr := do
  let some declName := notificationsExt.getState (← getEnv) |>.get? trigger
    | throwError "Failed to find notification with trigger {trigger}"
  let c ← Meta.mkConstWithFreshMVarLevels declName
  elabNotificationForMonad c m

end MetaRepl
