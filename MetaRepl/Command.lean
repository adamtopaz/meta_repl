import MetaRepl.Types
import Lean

open Lean JsonRpc

namespace MetaRepl

structure Command (m : Type → Type) where
  description : Option String := none
  paramSchema : Json := json% { type : ["object", "array"] }
  outputSchema : Json := json% { type : ["object", "array"] }
  run (param : Json) : m Result

def Command.liftM [MonadLiftT m n] (cmd : Command m) : Command n := 
  { cmd with run param := cmd.run param }

structure Commands (m : Type → Type) where
  data : Std.HashMap String <| Command m

def Commands.liftM [MonadLiftT m n] (cmds : Commands m) : Commands n where
  data := cmds.data.map fun _ c => c.liftM

def Commands.get (cmds : Commands m) (trigger : String) : Option <| Command m := 
  cmds.data.get? trigger

def Commands.empty : Commands m where data := {}

def Commands.insert (cmds : Commands m) (trigger : String) (cmd : Command m) : 
    Commands m where
  data := cmds.data.insert trigger cmd

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

open Lean Elab Term 

syntax (name := commandAttrStx) "command" ident : attr

initialize registerBuiltinAttribute {
  name := `commandAttrStx
  descr := "Register a command"
  add nm stx _ := match stx with 
    | `(attr|command $id:ident) => Meta.MetaM.run' do 
      let cinfo ← getConstInfo nm
      let (_, _, body) ← Meta.forallMetaTelescope cinfo.type
      let_expr Command _ := body | throwError "{nm} is not a valid command"
      modifyEnv fun e => commandsExt.addEntry e (id.getId.toString, nm)
    | _ => throwUnsupportedSyntax
}

def elabCommandForMonadViaLift (cmd m : Expr) : TermElabM Expr := do
  Meta.mkAppOptM ``Command.liftM #[none, m, none, cmd]

def elabCommandForMonadViaEval (cmd m : Expr) : TermElabM Expr := do
  let (args, binders, body) ← Meta.forallMetaTelescope <| ← Meta.inferType cmd
  let_expr Command n := body
    | throwError "{← Meta.ppExpr cmd} is not a function that outputs a command."
  unless ← Meta.isDefEq m n do 
    throwError "{← Meta.ppExpr n} is not defeq to {← Meta.ppExpr m}"
  for (arg,binder) in args.zip binders do
    if binder.isInstImplicit then 
      arg.mvarId!.assign <| ← Meta.synthInstance <| ← Meta.inferType arg
  instantiateMVars <| mkAppN cmd args

def elabCommandForMonad (cmd m : Expr) : TermElabM Expr := do
  try elabCommandForMonadViaLift cmd m
  catch _ => try elabCommandForMonadViaEval cmd m
  catch e => throw e

def elabCommand (trigger : String) (m : Expr) : TermElabM Expr := do
  let some declName := commandsExt.getState (← getEnv) |>.get? trigger
    | throwError "Failed to find command with trigger {trigger}"
  let c ← Meta.mkConstWithFreshMVarLevels declName
  elabCommandForMonad c m

syntax (name := commandsStx) "commands(" ident,* ")" : term 

@[term_elab commandsStx]
def elabCommands : TermElab := fun stx tp? => 
  match stx with 
  | `(term|commands($ids,*)) => do 
    let some tp := tp? | throwError "Failed to infer type"
    let_expr Commands m := ← Meta.whnf tp | throwError "{← Meta.ppExpr tp} is not of the right form"
    let ids := ids.getElems.map fun id => id.getId.toString
    let cmds ← ids.mapM fun s => elabCommand s m
    let mut out : Expr ← Meta.mkAppOptM ``Commands.empty #[m]
    for (id, cmd) in ids.zip cmds do 
      out ← Meta.mkAppOptM ``Commands.insert #[m,out,toExpr id,cmd]
    return out
  | _ => throwUnsupportedSyntax

end MetaRepl
