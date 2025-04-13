import MetaRepl.Server
import MetaRepl.History
import Lean

open Lean

namespace MetaRepl

structure Command (m : Type → Type) where
  description : Option String := none
  paramSchema : Json := json% { type : ["object", "array", "string", "number", "boolean", "null"] }
  outputSchema : Json := json% { type : ["object", "array", "string", "number", "boolean", "null"] }
  run (param : Json) : m Json

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

def Commands.run [Monad m] [MonadExcept ε m] [MonadBacktrack σ m] 
    (cmds : Commands m) (trigger : String) (param : Json) 
    (unknownCmd : ErrorObj) (failedCmd : ε → ErrorObj) :
    m Output := do
  let some cmd := cmds.get trigger | return .error unknownCmd
  let state ← saveState
  try 
    let out ← cmd.run param
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
  catch _ => throwError "Failed to elaborate {← Meta.ppExpr cmd} for monad {← Meta.ppExpr m}"

def elabCommand (trigger : String) (m : Expr) : TermElabM Expr := do
  let some declName := commandsExt.getState (← getEnv) |>.get? trigger
    | throwError "Failed to find command with trigger {trigger}"
  let c ← Meta.mkConstWithFreshMVarLevels declName
  elabCommandForMonad c m

end MetaRepl
