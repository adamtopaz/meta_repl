import MetaRepl
import MetaRepl.ExprWithCtx

open Lean Elab Tactic
open MetaRepl

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  show EIO _ Unit from Lean.withImportModules (trustLevel := 0) #[.mk `Lean false] {} fun env => 
      discard <| Core.CoreM.toIO (α := Unit) 
      (ctx := {fileName := "", options := {}, fileMap := default}) (s := {env}) do
    let cmds : Commands (ReplT ExprCtxM) := commands(
      close, 
      ExprWithCtx.pp, 
      ExprWithCtx.inferType,
      ExprWithCtx.intro
    )
    let repl : ReplStruct cmds := {
      init := return 
      term := return
      finished := return false
      unknownCmd _ input := return .error (← getRef) s!"Invalid command {input.method}"
      invalidIdx idx _ := return .error (← getRef) s!"Invalid index {idx}"
      strToErr s := return .error (← getRef) s
      errToStr s := s.toMessageData.toString
    }
    let initialState ← Meta.MetaM.run' do 
      let nm := args[0]!.toName
      return ⟨← mkConstWithLevelParams nm, ← getLCtx⟩
    discard <| repl.jsonRepl.run |>.run initialState
  /-
  let some path := args[0]?
    | throw <| .userError "Usage: lake exe meta_repl FILEPATH"
  let path : System.FilePath := .mk path
  let inputCtx ← Lean.Parser.readInputContext path
  let cmds : MetaRepl.Commands (MetaRepl.ReplT TacticM) := 
    commands(close, tactic, goals)
  /-
  let repl : MetaRepl.UserRepl (m := TacticM) cmds := {
    init := return
    term := return
    finished := return (← getUnsolvedGoals).isEmpty
    unknownCmd _ input := return .error (← getRef) m!"Unknown command {input.method}"
    invalidIdx idx _ := return .error (← getRef) m!"Invalid index {idx}"
    invalidInputIdx s := return .error (← getRef) m!"Invalid index {s}"
    invalidInputParam s := return .error (← getRef) m!"Invalid param {s}"
    mkError s := return .mk (← show IO _ from s.error.toMessageData.toString) .null
  }
  -/
  let repl := MetaRepl.jsonRepl (m := TacticM) (cmds := cmds) 
    (return (← getUnsolvedGoals).isEmpty) 
    (fun s => return .error (← getRef) s) 
    (fun e => e.toMessageData.toString)
  inputCtx.visitOriginalTacticInfos (filter := fun _ => return true) fun ctx info => do
    --println! ← info.format ctx
    info.runTacticM ctx <| discard <| repl.run
  -/
  return 0
