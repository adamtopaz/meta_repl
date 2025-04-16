import MetaRepl

open Lean Elab Tactic

def main (args : List String) : IO UInt32 := do
  let some path := args[0]?
    | throw <| .userError "Usage: lake exe meta_repl FILEPATH"
  let path : System.FilePath := .mk path
  let inputCtx ← Lean.Parser.readInputContext path
  let cmds : MetaRepl.Commands (MetaRepl.ReplT TacticM) := 
    commands(close, tactic, goals)
  let repl : MetaRepl.UserRepl (m := TacticM) cmds := {
    init := return
    term := return
    finished := return false
    unknownCmd _ input := return .error (← getRef) m!"Unknown command {input.method}"
    invalidIdx idx _ := return .error (← getRef) m!"Invalid index {idx}"
    invalidInputIdx s := return .error (← getRef) m!"Invalid index {s}"
    invalidInputParam s := return .error (← getRef) m!"Invalid param {s}"
    mkError s := return .mk (← show IO _ from s.error.toMessageData.toString) .null
  }
  inputCtx.visitOriginalTacticInfos (filter := fun _ => return true) fun ctx info => do
    println! ← info.format ctx
    info.runTacticM ctx <| discard <| repl.repl.run
  return 0
