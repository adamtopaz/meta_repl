import MetaRepl

def main (args : List String) : IO UInt32 := do
  let some path := args[0]? 
    | throw <| .userError "Usage: lake exe meta_repl FILEPATH"
  let path : System.FilePath := .mk path
  let inputCtx ← Lean.Parser.readInputContext path
  inputCtx.visitOriginalTacticInfos (filter := fun _ => return true) fun ctx info => 
    { ctx with mctx := info.mctxBefore }.runMetaM {} sorry 
  return 0
