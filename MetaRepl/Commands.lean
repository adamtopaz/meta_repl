import MetaRepl.Command

namespace MetaRepl

@[command ping]
def pingPong [Monad m] : Command m where
  description := "Reply with the input parameters" 
  run := pure

open Lean Elab Tactic in

@[command tactic]
def tactic : Command TacticM where
  paramSchema := json% { type : "string" }
  description := "Eval a tactic"
  run p := do 
    match p.getStr? with
    | .ok s => match Parser.runParserCategory (← getEnv) `tactic s with
      | .ok tac => 
        evalTactic tac
        return .null
      | .error e => throwError s!"Failed to parse parameter\n{s}\nas a tactic:\n{e}"
    | .error e => throwError s!"Parameter\n{p}\nis not a string:\n{e}"


open Lean Elab Tactic in

@[command goals]
def goals : Command TacticM where
  paramSchema := json% { type : "null" }
  outputSchema := json% {
    type: "array",
    items: { type : "string" } 
  }
  description := "Get current goals"
  run _ := withoutModifyingState do
    let goals ← getUnsolvedGoals
    let out : Array String ← goals.toArray.mapM fun goal => do
      let fmt ← Meta.ppGoal goal
      return fmt.pretty
    return toJson out

end MetaRepl
