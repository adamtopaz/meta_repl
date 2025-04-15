import MetaRepl.Command

namespace MetaRepl

@[command ping]
def pingPong [Monad m] : Command m where
  description := "Reply with the input parameters"
  run j := return .mk j

open Lean Elab Tactic in

@[command tactic]
def tactic : Command TacticM where
  paramSchema := json% { type : "string" }
  description := "Eval a tactic"
  run j := do
    let .ok tac := j.getStr?
      | throwError "{j} is not a string"
    let .ok tac := Lean.Parser.runParserCategory (← getEnv) `tactic tac
      | throwError "{tac} is not a tactic"
    evalTactic tac
    return .mk .null

open Lean Elab Tactic in

@[command goals]
def goals : Command TacticM where
  paramSchema := json% { type : "null" }
  outputSchema := json% {
    type: "array",
    items: { type : "string" }
  }
  description := "Get goals"
  run _ := withoutModifyingState do
    let goals ← getUnsolvedGoals
    let out : Array String ← goals.toArray.mapM fun goal => do
      let fmt ← Meta.ppGoal goal
      return fmt.pretty
    return .mk <| toJson out

end MetaRepl
