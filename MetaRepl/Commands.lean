import MetaRepl.Command

namespace MetaRepl

@[command ping]
def pingPong [Monad m] : Command m where
  description := "Reply with the input parameters"
  run j := return Lean.toJson j

open Lean Elab Tactic in

@[command tactic]
def tactic : Command TacticM where
  paramSchema := json% { type : "array" }
  description := "Eval a tactic"
  run 
  | some (.arr tacs) => do
      let .ok tacs := tacs.mapM fun j => j.getStr?
        | throwError "Error"
      let env ← getEnv
      let .ok tacs := tacs.mapM fun j => 
        Lean.Parser.runParserCategory env `tactic j
        | throwError "Error"
      for tac in tacs do 
        evalTactic tac
      return .null
  | some (.obj _) => throwError "Invalid parameters provided"
  | none => throwError "No parameters provided"

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
