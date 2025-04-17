import MetaRepl

open MetaRepl Lean Elab Tactic

@[command close]
def closeCmd [Monad m] [MonadState ReplSignal m] : Command m where
  run _ := do modify fun _ => .close ; return ⟨.null⟩

@[command tactic]
def tacticCmd : Command TacticM where
  description := "Evaluate a tactic"
  paramSchema := json% { type : "string" }
  outputSchema := json% { type : "null" }
  passive := false
  run j := do
    let .ok tac := j.getStr? | throwError "{j} is not a string"
    let .ok tac := Lean.Parser.runParserCategory (← getEnv) `tactic tac
      | throwError "Failed to parse tactic {tac}"
    evalTactic tac
    return ⟨.null⟩

@[command goals]
def goalsCmd : Command TacticM where
  description := "Display current goals"
  paramSchema := json% { type : "null" }
  outputSchema := json% {
    type: "array",
    items: { type : "string" }
  }
  run _ := do
    let goals ← getUnsolvedGoals
    let goals ← goals.mapM fun goal => Meta.ppGoal goal
    let goals := goals.map fun goal => goal.pretty
    return ⟨toJson goals⟩

def cmds : Commands (ReplT TacticM) := commands(tactic,goals,close)

def repl : ReplStruct (m := TacticM) cmds where
  init := do 
    let j : Array Json := cmds.data.toArray.map fun (method, cmd) => json% {
      method : $method,
      description : $cmd.description,
      paramSchema : $cmd.paramSchema,
      outputSchema : $cmd.outputSchema,
      passive : $cmd.passive
    }
    let stdout ← show IO _ from IO.getStdout
    stdout.putStrLn (toJson j).compress
    stdout.flush
  term := return
  finished := return (← getUnsolvedGoals).isEmpty
  unknownCmd _ input := return .error (← getRef) s!"Unknown command {input.method}"
  invalidIdx idx _ := return .error (← getRef) s!"Invalid idx {idx}"
  strToErr s := return .error (← getRef) s
  errToStr e := e.toMessageData.toString

def runRepl : TacticM (History Input Output SavedState) := repl.jsonRepl.run

def file := "example (p q : Prop) (h : p → q) (hp : p) : p ∧ q := by sorry"

open Frontend
def main : IO Unit := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let inputCtx : Parser.InputContext := Parser.mkInputContext file "<file>"
  let options : Options := {}
  let (header, parserState, messages) ← Lean.Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header options messages inputCtx
  let cmdState := Command.mkState env messages options
  let cmdState := { cmdState with infoState.enabled := true }
  let ctx : Frontend.Context := ⟨inputCtx⟩
  let state : Frontend.State := {
    commandState := cmdState
    parserState := parserState
    cmdPos := parserState.pos
  }
  (go.run ctx).run' state
where
go : Frontend.FrontendM Unit := do
  processCommands
  let trees := (← get).commandState.infoState.trees
  for tree in trees do tree.visitM' (preNode := fun _ _ _ => pure true) fun ctxInfo info _ => do 
    match info, info.stx.getHeadInfo?, info.stx with
    | .ofTacticInfo tac, some (.original ..), .node _ `Lean.Parser.Tactic.tacticSorry _ => do
      let ctxInfo := { ctxInfo with mctx := tac.mctxBefore }
      let runRepl := runRepl.run { elaborator := .anonymous } |>.run' { goals := tac.goalsBefore }
      discard <| ctxInfo.runMetaM {} <| Term.TermElabM.run' <| runRepl
    | _, _, _ => return

