import Lean

open Lean Elab Frontend Parser

def Lean.Parser.InputContext.runFrontend
    (inputCtx : InputContext)
    (m : Frontend.FrontendM α)
    (options : Options := {}) : IO (α × Frontend.State) := do
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
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
  StateRefT'.run (ReaderT.run m ctx) state

def Lean.Parser.InputContext.runFrontend'
    (inputCtx : InputContext)
    (m : Frontend.FrontendM α)
    (options : Options := {}) : IO α :=
  Prod.fst <$> inputCtx.runFrontend m options

def Lean.Parser.readInputContext
    (path : System.FilePath) :
    IO InputContext := do
  return mkInputContext (← IO.FS.readFile path) "<input>"

def Lean.Parser.InputContext.withInfoTrees
    (inputCtx : InputContext)
    (e : InfoTree → FrontendM α)
    (options : Options := {}) :
    IO (PersistentArray α) := inputCtx.runFrontend' (options := options) do
  processCommands
  let trees := (← get).commandState.infoState.trees
  trees.mapM e

def Lean.Parser.InputContext.withVisitInfos
    (inputCtx : InputContext)
    (pre : ContextInfo → Info → PersistentArray InfoTree → FrontendM Bool := fun _ _ _ => pure true)
    (post : ContextInfo → Info → PersistentArray InfoTree → List (Option α) → FrontendM α)
    (ctx? : Option ContextInfo := none)
    (options : Options := {}) :
    IO (PersistentArray (Option α)) := inputCtx.runFrontend' (options := options) do
  processCommands
  let trees := (← get).commandState.infoState.trees
  trees.mapM <| fun tree => tree.visitM pre post ctx?

def Lean.Parser.InputContext.withVisitInfos'
    (inputCtx : InputContext)
    (pre : ContextInfo → Info → (children : PersistentArray InfoTree) → FrontendM Bool := fun _ _ _ => pure true)
    (post : ContextInfo → Info → (children : PersistentArray InfoTree) → FrontendM Unit := fun _ _ _ => pure ())
    (ctx? : Option ContextInfo := none)
    (options : Options := {}) :
    IO Unit :=
  inputCtx.runFrontend' (options := options) do
  processCommands
  let trees := (← get).commandState.infoState.trees
  discard <| trees.mapM <| fun tree => tree.visitM' pre post ctx?

def Lean.Parser.InputContext.withFoldingInfos
    (inputCtx : InputContext)
    (f : ContextInfo → Info → α → FrontendM α)
    (init : α)
    (options : Options := {}) :
    IO (PersistentArray α) :=
  inputCtx.runFrontend' (options := options) do
  processCommands
  let trees := (← get).commandState.infoState.trees
  trees.mapM fun tree => tree.foldInfoM f init

def Lean.Parser.InputContext.visitOriginalTacticInfos
    (inputCtx : InputContext)
    (go : ContextInfo → TacticInfo → FrontendM Unit)
    (filter : TacticInfo → FrontendM Bool)
    (options : Options := {}) : IO Unit := 
      inputCtx.withVisitInfos' (options := options) (ctx? := none) 
      (pre := fun _ _ _ => pure true) 
      fun ctxInfo info _ => do 
  match info, info.stx.getHeadInfo? with 
  | .ofTacticInfo i, some (.original ..) => 
    if ← filter i then go ctxInfo i else return
  | _, _ => return


def Lean.Elab.TacticInfo.runTacticM 
    (info : TacticInfo) (ctx : ContextInfo) (e : Elab.Tactic.TacticM α) : IO α := 
  { ctx with mctx := info.mctxBefore }.runMetaM {} <| Term.TermElabM.run' <| 
  e.run { elaborator := .anonymous } |>.run' { goals := info.goalsBefore }
