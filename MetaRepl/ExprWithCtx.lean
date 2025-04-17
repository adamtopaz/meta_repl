import MetaRepl.Command

open Lean

namespace MetaRepl

structure ExprWithCtx where
  expr : Expr
  lctx : LocalContext

structure ExprWithCtxSavedState extends ExprWithCtx where
  core : Core.SavedState

abbrev ExprCtxM := StateRefT ExprWithCtx CoreM

instance : MonadBacktrack ExprWithCtxSavedState ExprCtxM where
  saveState := do 
    let coreState ← show CoreM _ from Core.saveState
    let state ← get
    return .mk state coreState
  restoreState s := do 
    show CoreM _ from s.core.restore
    set s.toExprWithCtx

nonrec def ExprCtxM.run (e : ExprCtxM α) (ec : ExprWithCtx) :
  CoreM (α × ExprWithCtx) := e.run ec

def ExprCtxM.liftMetaM (e : Expr → MetaM α) : ExprCtxM α := do 
  (e (← get).expr).run' { lctx := (← get).lctx }

def ExprCtxM.pp : ExprCtxM Format := .liftMetaM fun e => do 
  let m ← Meta.mkFreshExprMVar e -- HACK
  Meta.ppGoal m.mvarId!

@[command ExprWithCtx.pp]
def ppCmd : Command ExprCtxM where
  run _ := do 
    let fmt ← ExprCtxM.pp
    return .mk <| toString fmt

@[command ExprWithCtx.intro]
def introCmd : Command ExprCtxM where
  passive := false
  run _ := do 
    set <| ← .liftMetaM (α := ExprWithCtx) fun e => match e with
      | .forallE nm tp body binfo => Meta.withLocalDecl nm binfo tp fun fvar => 
        let body := body.instantiateRev #[fvar]
        return ⟨body, ← getLCtx⟩
      | _ => do throwError "{← Meta.ppExpr e} is not universally quantified"
    return .mk .null

@[command ExprWithCtx.inferType]
def typeCmd : Command ExprCtxM where
  passive := false
  run _ := do 
    let tp : Expr ← .liftMetaM Meta.inferType
    modify fun ⟨_, ctx⟩ => ⟨tp, ctx⟩
    return .mk .null

end MetaRepl
