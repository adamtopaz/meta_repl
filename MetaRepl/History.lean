import MetaRepl.Command

open Lean

namespace MetaRepl

structure HistoryStep (α ω : Type) where
  action : Option α
  result : ω 
  startIdx : Nat
  endIdx : Nat

structure History (α ω σ : Type) where
  head : Nat
  states : Array σ
  history : Array <| HistoryStep α ω

abbrev HistoryT (α ω : Type) (m : Type → Type) 
    [STWorld w m] [MonadBacktrack σ m] :=
  StateRefT (History α ω σ) m

instance [STWorld w m] [MonadBacktrack σ m] : 
    MonadBacktrack σ (HistoryT α ω m) where
  saveState := show m _ from saveState
  restoreState s := show m _ from restoreState s

instance [STWorld w m] [MonadBacktrack σ m] [MonadExcept ε m] : 
    MonadExcept ε (HistoryT α ω m) where
  throw e _ := throw e
  tryCatch e f s := tryCatch (e s) (fun t => f t s)

end MetaRepl
