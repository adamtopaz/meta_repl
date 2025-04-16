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

def History.record (h : History α ω σ) (a : Option α) (w : ω) (s : Option σ) :
    History α ω σ :=
match s with
| some s => {
    head := h.states.size
    states := h.states.push s
    history := h.history.push {
      action := a
      result := w
      startIdx := h.head
      endIdx := h.states.size
    }
  }
| none => {
    head := h.head
    states := h.states
    history := h.history.push {
      action := a
      result := w
      startIdx := h.head
      endIdx := h.head
    }
  }

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

def recordHistory
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m] [MonadBacktrack σ m]
    (a : Option α) (w : ω) (s : Option σ) :
    HistoryT α ω m Unit := do
  modify fun h => h.record a w s

def getHead
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m] [MonadBacktrack σ m] :
    HistoryT α ω m Nat := return (← get).head

end MetaRepl
