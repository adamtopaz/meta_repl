import MetaRepl.Command

open Lean

namespace MetaRepl

structure ParentStruct (α ω : Type) where
  action : Option α
  result : ω
  parentIdx : Nat

structure History (α ω σ : Type) where
  head : Nat
  states : Array σ
  parent : Std.HashMap Nat <| ParentStruct α ω

def History.record (h : History α ω σ) (a : Option α) (w : ω) (s : Option σ) :
    History α ω σ :=
match s with
| some s => {
    head := h.states.size
    states := h.states.push s
    parent := h.parent.insert h.states.size { action := a, result := w, parentIdx := h.head }
  }
| none => {
    head := h.head
    states := h.states
    parent := h.parent.insert h.head { action := a, result := w, parentIdx := h.head }
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
