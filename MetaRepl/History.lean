import MetaRepl.Command

open Lean

namespace MetaRepl

structure ParentStruct (α : Type) where
  action : α
--  result : ω
  parentIdx : Nat

structure History (α ω σ : Type) where
  head : Nat
  states : Array σ
  parent : Std.HashMap Nat <| ParentStruct α 

def History.record (h : History α ω σ) (a : α) (s : Option σ) :
    History α ω σ :=
match s with
| some s => {
    head := h.states.size
    states := h.states.push s
    parent := h.parent.insert h.states.size { action := a, parentIdx := h.head }
  }
| none => {
    head := h.head
    states := h.states
    parent := h.parent.insert h.head { action := a, parentIdx := h.head }
  }

def History.revert (h : History α ω σ) : Option α × History α ω σ := 
  match h.parent.get? h.head with
  | some ⟨a,i⟩ => (a, { h with head := i })
  | none => (none, h)

def History.trace (h : History α ω σ) : Array α := Id.run do 
  let mut out := #[]
  let mut hist := h
  while true do
    let ⟨a,h⟩ := hist.revert
    match a with 
    | some a => 
        out := out.push a
        hist := h
    | none => break
  return out

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
    (a : α) (s : Option σ) :
    HistoryT α ω m Unit := do
  modify fun h => h.record a s

def getHead
    [Monad m] [STWorld w m] [MonadLiftT (ST w) m] [MonadBacktrack σ m] :
    HistoryT α ω m Nat := return (← get).head

end MetaRepl
