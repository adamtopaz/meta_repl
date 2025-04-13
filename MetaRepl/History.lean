import Lean

open Lean

namespace MetaRepl

structure History (σ : Type) where
  states : Array σ 

abbrev HistoryT (m : Type → Type) 
    [MonadBacktrack σ m] [STWorld w m] :=
  StateRefT (History σ) m

instance [MonadBacktrack σ m] [STWorld w m] : 
    MonadBacktrack σ (HistoryT m) where
  saveState := show m _ from saveState
  restoreState s := show m _ from restoreState s

instance [MonadExcept ε m] [MonadBacktrack σ m] [STWorld w m] :
    MonadExcept ε (HistoryT m) where
  throw e := show m _ from throw e
  tryCatch e f s := tryCatch (e s) (fun err => f err s)

end MetaRepl
