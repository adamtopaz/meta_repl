import MetaRepl.Command
import MetaRepl.History
import MetaRepl.Repl
import MetaRepl.Types
import MetaRepl.Replay

namespace MetaRepl

@[command close]
def closeCmd [Monad m] [MonadState ReplSignal m] : Command m where
  description := "Send the close signal to the REPL"
  paramSchema := json% { type : "null" }
  outputSchema := json% { type : "null" }
  passive := true
  impl _ := do 
    modify fun _ => .close
    return ⟨.null⟩

@[command forget]
def forgetCmd [Monad m] [STWorld w m] [MonadLiftT (ST w) m] [Lean.MonadBacktrack σ m] : 
    Command (ReplT m) where
  description := "Forget the REPL history"
  paramSchema := json% { type : "null" }
  outputSchema := json% { type : "null" }
  passive := true
  impl _ := do 
    let s ← Lean.saveState
    set (σ := History Input σ) {
      head := 0
      states := #[s]
      parent := {}
    }
    return .mk .null
