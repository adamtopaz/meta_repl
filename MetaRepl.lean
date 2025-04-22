import MetaRepl.Command
import MetaRepl.History
import MetaRepl.Repl
import MetaRepl.Types

namespace MetaRepl

@[command close]
def closeCmd [Monad m] [MonadState ReplSignal m] : Command m where
  description := "Send the close signal to the REPL"
  paramSchema := json% { type : "null" }
  outputSchema := json% { type : "null" }
  passive := true
  run _ := do 
    modify fun _ => .close
    return ⟨.null⟩
