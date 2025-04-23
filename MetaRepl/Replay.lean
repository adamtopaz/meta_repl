import MetaRepl.History

open Lean

namespace MetaRepl

def Commands.replay 
    [Monad m] [MonadBacktrack σ m] [MonadExcept ε m]
    (cmds : Commands m) (steps : Array Input) : 
    m (Array Result) := do
  let mut out := #[]
  for step in steps do 
    let .ok res ← cmds.run step | continue
    out := out.push res
  return out

end MetaRepl
