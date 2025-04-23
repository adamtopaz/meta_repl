import MetaRepl.History

open Lean

namespace MetaRepl

def Commands.replay 
    [Monad m] [MonadBacktrack σ m] [MonadExcept ε m]
    (cmds : Commands m) (history : History Input Output σ) : 
    m (Array Result) := do
  let trace := history.trace
  let mut out := #[]
  for step in trace do 
    let .ok res ← cmds.run step | continue
    out := out.push res
  return out

end MetaRepl
