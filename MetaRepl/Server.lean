import Lean

open Lean

namespace MetaRepl

structure Request where
  method : String
  params : Json
  id : Option UInt64 -- None is a notification
deriving ToJson, FromJson

structure Response where
  result : Json
  id : UInt64
deriving ToJson, FromJson

structure ErrorObj where
  code : UInt64
  message : String
  data : Json
deriving ToJson, FromJson

structure Error where
  error : ErrorObj
  id : UInt64
deriving ToJson, FromJson

structure Server (m : Type → Type) [MonadExcept ε m] where
  getRequest : m Request
  notify (req : Request) : m Unit
  mkError (req : Request) (err : ε) : m Error
  respond (method : String) (params : Json) : m Json
  sendResponse (response : Response) : m Unit
  sendError (err : Error) : m Unit

def Server.step [Monad m] [MonadExcept ε m]
    (s : Server m) : m Unit := do
  let req ← s.getRequest
  match req.id with
  | some id => 
    try 
      let res ← s.respond req.method req.params
      s.sendResponse <| .mk res id
    catch e => s.sendError <| ← s.mkError req e
  | none => 
    try s.notify req
    catch e => s.sendError <| ← s.mkError req e

partial
def Server.run [Monad m] [MonadLiftT IO m] [MonadExcept ε m] (s : Server m) : 
    m Unit := do 
  s.step
  if ← show IO _ from  IO.checkCanceled then return
  s.run

structure StdServer (m : Type → Type) [MonadExcept ε m] where
  mkError (req : Request) (err : ε) : m Error
  respond (method : String) (params : Json) : m Json

-- Single thread
def StdServer.server [Monad m] [MonadLiftT IO m] 
    [MonadExcept ε m] (s : StdServer m) : 
    Server m where
  getRequest := do
    let stdin ← show IO _ from IO.getStdin
    let line ← stdin.getLine
    match Json.parse line.trim with
    | .ok out => match fromJson? (α := Request) out with
      | .ok out => return out
      | .error e => show IO _ from throw <| .userError s!"[FATAL] Failed to parse json\n\n{out}\n\nas request:\n\n{e}"
    | .error e => show IO _ from throw <| .userError s!"[FATAL] Failed to parse\n\n{line}\n\nas json:\n\n{e}"
  notify req := do 
    let s ← show IO _ from IO.getStdin
    s.putStrLn (toJson req).compress
    s.flush
  mkError := s.mkError
  respond := s.respond
  sendResponse res := do 
    let s ← show IO _ from IO.getStdin
    s.putStrLn (toJson res).compress
    s.flush
  sendError err := do 
    let s ← show IO _ from IO.getStdin
    s.putStrLn (toJson err).compress
    s.flush
