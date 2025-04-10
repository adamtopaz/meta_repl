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

inductive Output where
  | response : Json → Output
  | error : ErrorObj → Output

structure Server (m : Type → Type) where
  getRequest : m Request
  notify (method : String) (params : Json) : m Unit
  getOutput (method : String) (params : Json) : m Output
  sendResponse (response : Response) : m Unit
  sendError (error : Error) : m Unit

def Server.step [Monad m] (s : Server m) : m Unit := do
  let req ← s.getRequest
  match req.id with
  | some id => match ← s.getOutput req.method req.params with
    | .response res => s.sendResponse <| .mk res id
    | .error err => s.sendError <| .mk err id
  | none => s.notify req.method req.params

partial
def Server.run [Monad m] [MonadLiftT IO m] (s : Server m) : 
    m Unit := do 
  s.step
  if ← show IO _ from  IO.checkCanceled then return
  s.run

structure StdServer (m : Type → Type) where
  notify (method : String) (params : Json) : m Unit
  getOutput (method : String) (params : Json) : m Output

-- Single thread
def StdServer.server [Monad m] [MonadLiftT IO m] (s : StdServer m) : 
    Server m where
  getRequest := do 
    let stdin ← show IO _ from IO.getStdin
    let line ← stdin.getLine
    match Json.parse line.trim with 
    | .ok j => 
      match fromJson? (α := Request) j with 
      | .ok req => return req
      | .error e => show IO _ from throw <| .userError <| 
        s!"Failed to parse json\n\n{j}\n\nas request:\n{e}"
    | .error e => show IO _ from throw <| .userError <| 
      s!"Failed to parse\n\n{line}\n\nas json:\n{e}"
  notify := s.notify
  getOutput := s.getOutput
  sendResponse res := do 
    let stdout ← show IO _ from IO.getStdout
    stdout.putStrLn <| (toJson res).compress
    stdout.flush
  sendError err := do 
    let stdout ← show IO _ from IO.getStdout
    stdout.putStrLn <| (toJson err).compress
    stdout.flush

def StdServer.step [Monad m] [MonadLiftT IO m] (s : StdServer m) : m Unit := 
  s.server.step

def StdServer.run [Monad m] [MonadLiftT IO m] (s : StdServer m) : m Unit := 
  s.server.run
