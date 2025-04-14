import Lean

open Lean

namespace MetaRepl

structure Input where
  method : String
  param : Json
deriving ToJson, FromJson

structure Result where
  data : Json
deriving ToJson, FromJson

structure Error where
  message : String
  data : Json
deriving ToJson, FromJson

inductive Output where
  | result : Result → Output
  | error : Error → Output
deriving ToJson, FromJson
