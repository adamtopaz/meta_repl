# Meta Repl

This library can be used to create REPLs of various kinds.

To create a REPL which can run in a monad `m`, first create various commands of type 
`MetaRepl.Command m`, and tag them with the `@[command trigger]` attribute.
Here `trigger` is a Lean4 name that will be used by the REPL to run the command.

