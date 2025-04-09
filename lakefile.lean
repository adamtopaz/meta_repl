import Lake
open Lake DSL

package «meta_repl» where
  -- add package configuration options here

lean_lib «MetaRepl» where
  -- add library configuration options here

@[default_target]
lean_exe «meta_repl» where
  root := `Main
