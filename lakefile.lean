import Lake
open Lake DSL

package «algebra» where
  -- add package configuration options here

lean_lib «Algebra» where
  -- add library configuration options here

@[default_target]
lean_exe «algebra» where
  root := `Main
