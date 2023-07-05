import Lake
open Lake DSL

package «Functional-Programming-In-Lean» {
  -- add package configuration options here
}

lean_lib «FunctionalProgrammingInLean» {
  -- add library configuration options here
}

--@[default_target]
lean_exe «Functional-Programming-In-Lean» {
  root := `Main
}
