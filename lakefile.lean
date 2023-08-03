import Lake
open Lake DSL

package foo {
  -- add package configuration options here
}

require mathlib 
  from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib FormalSystems