import Lake
open Lake DSL

package foo {
  -- add package configuration options here
}

require preliminaries from "preliminaries"

@[defaultTarget]
lean_exe foo {
  root := `Main
}
