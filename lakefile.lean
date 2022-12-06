import Lake
open Lake DSL

package foo {
  -- add package configuration options here
}


@[defaultTarget]
lean_exe foo {
  root := `Main
}
