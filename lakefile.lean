import Lake
open Lake DSL

package jalean {
  -- add package configuration options here
}

lean_lib Jalean {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe jalean {
  root := `Main
}
