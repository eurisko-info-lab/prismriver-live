import Lake
open Lake DSL

package prismriver_live

require Prismriver from git
  "https://github.com/lenianiva/Prismriver" @ "main"

@[default_target]
lean_exe prismriver_live where
  root := `Main
