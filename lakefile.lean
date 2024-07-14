import Lake
open Lake DSL

package «formalSnarksProject» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «FormalSnarksProject» {
  -- add any library configuration options here
}
