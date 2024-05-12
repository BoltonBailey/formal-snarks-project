import Lake
open Lake DSL

package «formalSnarksProject» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "incr-tactic-fixes-toolchain"

@[default_target]
lean_lib «FormalSnarksProject» {
  -- add any library configuration options here
}
