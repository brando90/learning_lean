import Lake
open Lake DSL

package «lean_src_proj» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LeanSrcProj» {
  -- add any library configuration options here
}
require aesop from git "https://github.com/JLimperg/aesop"
