import Lake
open Lake DSL

package «pdl»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.22.0-rc3"

@[default_target]
lean_lib «Pdl»

lean_lib «Bml»
