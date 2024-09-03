import Lake
open Lake DSL

package «pdl» where
  -- add any package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.11.0"

@[default_target]
lean_lib «Pdl» where
  -- add any library configuration options here

lean_lib «Bml» where
  -- add any library configuration options here
