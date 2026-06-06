import Lake
open Lake DSL

package «observerEquivariance» where
  -- no special settings needed to start

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «ObserverEquivariance» where
  -- the library root
