import Lake
open Lake DSL

package formatted_graph where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

require Qq from git
  "https://github.com/leanprover-community/quote4" @ "v4.30.0"

@[default_target]
lean_lib FormattedGraph
