import Lake

open Lake DSL

package «AdaptiveGroupSequentialTrials» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

-- Pin StatsMLlib's matching release. StatsMLlib in turn pins Mathlib and Lean to v4.33.0,
-- giving the formalization a reproducible dependency graph without a vendored checkout.
require «StatsMLlib» from git
  "https://github.com/Lean-MoDS/StatsMLlib.git" @ "v4.33.0"

@[default_target]
lean_lib «AdaptiveGroupSequentialTrials» where
  globs := #[.andSubmodules `AdaptiveGroupSequentialTrials]
