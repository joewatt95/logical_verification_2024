import Lake

open Lake DSL

package love where
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]

@[default_target]
lean_lib LoVe where
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
    @ "f3ca78288e785e4c4219ab0e6a88af33dcb5b85f"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "664c8f272a9f5552fd1bac68644e0d3b19c9438e"

require Duper from git
  "https://github.com/leanprover-community/duper" @ "v0.0.11"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.0"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "34713b27a0cab653313288397c5f0efb6b2061b0"
