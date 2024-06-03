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
    @ "7aa5faafc8815ed358053e05f51f4aea8e47f4e2"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "91cd0e81ec8bd16baa2c08e3d00a7f8e473477b4"

require Duper from git
  "https://github.com/leanprover-community/duper" @ "v0.0.12"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.2"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "fa2ddf5771cc25b0d6e552ef63b51a68351e437f"
