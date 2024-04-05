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
    @ "483848e8afb952d25f51f5ab865b4b3525c086b9"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "1507142f79f05371e5eb25202eec6396bb940d72"

require Duper from git
  "https://github.com/leanprover-community/duper"
    @ "2a92f810e3c0c3f9431c6abc1588f540ca621f49"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.0"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "34713b27a0cab653313288397c5f0efb6b2061b0"
