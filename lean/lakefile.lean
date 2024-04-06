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
    @ "3f22805959e0d0d2a79b84610a1fefaa86b58391"

require auto from git
  "https://github.com/leanprover-community/lean-auto"
    @ "27f1b265f6ab512cfa38c874b9070f63b0caf7ed"

require Duper from git
  "https://github.com/leanprover-community/duper"
    @ "2a92f810e3c0c3f9431c6abc1588f540ca621f49"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.0"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "34713b27a0cab653313288397c5f0efb6b2061b0"
