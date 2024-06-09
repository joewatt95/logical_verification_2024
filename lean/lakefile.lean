import Lake

open Lake DSL

package love where
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]

@[default_target]
lean_lib LoVe where
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
    @ "v4.8.0"

require Duper from git
  "https://github.com/leanprover-community/duper"
    @ "v0.0.13"

require egg from git
  "https://github.com/marcusrossel/lean-egg"
    @ "7624eb676fcab4b60fcb2cddf3e45202126b4338"

-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot" @ "v1.2.2"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "5faf10c5a55c01b1b55585fe44311414df5af3c4"
