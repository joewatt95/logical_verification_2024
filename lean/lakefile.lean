import Lake
open Lake DSL

private def args : Array String :=
  #[s!"--load-dynlib={libcpp}"]
  where
    libcpp :=
      if System.Platform.isWindows then "libstdc++-6.dll"
      else if System.Platform.isOSX then "libc++.dylib"
      else "libstdc++.so.6"

package love where
  moreLeanArgs := args
  moreGlobalServerArgs := args
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
    @ "v4.9.0"

require Duper from git
  "https://github.com/leanprover-community/duper"
    @ "d198aba058bbf37e602d68fd08903281bfe6e3a6"

-- require smt from git
--   "https://github.com/ufmg-smite/lean-smt"
--     @ "2899f02744cc12636f71c04e200bce0b308f73b5"

require egg from git
  "https://github.com/marcusrossel/lean-egg"
    @ "abaab85d51d33ef01ed8c757bfb49cc55abae229"

-- require LeanCopilot from git
--   "https://github.com/lean-dojo/LeanCopilot" @ "v1.3.0"

require loogle from git
  "https://github.com/nomeata/loogle"
    @ "cd8680514b046e71b79183bf3c64de3350cd0c10"
