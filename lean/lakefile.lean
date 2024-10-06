import Lake
open Lake DSL

-- This is needed because we compile and link against the C++ API of cvc5.
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

require "leanprover-community" / "mathlib" @
  git "v4.11.0"

require "leanprover-community" / "Duper" @
  git "v0.0.16"

require "leanprover-community" / "LeanSearchClient" @
  git "v4.11.0"
  from
    git "https://github.com/leanprover-community/LeanSearchClient" @
    "v4.11.0"

require "ufmg-smite" / "smt" @
  git "0ad8dee4b3acf04bad031a7d1528c58e68193c3d"

require "marcusrossel" / "egg" @
  git "c51f43f79a4ed5dacadc7ae2500828b6534bfab3"

-- require "LeanCopilot" @
--   git "v1.4.0"

require "nomeata" / "loogle" @
  git "f46663afcd4067a606094dda363f67922e6990a4"
