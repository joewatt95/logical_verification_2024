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
  git "v4.13.0"

require "leanprover-community" / "plausible" @
  git "v4.14.0-rc1"

require "leanprover-community" / "Duper" @
  git "v0.0.20"

require "ufmg-smite" / "smt" @
  git "39b27823e47de6da73e7724c933d169dac7aac91"

require "marcusrossel" / "egg" @
  git "7af87123bf258490f273df28d83b26143b6e9a24"

-- require "LeanCopilot" @
--   git "v1.4.0"

require "nomeata" / "loogle" @
  git "3791f4883b7f970e729b962d82976453ef1104a4"
