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

require "joewatt95" / "smt"
  from git "https://github.com/joewatt95/lean-smt"
  @ "583ba7af756cf263704a6b293ca59e3adacd39f0"

require "marcusrossel" / "egg" @
  git "7af87123bf258490f273df28d83b26143b6e9a24"

-- require "LeanCopilot" @
--   git "v1.4.0"

require "nomeata" / "loogle" @
  git "f46663afcd4067a606094dda363f67922e6990a4"
