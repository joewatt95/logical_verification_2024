import Lake
open Lake DSL

-- This is needed because we compile and link against the C++ API of cvc5.
-- private def args : Array String :=
--   #[s!"--load-dynlib={libcpp}"]
--   where
--     libcpp :=
--       if System.Platform.isWindows then "libstdc++-6.dll"
--       else if System.Platform.isOSX then "libc++.dylib"
--       else "libstdc++.so.6"

package love where
  -- moreLeanArgs := args
  -- moreGlobalServerArgs := args

  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]

@[default_target]
lean_lib LoVe where
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]

require "ufmg-smite" / smt @
  git "4cdea120ba132ba0cb817e7fd516a967f1148752"

require "leanprover-community" / Duper @
  git "v0.0.22"

require "marcusrossel" / egg @
  git "12971b1572720cac3116237f5383751abfb1e12a"

require "nomeata" / loogle @
  git "026c9d97a9e93f53852c44a411d91a79acb4fb9c"

require "leanprover" / verso @
  git "v4.15.0"

require "leanprover-community" / mathlib @
  git "v4.15.0-patch1"
