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

require "ufmg-smite" / smt @
  git "b2a9bacb2c8c5b6d31537d23fa56845c0358d232"

require "leanprover-community" / Duper @
  git "v0.0.21"

require "marcusrossel" / egg @
  git "3c1a713c803c08cb8be8f6adc89394441eb7fbb0"

require "nomeata" / loogle @
  git "4e1aab07fa10f263a2110787180f8f5db93ee650"

require "leanprover" / verso @
  git "v4.14.0"

require "leanprover-community" / mathlib @
  git "v4.14.0"
