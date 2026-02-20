import Lake
open Lake DSL

package love where

@[default_target]
lean_lib LoVe where
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]

require "ufmg-smite" / smt @ git
  "3bc19f2d3caba4c5fbfe213143c79364c3d9c97a"

require "chasenorman" / Canonical @ git "v4.27.0"

require "JOSHCLUNE" / Hammer @ git "v4.27.0"

require "Joewatt95" / egg from git
  "https://github.com/Joewatt95/lean-egg" @
  "8b978c7e1614dc88b1165d0543141412f8631e29"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "79343e3e37b64046e6b555936682012e80300df1"

require "leanprover" / verso @ git "v4.27.0"

require "leanprover-community" / mathlib @ git "v4.27.0"
