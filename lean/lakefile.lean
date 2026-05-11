import Lake
open Lake DSL

package love where

@[default_target]
lean_lib LoVe where
  roots := #[`LoVe]
  globs := #[Glob.submodules `LoVe]

require "ufmg-smite" / smt @
  git "7d1d8239e78daa5197f9a71948776c4627049f5f"

require "chasenorman" / Canonical @ git "v4.29.0"

require "JOSHCLUNE" / Hammer @ git "v4.29.0"

require sos from
  git "https://github.com/kim-em/sos" @
  "4a92deb7a187abebda15d2e7f8509cf863811ac1"

require "nomeata" / calcify @
  git "b89b823f26eb35a1d9ed57af2663128d6b3a35c2"

require "nomeata" / loogle @
  git "8e80836a86196849b2393e7a752d6100c17b772d"

require "leanprover" / verso @ git "v4.29.0"

require "leanprover-community" / mathlib @ git "v4.29.1"
