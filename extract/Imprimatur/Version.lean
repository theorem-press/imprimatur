/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Version information
-/

namespace Imprimatur

/-- The version of the extractor. -/
def version : String := "0.0.0"

/-- The schema identifier of the bundles this extractor writes (DESIGN §8). -/
def bundleSchema : String := "imprimatur-bundle/1"

/-- The Lean toolchain this extractor was compiled with, as in a
`lean-toolchain` file's version part (`v4.31.0`, `v4.28.0-rc1`). -/
def leanVersion : String := "v" ++ Lean.versionString

end Imprimatur
