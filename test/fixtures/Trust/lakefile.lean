/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

/-! The `Trust` fixture (PLAN §2.2). `lake build -Kweak=1` swaps the
definition of `Trust.Hyp` for a vacuous one, which the drift tests of
DESIGN §10.3 must catch. -/

package «trust-fixture»

/-- The variant of `Trust.Hyp` to build. Changing it changes the source
directory, so Lake rebuilds everything downstream. -/
def variantDir : System.FilePath :=
  if (get_config? weak).isSome then "variants/weak" else "variants/strong"

lean_lib TrustVariant where
  srcDir := variantDir

@[default_target]
lean_lib Trust
