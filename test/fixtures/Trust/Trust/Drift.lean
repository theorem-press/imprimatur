/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TrustVariant.Hyp

/-!
A theorem whose hypothesis is defined in `TrustVariant/Hyp.lean`, which has a
real and a weakened version (see `lakefile.lean`). The statement reads the
same either way; `stmtHash` must differ.
-/

namespace Trust

theorem uses_hyp (n : Nat) (h : Hyp n) : Hyp (n + 2) := by
  unfold Hyp at *
  first | omega | trivial

end Trust
