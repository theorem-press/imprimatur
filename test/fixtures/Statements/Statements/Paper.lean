/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Statements.Defs
import Imprimatur

/-! The paper's notation. -/

open Statements

-- An instance binder `[Positive n]` is stated as a hypothesis.
latex_notation Positive n => r"\mathsf{pos}(#n)"
