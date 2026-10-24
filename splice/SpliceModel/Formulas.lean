/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Layout

/-!
# Formulas: what the emitter does with precedences

A formula is rendered as a `Doc` tree and emitted by
`Imprimatur.Layout.Doc.pieces`, the one place parentheses are decided
(DESIGN §7.1). The lemma here states that policy: a child is wrapped in
parentheses exactly when its precedence is below what its place needs. The
precedence a hole of a notation rule needs is one function,
`Doc.holeNeeds`, which the renderer (`Render.fillTemplate`) and the
validator's grammar (`Validate.ofRule`) both call, so that the grammar
demands of an argument what the renderer gives it, by construction rather
than by mirroring.
-/

namespace SpliceModel

open Imprimatur.Layout

/-- **Parentheses.** A child is parenthesised exactly when its precedence is
below what its place needs. -/
theorem Doc.pieces_child (m : Nat) (c : Doc) (depth : Nat) :
    (Doc.child m c).pieces depth =
      if c.prec < m then #[.text "(" 1] ++ c.pieces depth ++ #[.text ")" 1] else c.pieces depth := by
  rw [Doc.pieces]

/-- Inside braces, a hole needs nothing. -/
theorem Doc.holeNeeds_braced (prec : Nat) (assoc : String) {depth : Nat} (h : 0 < depth)
    (edge first last : Bool) : Doc.holeNeeds prec assoc depth edge first last = 0 := by
  simp [Doc.holeNeeds, h]

/-- A hole never needs more than atomic precedence. -/
theorem Doc.holeNeeds_le (prec : Nat) (assoc : String) (depth : Nat) (edge first last : Bool)
    (hp : prec < Doc.maxPrec) : Doc.holeNeeds prec assoc depth edge first last ≤ Doc.maxPrec := by
  unfold Doc.holeNeeds
  split
  · omega
  split
  · split <;> omega
  split
  · split <;> omega
  split
  · split <;> omega
  · omega

end SpliceModel
