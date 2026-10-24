/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Layout

/-!
# The `Doc` IR and its TeX emitter

The tree a formula is rendered as, and the one place parentheses are
decided, live in the shared module `Imprimatur.Layout` (DESIGN §7.1,
docs/verified-extractor.md), so that the paper's model proves things of
them. This file brings them into `Imprimatur`, where the extractor names
them.
-/

namespace Imprimatur

export Layout (Doc Doc.text Doc.node Doc.child Doc.brk Doc.maxPrec Doc.holeNeeds Doc.tex Doc.prec
  Doc.width Doc.Piece Doc.Piece.text Doc.Piece.brk Doc.pieces Doc.render texWidth)

end Imprimatur
