/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel
import Stlc

/-! # What the paper reads: the splicer's model, and the example -/

namespace About

/-- The requests the four blocks of Figure 1 make: each key, as the document
writes it, with the view its block shows. -/
def figureRequests : List (Imprimatur.Key × List Imprimatur.View) :=
  [("Stlc.Tm", ["grammar|display"]), ("Stlc.Step", ["rules"]),
    ("Values are final", ["prose"]), ("Stlc.values_final", ["lean"])]

end About
