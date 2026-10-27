/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel
import Stlc

/-! # What the paper reads: the splicer's model, and the example -/

namespace About

/-- The requests the five blocks of Figure 1 make: each key, as the document
writes it, with the view its block shows. -/
def figureRequests : List (Imprimatur.Key × List Imprimatur.View) :=
  [("Stlc.Tm", ["grammar|display"]), ("Stlc.IsValue", ["rules"]), ("Stlc.Step", ["rules"]),
    ("Values are final", ["prose"]), ("Stlc.values_final", ["lean"])]

open Imprimatur.Layout in
/-- The sentence of *Values are final*, as the prose view says it: a value,
bound in the predicate its hidden premise puts it in, a term, and a
conclusion, each a formula of TeX. -/
def valuesFinalSentence : Prose (List Char) := .statement
  { vars := [{ names := ["V".toList], kind := .ofType "\\mathit{Val}".toList },
      { names := ["M".toList], kind := .ofType "\\mathit{Term}".toList }],
    hyps := [], concl := .formula "\\neg (V \\longrightarrow M)".toList }

/-- The TeX of the block of *Values are final*: its prose rendering, which
the paper's view of the block checks it still is. -/
def valuesFinalTeX : String :=
  "\\LeanProse{Let $V \\in \\mathit{Val}$ and $M \\in \\mathit{Term}$. Then $\\neg (V \\longrightarrow M)$.}"

open Imprimatur.Layout in
/-- **Values are final, taken apart.** The prose parser takes the TeX of
the block apart into its sentence: the layout of the sentence is that TeX,
which the kernel computes, and the parser undoes the layout. -/
theorem valuesFinal_parses : proseSentence valuesFinalTeX.toList = some valuesFinalSentence := by
  have hplain : valuesFinalSentence.Plain := by
    simp only [valuesFinalSentence, Prose.Plain, VarGroup.Plain, PlainName, Plain, Concl.Plain,
      List.mem_cons, forall_eq_or_imp, List.not_mem_nil,
      false_implies, implies_true, and_true, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    decide
  have hlayout : proseLayout valuesFinalSentence = valuesFinalTeX := by decide
  rw [← hlayout]
  exact SpliceModel.proseSentence_proseLayout hplain

end About
