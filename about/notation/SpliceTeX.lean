import SpliceModel
import Imprimatur

/-! # How the paper writes the model of the splicer

The notation module, outside the Lean project (external mode). -/

open SpliceModel

-- Applied variables are written as calls: b(k), render(T).
latex_style applied_variables := call
-- Each metavariable stands for one type, and a variable of that type is
-- written with it.
latex_style categories := strict

-- The splicer's functions.
latex_notation SpliceModel.apply b d => r"\mathsf{apply}_{#b}(#d)"
latex_notation SpliceModel.check b d => r"\mathsf{check}_{#b}(#d)"
latex_notation SpliceModel.accept b d => r"\mathsf{accept}_{#b}(#d)"
latex_notation SpliceModel.regen b p => r"\mathsf{regen}_{#b}(#p)"
latex_notation SpliceModel.diags b p => r"\mathsf{diags}_{#b}(#p)"
latex_notation SpliceModel.rendering b k v => r"\mathsf{rendering}_{#b}(#k, #v)"
latex_notation fill old r => r"\mathsf{fill}(#old, #r)"
latex_notation slots r => r"\mathsf{slots}(#r)"
latex_notation ids r => r"\mathsf{ids}(#r)"
-- A slot's text in a list of slots: l[i] (not l(i), which is an application).
latex_notation lookup i l => r"#l[#i]"
latex_notation outline p => r"\lfloor #p \rfloor"
latex_notation List.map outline d => r"\lfloor #d \rfloor"
latex_notation WF b => r"\mathsf{wf}(#b)"
-- The bundle of a world: the views and the validator are fixed for a paper.
latex_notation entryOf W views problems k S => r"\mathsf{entry}_{#W}(#k, #S)"
  hide views := _ hide problems := _
latex_notation bundleOf W views problems keys => r"\mathsf{bundle}_{#W}(#keys)"
  hide views := _ hide problems := _

-- The bundle's type, and the model's instance of it.
latex_notation Imprimatur.Bundle.find? b k => r"#b[#k]"
latex_notation Imprimatur.Entry.statement e => r"#e.\mathit{statement}"
latex_notation Imprimatur.Entry.verdict e => r"#e.\mathit{verdict}"
latex_notation Imprimatur.Entry.decl e => r"#e.\mathit{decl}"
latex_notation Imprimatur.Decl.kind d => r"#d.\mathit{kind}"
latex_notation Imprimatur.Image.view? i v => r"\mathit{view}_{#v}(#i)"
latex_notation Imprimatur.Image.stmtHash i => r"#i.\mathit{stmtHash}"
latex_notation Imprimatur.Image.sigHash i => r"#i.\mathit{sigHash}"
latex_notation Imprimatur.Image.views i => r"#i.\mathit{views}"
latex_notation Imprimatur.Image.problems i v => r"\mathit{problems}_{#i}(#v)"
latex_notation Imprimatur.Entry σ π => r"\texttt{Entry}(#σ, #π)"
latex_notation Imprimatur.Bundle σ π => r"\texttt{Bundle}(#σ, #π)"
latex_notation Imprimatur.Image τ => r"\texttt{Image}(#τ)"
latex_notation Imprimatur.World τ => r"\texttt{World}(#τ)"
latex_notation Imprimatur.Verdict => r"\texttt{Verdict}"
latex_notation Imprimatur.Decl => r"\texttt{Decl}"
latex_notation Imprimatur.Kind => r"\texttt{Kind}"
latex_notation Imprimatur.Source => r"\texttt{Source}"
latex_notation Imprimatur.Cone => r"\texttt{Cone}"
latex_notation Imprimatur.Hash => r"\mathit{Hash}"
latex_notation Imprimatur.View => r"\mathit{View}"
latex_notation Imprimatur.Key => r"\mathit{Key}"
latex_notation Imprimatur.TeX => r"\mathit{TeX}"
latex_notation SpliceModel.Entry => r"\mathit{Entry}"
latex_notation SpliceModel.Bundle => r"\mathit{Bundle}"
latex_notation SpliceModel.World => r"\mathit{World}"

-- The world: the development as the extractor presents it.
latex_notation Imprimatur.World.Stmt W => r"\mathit{Stmt}_{#W}"
latex_notation Imprimatur.World.kind W k => r"\mathit{kind}_{#W}(#k)"
latex_notation Imprimatur.World.stmt W k => r"\mathit{stmt}_{#W}(#k)"
latex_notation Imprimatur.World.trusted W k => r"\mathit{trusted}_{#W}(#k)"
latex_notation Imprimatur.World.hash W S => r"\mathit{hash}_{#W}(#S)"
latex_notation Imprimatur.World.sig W S => r"\mathit{sig}_{#W}(#S)"
latex_notation Imprimatur.World.render W v S => r"\mathit{render}_{#W}(#v, #S)"
latex_notation Imprimatur.World.Reads W r S => r"\mathit{reads}_{#W}(#r, #S)"

-- Truth: of an image, an entry, a bundle, a piece and a document.
latex_rule_label Imprimatur.Image.Of.mk "Image"
latex_rule_label Imprimatur.Entry.True.mk "Entry"
latex_notation Imprimatur.Image.Of W S i => r"\mathit{image}_{#W}(#S, #i)"
latex_notation Imprimatur.Entry.True W trusted k e => r"#W \models_{#k} #e" hide trusted := _
latex_notation Imprimatur.Bundle.True W trusted b => r"#W \models #b" hide trusted := _
latex_notation Piece.True W p => r"#W \models #p"
latex_notation Doc.True W d => r"#W \models #d"

-- Lists, pairs and strings.
latex_notation List.nil => r"[]"
latex_notation List.cons a l => r"#a \mathbin{::} #l" prec := 67 assoc := right
latex_notation List α => r"\mathsf{List}(#α)"
latex_notation Array α => r"\mathsf{Array}(#α)"
latex_notation Option α => r"\mathsf{Option}(#α)"
latex_notation α × β => r"#α \times #β" prec := 35
latex_notation String => r"\mathit{String}"
latex_notation Bool => r"\mathbb{B}"
latex_notation Bool.true => r"\mathsf{true}"
latex_notation Bool.false => r"\mathsf{false}"
-- Arrays are written as lists.
latex_notation List.toArray l => r"#l"
latex_notation Nat => r"\mathbb{N}"
latex_notation Option.some x => r"#x"
latex_notation Option.getD o t => r"#o \mathbin{\mathsf{else}} #t" prec := 60
latex_notation List.Nodup l => r"#l\ \text{has no repeats}" prec := 50
latex_notation ¬ (a ∈ l) => r"#a \notin #l" prec := 50

-- Documents.
latex_notation Seg.gen s => r"\mathsf{gen}(#s)"
latex_notation Seg.slot i t => r"\mathsf{slot}_{#i}(#t)"
latex_notation Piece.text s => r"\mathsf{text}(#s)"
latex_notation Piece.block k v body => r"\mathsf{block}_{#k}^{#v}(#body)"
latex_notation Piece.check k h => r"\mathsf{checked}_{#k}(#h)"
latex_notation Diag.brokenRef k => r"\mathsf{broken}(#k)"
latex_notation Diag.untrusted k => r"\mathsf{untrusted}(#k)"
latex_notation Diag.missingView k v => r"\mathsf{missing}_{#k}(#v)"
latex_notation Diag.stale k => r"\mathsf{stale}(#k)"
latex_notation Diag.unfaithful k v => r"\mathsf{unfaithful}_{#k}(#v)"
latex_notation Diag.noHash k => r"\mathsf{nohash}(#k)"
latex_notation Diag.drift k => r"\mathsf{drift}(#k)"
latex_notation Piece => r"\mathit{Piece}"
latex_notation Seg => r"\mathit{Seg}"
latex_notation Diag => r"\mathit{Diag}"
latex_notation Doc => r"\mathit{Doc}"
latex_notation Body => r"\mathit{Body}"
latex_notation SlotId => r"\mathit{SlotId}"

-- The metavariables of the grammars.
latex_category Seg => r"\varsigma"
latex_category Piece => "p"
latex_category Diag => "x"
latex_category SpliceModel.Bundle => "b"
latex_category SpliceModel.Entry => "e"
latex_category SpliceModel.World => "W"
latex_category Imprimatur.World => "W"
latex_category Doc => "d"
latex_category Imprimatur.Key => "k"
latex_category Imprimatur.View => "v"
latex_category Imprimatur.Hash => "h"
latex_category Body => "r"
latex_category Imprimatur.World.Stmt => "S"

-- The results, by title.
latex_entry "Locality" => SpliceModel.apply_outline
latex_entry "Idempotence" => SpliceModel.apply_apply
latex_entry "Fixed point" => SpliceModel.not_stale_after_apply
latex_entry "Slot preservation" => SpliceModel.slot_kept
latex_entry "Generated mathematics" => SpliceModel.block_true
latex_entry "Attested prose" => SpliceModel.check_true
latex_entry "The typeset mathematics is true" => SpliceModel.document_true
latex_entry "Attested prose faces its statement" => SpliceModel.attested
latex_entry "The bundle of a world is true" => SpliceModel.bundleOf_true
latex_entry "The hash names the statement" => Imprimatur.Image.Of.stmt_eq
latex_entry "A view shows the statement" => Imprimatur.Bundle.True.view
