import SpliceModel
import BundleTypes
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
latex_notation apply b d => r"\mathsf{apply}_{#b}(#d)"
latex_notation check b d => r"\mathsf{check}_{#b}(#d)"
latex_notation accept b d => r"\mathsf{accept}_{#b}(#d)"
latex_notation regen b p => r"\mathsf{regen}_{#b}(#p)"
latex_notation diags b p => r"\mathsf{diags}_{#b}(#p)"
latex_notation fill old r => r"\mathsf{fill}(#old, #r)"
latex_notation slots r => r"\mathsf{slots}(#r)"
latex_notation ids r => r"\mathsf{ids}(#r)"
-- A slot's text in a list of slots: l[i] (not l(i), which is an application).
latex_notation lookup i l => r"#l[#i]"
latex_notation outline p => r"\lfloor #p \rfloor"
latex_notation List.map outline d => r"\lfloor #d \rfloor"
latex_notation WF b => r"\mathsf{wf}(#b)"
-- The bundle exported from an environment; how statements are rendered and
-- hashed is fixed for a paper, so it is not shown.
latex_notation extract ren hsh E => r"\mathsf{export}(#E)" hide ren := _ hide hsh := _

-- Environments and entries.
latex_notation Env.stmt E k => r"\mathit{stmt}_{#E}(#k)"
latex_notation Env.trusted E k = true => r"\mathit{trusted}_{#E}(#k)"
latex_notation Entry.render e => r"#e.\mathit{render}"
latex_notation Option.some x => r"#x"
latex_notation List.Nodup l => r"#l\ \text{has no repeats}" prec := 50
latex_notation Env S => r"\mathit{Env}(#S)"
latex_notation Option.getD o t => r"#o \mathbin{\mathsf{else}} #t" prec := 60

-- Lists, pairs and strings.
latex_notation List.nil => r"[]"
latex_notation List.cons a l => r"#a \mathbin{::} #l" prec := 67 assoc := right
latex_notation List α => r"\mathsf{List}(#α)"
latex_notation α × β => r"#α \times #β" prec := 35
latex_notation String => r"\mathit{String}"
latex_notation ¬ (a ∈ l) => r"#a \notin #l" prec := 50

-- Documents.
latex_notation Seg.gen s => r"\mathsf{gen}(#s)"
latex_notation Seg.slot i t => r"\mathsf{slot}_{#i}(#t)"
latex_notation Piece.text s => r"\mathsf{text}(#s)"
latex_notation Piece.block k body => r"\mathsf{block}_{#k}(#body)"
latex_notation Piece.check k h => r"\mathsf{checked}_{#k}(#h)"
latex_notation Diag.brokenRef k => r"\mathsf{broken}(#k)"
latex_notation Diag.untrusted k => r"\mathsf{untrusted}(#k)"
latex_notation Diag.stale k => r"\mathsf{stale}(#k)"
latex_notation Diag.drift k => r"\mathsf{drift}(#k)"
latex_notation Piece => r"\mathit{Piece}"
latex_notation Seg => r"\mathit{Seg}"
latex_notation Diag => r"\mathit{Diag}"
latex_notation Bundle => r"\mathit{Bundle}"
latex_notation Doc => r"\mathit{Doc}"
latex_notation Body => r"\mathit{Body}"
latex_notation Key => r"\mathit{Key}"
latex_notation SlotId => r"\mathit{SlotId}"

-- The splicer's own types for a bundle (Section 3), in typewriter, apart
-- from the model's.
latex_notation Splice.Bundle => r"\texttt{Bundle}"
latex_notation Splice.Entry => r"\texttt{Entry}"
latex_notation Splice.SourceLoc => r"\texttt{SourceLoc}"
latex_notation Array α => r"\mathsf{Array}(#α)"
latex_notation Option α => r"\mathsf{Option}(#α)"
latex_notation Bool => r"\mathbb{B}"
latex_notation Nat => r"\mathbb{N}"

-- The metavariables of the grammars.
latex_category Seg => r"\sigma"
latex_category Piece => "p"
latex_category Diag => "x"
latex_category Bundle => "b"
latex_category Doc => "d"
latex_category Key => "k"

-- The results, by title.
latex_entry "Locality" => SpliceModel.apply_outline
latex_entry "Idempotence" => SpliceModel.apply_apply
latex_entry "Fixed point" => SpliceModel.not_stale_after_apply
latex_entry "Slot preservation" => SpliceModel.slot_kept
latex_entry "Soundness for blocks" => SpliceModel.block_sound
latex_entry "Soundness for checked prose" => SpliceModel.check_sound
latex_entry "Attested prose" => SpliceModel.attested
