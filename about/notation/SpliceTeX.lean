import SpliceModel
import Imprimatur.Layout
import Stlc
import Imprimatur

/-! # How the paper writes the model of the splicer

The notation module, outside the Lean project (external mode). -/

open SpliceModel Imprimatur.Layout

-- Applied variables are written as calls: b(k), render(T).
latex_style applied_variables := call
-- Each metavariable stands for one type, and a variable of that type is
-- written with it.
latex_style categories := strict
-- List literals are written [a, b], not a :: b :: [].
latex_style lists := literal

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
latex_notation SpliceModel.Doc.True W d => r"#W \models #d"

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
latex_notation SpliceModel.Doc => r"\mathit{Doc}"
latex_notation Body => r"\mathit{Body}"
latex_notation SlotId => r"\mathit{SlotId}"

-- The metavariables of the grammars.
latex_category Seg => r"\varsigma"
latex_category Piece => "p"
latex_category Diag => r"\delta"
latex_category SpliceModel.Bundle => "b"
latex_category SpliceModel.Entry => "e"
latex_category SpliceModel.World => "W"
latex_category Imprimatur.World => "W"
latex_category SpliceModel.Doc => "d"
latex_category Imprimatur.Key => "k"
latex_category Imprimatur.View => "v"
latex_category Imprimatur.Hash => "h"
latex_category Body => "r"
latex_category Imprimatur.World.Stmt => "S"

-- Two views read: how statements and renderings come apart.
latex_notation Anatomy W => r"\texttt{Anatomy}(#W)"
latex_notation Anatomy.Part A => r"\mathit{Part}_{#A}"
latex_notation Anatomy.gather A S => r"\mathit{gather}_{#A}(#S)"
latex_notation Anatomy.ctors A S => r"\mathit{ctors}_{#A}(#S)"
latex_notation Anatomy.print A q => r"\mathit{print}_{#A}(#q)"
latex_notation Prose.map (Anatomy.print A) u => r"\mathit{print}^{*}_{#A}(#u)"
latex_notation Anatomy.PrintsProse A S r => r"#r = \mathit{print}^{\mathsf{prose}}_{#A}(#S)" prec := 50
latex_notation Anatomy.Faithful A S => r"\mathit{faithful}_{#A}(#S)"
latex_notation Rule.map (Anatomy.print A) q => r"\mathit{print}^{*}_{#A}(#q)"
latex_notation List.map (Rule.map (Anatomy.print A)) qs => r"\mathit{print}^{*}_{#A}(#qs)"
latex_notation Anatomy.PrintsRules A S r => r"#r = \mathit{print}^{\mathsf{rules}}_{#A}(#S)" prec := 50
latex_notation Anatomy.FaithfulRules A S => r"\mathit{faithful}^{\mathsf{rules}}_{#A}(#S)"
latex_notation Anatomy.ReadsPart A f q => r"#f \rightsquigarrow_{#A} #q" prec := 50
latex_notation Anatomy.ReadsAll A fs qs => r"#fs \rightsquigarrow^{*}_{#A} #qs" prec := 50
latex_notation Anatomy.ReadsKind A t u => r"#t \rightsquigarrow^{\mathsf{kind}}_{#A} #u" prec := 50
latex_notation Anatomy.ReadsGroup A g u => r"#g \rightsquigarrow^{\mathsf{group}}_{#A} #u" prec := 50
latex_notation Anatomy.ReadsGroups A gs us => r"#gs \rightsquigarrow^{\mathsf{groups}}_{#A} #us" prec := 50
latex_notation Anatomy.ReadsHyp A hy u => r"#hy \rightsquigarrow^{\mathsf{hyp}}_{#A} #u" prec := 50
latex_notation Anatomy.ReadsHyps A hs us => r"#hs \rightsquigarrow^{\mathsf{hyps}}_{#A} #us" prec := 50
latex_notation Anatomy.ReadsConcl A c u => r"#c \rightsquigarrow^{\mathsf{then}}_{#A} #u" prec := 50
latex_notation Anatomy.ReadsProse A t u => r"#t \rightsquigarrow^{\mathsf{prose}}_{#A} #u" prec := 50
latex_notation Anatomy.ReadsRule A f q => r"#f \rightsquigarrow^{\mathsf{rule}}_{#A} #q" prec := 50
latex_notation Anatomy.ReadsRules A fs qs => r"#fs \rightsquigarrow^{\mathsf{rules}}_{#A} #qs" prec := 50
latex_notation Anatomy.Prose A r S => r"\mathit{prose}_{#A}(#r, #S)"
latex_notation Anatomy.Rules A r S => r"\mathit{rules}_{#A}(#r, #S)"
latex_notation Anatomy.Sound A => r"\mathsf{sound}(#A)"
latex_category Anatomy => r"\mathcal{A}"
latex_rule_label Anatomy.Sound.mk "Sound"
latex_display "Anatomies" := [Anatomy]

-- What the prose view says (Imprimatur.Layout), and how it is laid out.
latex_notation VarKind α => r"\texttt{Range}(#α)"
latex_notation VarKind.ofType t => r"{\in}\, #t"
latex_notation VarKind.type => r"\text{a type}"
latex_notation VarKind.prop => r"\text{a proposition}"
latex_notation VarGroup α => r"\texttt{Group}(#α)"
latex_notation VarGroup.mk names kind => r"\langle #names, #kind\rangle"
latex_notation VarGroup.names g => r"#g.\mathit{names}"
latex_notation VarGroup.kind g => r"#g.\mathit{kind}"
latex_notation Hyp α => r"\texttt{Hyp}(#α)"
latex_notation Hyp.mk l f => r"\langle #l, #f\rangle"
latex_notation Hyp.label hy => r"#hy.\mathit{label}"
latex_notation Hyp.formula hy => r"#hy.\mathit{formula}"
latex_notation Concl α => r"\texttt{Concl}(#α)"
latex_notation Concl.formula f => r"\mathsf{just}(#f)"
latex_notation Concl.conjuncts fs => r"\mathsf{all}(#fs)"
latex_notation Concl.iff lhs rhs => r"\mathsf{iff}(#lhs, #rhs)"
latex_notation Concl.exists_ w c => r"\mathsf{some}(#w, #c)"
latex_notation Statement α => r"\texttt{Statement}(#α)"
latex_notation Statement.mk gs hs c => r"\langle #gs, #hs, #c\rangle"
latex_notation Statement.vars s => r"#s.\mathit{vars}"
latex_notation Statement.hyps s => r"#s.\mathit{hyps}"
latex_notation Statement.concl s => r"#s.\mathit{concl}"
latex_notation Prose α => r"\texttt{Prose}(#α)"
latex_notation Prose.define f => r"\mathsf{define}(#f)"
latex_notation Prose.statement s => r"\mathsf{statement}(#s)"
latex_notation Prose.Plain pr => r"\mathsf{plain}(#pr)"
latex_notation kindParts t => r"\mathsf{parts}(#t)"
latex_notation groupParts g => r"\mathsf{parts}(#g)"
latex_notation Concl.parts c => r"\mathsf{parts}(#c)"
latex_notation Prose.parts pr => r"\mathsf{parts}(#pr)"
latex_display "What the prose view says" := [VarKind, VarGroup, Hyp, Concl, Statement, Prose]

-- What the rules view says (Imprimatur.Layout), and how it is laid out.
latex_notation Mark => r"\texttt{Mark}"
latex_notation Mark.name m => r"#m.\mathit{name}"
latex_notation Mark.key m => r"#m.\mathit{key}"
latex_notation Mark.Plain m => r"\mathsf{plain}(#m)"
latex_notation Rule α => r"\texttt{Rule}(#α)"
latex_notation Rule.mark r => r"#r.\mathit{mark}"
latex_notation Rule.label r => r"#r.\mathit{label}"
latex_notation Rule.premises r => r"#r.\mathit{premises}"
latex_notation Rule.concl r => r"#r.\mathit{concl}"
latex_notation Rule.mk mark label ps c => r"\langle #mark, #label, #ps, #c\rangle"
latex_notation Rule.Plain r => r"\mathsf{plain}(#r)"
latex_notation Rule.parts r => r"\mathsf{parts}(#r)"
latex_notation Item α => r"\texttt{Item}(#α)"
latex_notation Item.rule r => r"\mathsf{rule}(#r)"
latex_notation Item.missing n => r"\mathsf{missing}(#n)"
latex_notation ruleItems rs => r"\mathsf{items}(#rs)"
latex_notation Line => r"\mathit{Line}"
latex_notation Line.blank => r"\text{``''}"
latex_notation Line.beginK => r"\text{``\textbackslash{}begin\{mathpar\}''}"
latex_notation Line.endK => r"\text{``\textbackslash{}end\{mathpar\}''}"
latex_notation Line.andK => r"\text{``\textbackslash{}and''}"
latex_notation Line.openK => r"\text{``\ \ \{''}"
latex_notation Line.openEmpty => r"\text{``\ \ \{ \}''}"
latex_notation Line.closeK => r"\text{``\ \ \}''}"
latex_notation Line.header label => r"\mathsf{header}(#label)"
latex_notation Line.mark m label => r"\mathsf{mark}(#m, #label)"
latex_notation Line.line text => r"\mathsf{premise}(#text)"
latex_notation Line.concl f => r"\mathsf{concl}(#f)"
latex_notation Line.comment n => r"\mathsf{comment}(#n)"
latex_notation inferOpen => r"\mathsf{inferOpen}"
latex_notation indent => r"\mathsf{indent}"
latex_notation conclOpen => r"\mathsf{conclOpen}"
latex_notation conclClose => r"\mathsf{conclClose}"
latex_notation lineBreak => r"\mathsf{lineBreak}"
latex_notation lineText t => r"\mathsf{lineText}(#t)"
latex_notation joinLines ls => r"\mathsf{joinLines}(#ls)"
latex_notation premiseLines ps => r"\mathsf{premiseLines}(#ps)"
latex_notation bodyLines ps c => r"\mathsf{bodyLines}(#ps, #c)"
latex_notation markLines o label => r"\mathsf{markLines}(#o, #label)"
latex_notation ruleLines r => r"\mathsf{ruleLines}(#r)"
latex_notation itemLines i => r"\mathsf{itemLines}(#i)"
latex_notation trimAnd ls => r"\mathsf{trimAnd}(#ls)"
latex_notation figureLines items => r"\mathsf{figureLines}(#items)"
latex_notation figureChars items => r"\mathsf{figureChars}(#items)"
latex_notation figureLayout items => r"\mathsf{figure}(#items)"
latex_notation lines cs => r"\mathsf{lines}(#cs)"
latex_notation lexLines ls => r"\mathsf{lex}(#ls)"
latex_notation dropPrefix pre l => r"\mathsf{dropPrefix}(#pre, #l)"
latex_notation dropSuffix suf l => r"\mathsf{dropSuffix}(#suf, #l)"
latex_notation parsePremises ps ls => r"\mathsf{premises}_{#ps}(#ls)"
latex_notation premiseNext ps p ls => r"\mathsf{next}_{#ps}(#p, #ls)"
latex_notation unbreak ps o ls => r"\mathsf{unbreak}_{#ps}(#o, #ls)"
latex_notation withPremises mark label o => r"\mathsf{withPremises}(#mark, #label, #o)"
latex_notation parseBody mark label ls => r"\mathsf{body}(#mark, #label, #ls)"
latex_notation parseRule ls => r"\mathsf{parseRule}(#ls)"
latex_notation ruleOf o => r"\mathsf{ruleOf}(#o)"
latex_notation parseChunk ls => r"\mathsf{chunk}(#ls)"
latex_notation consRule o os => r"\mathsf{consRule}(#o, #os)"
latex_notation parseChunks chs => r"\mathsf{chunks}(#chs)"
latex_notation chunks cur ls => r"\mathsf{split}_{#cur}(#ls)"
latex_notation bodyOf ls => r"\mathsf{bodyOf}(#ls)"
latex_notation rulesOf o => r"\mathsf{rulesOf}(#o)"
latex_notation figureOf ls => r"\mathsf{figureOf}(#ls)"
latex_notation ofLines o => r"\mathsf{ofLines}(#o)"
latex_notation figure cs => r"\mathsf{rules}(#cs)"
latex_display "What the rules view says" := [Mark, Rule, Item]
latex_display "Lines" := [Line]
latex_display "The rules layout" := [lineText, joinLines, premiseLines, bodyLines, markLines, ruleLines,
  itemLines, trimAnd, figureLines, figureChars, figureLayout]
latex_display "The rules parser" := [parsePremises, premiseNext, unbreak, withPremises, parseBody,
  parseRule, ruleOf, parseChunk, consRule, parseChunks, chunks, bodyOf, rulesOf, figureOf, ofLines, figure]
latex_display "Printing rules" := [Anatomy.PrintsRules, Anatomy.FaithfulRules]
-- Tokens: keywords print as their text.
latex_notation Kw => r"\mathit{Kw}"
latex_notation Tok => r"\mathit{Tok}"
latex_notation Tok.kw word => r"#word"
latex_notation Tok.formula f => r"\text{\$}#f\text{\$}"
latex_notation Tok.label n => r"\mathsf{label}(#n)"
latex_notation Tok.item ds => r"\mathsf{item}(#ds)"
latex_notation Kw.prose => r"\text{``\textbackslash{}LeanProse\{''}"
latex_notation Kw.weDefine => r"\text{``We define ''}"
latex_notation Kw.letK => r"\text{``Let ''}"
latex_notation Kw.assumeK => r"\text{``Assume ''}"
latex_notation Kw.thenK => r"\text{``Then ''}"
latex_notation Kw.comma => r"\text{``, ''}"
latex_notation Kw.andK => r"\text{`` and ''}"
latex_notation Kw.beAType => r"\text{`` be a type''}"
latex_notation Kw.beTypes => r"\text{`` be types''}"
latex_notation Kw.beAProp => r"\text{`` be a proposition''}"
latex_notation Kw.beProps => r"\text{`` be propositions''}"
latex_notation Kw.dotSpace => r"\text{``. ''}"
latex_notation Kw.endK => r"\text{``.\}''}"
latex_notation Kw.thereIs => r"\text{``there is ''}"
latex_notation Kw.suchThat => r"\text{`` such that ''}"
latex_notation Kw.iffK => r"\text{`` if and only if ''}"
latex_notation kwText word => r"\mathsf{spelling}(#word)"
latex_notation tokChars t => r"\mathsf{text}(#t)"
latex_notation printToks ts => r"\mathsf{text}(#ts)"
latex_notation labelOpen => r"\mathsf{labelOpen}"
latex_notation decimal n => r"\mathsf{decimal}(#n)"
latex_notation andRestToks ys => r"\mathsf{rest}(#ys)"
latex_notation andToks ys => r"\mathsf{list}(#ys)"
latex_notation joinComma ns => r"\mathsf{names}(#ns)"
latex_notation inSep => r"\mathsf{inSep}"
latex_notation commaSep => r"\mathsf{commaSep}"
latex_notation groupToks g => r"\mathsf{group}(#g)"
latex_notation hypToks hy => r"\mathsf{hyp}(#hy)"
latex_notation numbered i fs => r"\mathsf{numbered}_{#i}(#fs)"
latex_notation conclToks c => r"\mathsf{then}(#c)"
latex_notation sentencesToks ss => r"\mathsf{sentences}(#ss)"
latex_notation statementToks s => r"\mathsf{statement}(#s)"
latex_notation proseToks pr => r"\mathsf{toks}(#pr)"
latex_notation proseChars pr => r"\mathsf{chars}(#pr)"
latex_notation letToks gs => r"\mathsf{let}(#gs)"
latex_notation assumeToks hs => r"\mathsf{assume}(#hs)"
latex_notation thenKw ss => r"\mathsf{thenKw}(#ss)"
latex_notation thenToks ss c => r"\mathsf{then}(#ss, #c)"
latex_notation proseLayout pr => r"\mathsf{layout}(#pr)"
latex_notation lex cs => r"\mathsf{lex}(#cs)"
latex_notation splitFirst sep cs => r"\mathsf{splitFirst}_{#sep}(#cs)"
latex_notation splitAll sep cs => r"\mathsf{splitAll}_{#sep}(#cs)"
latex_notation parseGroups acc ts => r"\mathsf{groups}_{#acc}(#ts)"
latex_notation ofTypeGroup acc ts o => r"\mathsf{ofType}_{#acc}(#ts, #o)"
latex_notation afterGroup g acc ts => r"\mathsf{afterGroup}_{#acc}(#g, #ts)"
latex_notation parseHyps acc ts => r"\mathsf{hyps}_{#acc}(#ts)"
latex_notation parseItems acc ts => r"\mathsf{items}_{#acc}(#ts)"
latex_notation afterSuch w o => r"\mathsf{afterSuch}(#w, #o)"
latex_notation parseConcl ts => r"\mathsf{concl}(#ts)"
latex_notation finishWith gs hs o => r"\mathsf{finishWith}(#gs, #hs, #o)"
latex_notation finish gs hs ts => r"\mathsf{finish}(#gs, #hs, #ts)"
latex_notation afterAssume gs o => r"\mathsf{afterAssume}(#gs, #o)"
latex_notation afterLet o => r"\mathsf{afterLet}(#o)"
latex_notation parseStatement ts => r"\mathsf{statement}(#ts)"
latex_notation parseProse ts => r"\mathsf{parse}(#ts)"
latex_notation proseSentence cs => r"\mathsf{sentence}(#cs)"
latex_notation ite c a b => r"\mathsf{if}\ #c\ \mathsf{then}\ #a\ \mathsf{else}\ #b" prec := 10
latex_notation a ++ b => r"#a \mathbin{+\!\!+} #b" prec := 65 assoc := left
latex_notation Option.none => r"\mathsf{none}"
latex_notation String.ofList cs => r"#cs"
latex_notation String.toList s => r"#s"
latex_notation Char => r"\mathit{Char}"
latex_display "The prose layout" := [andRestToks, andToks, joinComma, groupToks, hypToks, numbered,
  conclToks, letToks, assumeToks, thenKw, thenToks, sentencesToks, statementToks, proseToks, tokChars,
  printToks, proseLayout]
latex_display "The prose parser" := [parseGroups, ofTypeGroup, afterGroup, parseHyps, parseItems, afterSuch, parseConcl,
  finishWith, finish, afterAssume, afterLet, parseStatement, parseProse, proseSentence]
latex_display "Printing prose" := [Anatomy.PrintsProse, Anatomy.Faithful]
latex_group "Reading back" := [Anatomy.ReadsAll.nil, Anatomy.ReadsAll.cons, Anatomy.ReadsKind.ofType,
  Anatomy.ReadsKind.type, Anatomy.ReadsKind.prop, Anatomy.ReadsGroup.mk, Anatomy.ReadsGroups.nil,
  Anatomy.ReadsGroups.cons, Anatomy.ReadsHyp.mk, Anatomy.ReadsHyps.nil, Anatomy.ReadsHyps.cons,
  Anatomy.ReadsConcl.formula, Anatomy.ReadsConcl.conjuncts, Anatomy.ReadsConcl.iff,
  Anatomy.ReadsConcl.exists_, Anatomy.ReadsProse.define, Anatomy.ReadsProse.statement,
  Anatomy.ReadsRule.mk, Anatomy.ReadsRules.nil, Anatomy.ReadsRules.cons]
latex_display "Reading two views" := [Anatomy.Prose, Anatomy.Rules]

-- Reading formulas back (Imprimatur.ReadBack), and what is proved of it.
latex_notation Imprimatur.Validate.SortAlgebra => r"\texttt{Sorts}"
latex_notation Imprimatur.Validate.Grammar => r"\texttt{Grammar}"
latex_notation Imprimatur.Validate.Reading => r"\texttt{Reading}"
latex_notation Imprimatur.Validate.Reading.matches e r => r"\mathsf{matches}(#e, #r)"
latex_notation Matches e r => r"#e \succcurlyeq #r" prec := 50
latex_notation Array.size xs => r"|#xs|"
latex_notation Imprimatur.Validate.readBackWith A g ts s => r"\mathsf{readBack}_{#A}(#g, #ts, #s)"
latex_notation Prod.fst (Imprimatur.Validate.readBackWith A g ts s) => r"\mathsf{readings}_{#A}(#g, #ts, #s)"
latex_notation Imprimatur.Validate.Flags.any (Prod.snd (Imprimatur.Validate.readBackWith A g ts s)) => r"\mathsf{flagged}_{#A}(#g, #ts, #s)"
latex_notation Exp A g ts s p excl ch i j r σ => r"#ts[#i, #j) \rightsquigarrow^{#g}_{#A}(#s, #p, #excl, #ch)\ #r : #σ" prec := 50
latex_notation Imprimatur.Validate.Chain => r"\texttt{Chain}"
latex_notation Imprimatur.Validate.Grammar.chain0 g => r"\mathsf{top}_{#g}"
latex_notation Validated => r"\texttt{Validated}"
latex_category Validated => "X"
latex_notation Validated.base X => r"W^{\circ}_{#X}"
latex_notation Validated.Part X => r"\mathit{Part}_{#X}"
latex_notation Validated.world X => r"W_{#X}"
latex_notation Validated.anatomy X => r"\mathcal{A}_{#X}"
latex_notation Validated.gather X S => r"\mathit{gather}_{#X}(#S)"
latex_notation Validated.ctors X S => r"\mathit{ctors}_{#X}(#S)"
latex_notation Validated.print X q => r"\mathit{print}_{#X}(#q)"
latex_notation Prose.map (Validated.print X) u => r"\mathit{print}^{*}_{#X}(#u)"
latex_notation Rule.map (Validated.print X) q => r"\mathit{print}^{*}_{#X}(#q)"
latex_category Imprimatur.Validate.SortAlgebra => r"\mathcal{S}"
latex_category Imprimatur.Validate.Grammar => "G"

-- The names a bundle uses, all strings.
latex_display "Names" := [Imprimatur.Key, Imprimatur.View, Imprimatur.TeX, Imprimatur.Hash]

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
latex_entry "The prose parser undoes the layout" => SpliceModel.proseSentence_proseLayout
latex_entry "The figure parser undoes the layout" => SpliceModel.figure_figureLayout
latex_entry "The parser is sound" => SpliceModel.readBack_sound
latex_entry "The parser is complete" => SpliceModel.readBack_complete
latex_entry "A validated formula reads only as what it was rendered from" => SpliceModel.pollack
latex_entry "The validator's anatomy is sound" => SpliceModel.Validated.sound
latex_entry "A prose rendering shows its statement" => SpliceModel.Anatomy.Sound.proseShows
latex_entry "A rules rendering shows its predicate" => SpliceModel.Anatomy.Sound.rulesShow
latex_entry "Prose shows the statement" => SpliceModel.prose_true
latex_entry "Rules show the predicate" => SpliceModel.rules_true
