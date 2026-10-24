/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Layout
import SpliceModel.Prose

/-!
# The rules figure reads back

The extractor's `rules` view lays a figure out line by line
(`Imprimatur.Layout.figureLayout`), and its parser (`figure`) reads the
lines back and the rules off them. Here the parser is shown to undo the
layout for every plain figure: one whose labels, formulas, macros and keys
hold no newline, whose macros hold no `{` and whose keys no `}`
(`figure_figureLayout`). The definitions are the extractor's own, from the
shared module; only the theorems live here.
-/

namespace SpliceModel

open Imprimatur.Layout

/-! ## Lines -/

theorem linesGo_append {x : List Char} (hx : '\n' ∉ x) : ∀ (rest cur : List Char),
    linesGo (x ++ '\n' :: rest) cur = (cur.reverse ++ x) :: linesGo rest [] := by
  induction x with
  | nil => intro rest cur; simp [linesGo]
  | cons c x ih =>
    intro rest cur
    have hc : c ≠ '\n' := fun h => hx (h ▸ List.mem_cons_self ..)
    simp only [List.cons_append, linesGo, hc, ↓reduceIte]
    rw [ih (fun h => hx (List.mem_cons_of_mem _ h)) rest (c :: cur)]
    simp

theorem linesGo_last {x : List Char} (hx : '\n' ∉ x) : ∀ (cur : List Char),
    linesGo x cur = [cur.reverse ++ x] := by
  induction x with
  | nil => intro cur; simp [linesGo]
  | cons c x ih =>
    intro cur
    have hc : c ≠ '\n' := fun h => hx (h ▸ List.mem_cons_self ..)
    simp only [linesGo, hc, ↓reduceIte]
    rw [ih (fun h => hx (List.mem_cons_of_mem _ h)) (c :: cur)]
    simp

/-- Lines with no newline in them come apart again. -/
theorem lines_joinLines : ∀ {xs : List (List Char)}, xs ≠ [] → (∀ x ∈ xs, '\n' ∉ x) →
    lines (joinLines xs) = xs
  | [], h, _ => absurd rfl h
  | [x], _, h => by
    simp only [joinLines, lines]
    rw [linesGo_last (h x (by simp))]
    simp
  | x :: x' :: xs, _, h => by
    simp only [joinLines, lines]
    rw [linesGo_append (h x (by simp))]
    have ih := lines_joinLines (xs := x' :: xs) (by simp) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [lines] at ih
    rw [ih]
    simp

/-! ## Prefixes and suffixes -/

theorem dropPrefix_append (pre l : List Char) : dropPrefix pre (pre ++ l) = some l := by
  simp [dropPrefix, isPrefixOf_self_append]

theorem dropSuffix_append (suf l : List Char) : dropSuffix suf (l ++ suf) = some l := by
  simp [dropSuffix, List.reverse_append, dropPrefix_append]

theorem drop_append_cons : ∀ (f : List Char) (d : Char) (s : List Char),
    (f ++ d :: s).drop (f.length + 1) = s
  | [], _, _ => rfl
  | c :: f, d, s => by simp [drop_append_cons f d s]

theorem getLast?_append_singleton (l : List Char) (c : Char) : (l ++ [c]).getLast? = some c := by
  simp

/-! ## The lexer -/

/-- A line the lexer reads back: no newline in its text, no `{` in a macro's
name and no `}` in a key; no comment. -/
def LineWF : Line → Prop
  | .header label => '\n' ∉ label
  | .mark m label => m.Plain ∧ '\n' ∉ label
  | .line text => '\n' ∉ text
  | .concl f => '\n' ∉ f
  | .comment _ => False
  | _ => True

theorem beginWord_eq : "begin{mathpar}".toList = ['b', 'e', 'g', 'i', 'n', '{', 'm', 'a', 't', 'h', 'p', 'a', 'r', '}'] := by
  decide
theorem endWord_eq : "end{mathpar}".toList = ['e', 'n', 'd', '{', 'm', 'a', 't', 'h', 'p', 'a', 'r', '}'] := by
  decide
theorem andWord_eq : "and".toList = ['a', 'n', 'd'] := by decide
theorem inferWord_eq : "inferrule[".toList = ['i', 'n', 'f', 'e', 'r', 'r', 'u', 'l', 'e', '['] := by decide
theorem inferOpen_eq : inferOpen = '\\' :: "inferrule[".toList := by decide
theorem indent_eq : indent = [' ', ' ', ' ', ' '] := by decide
theorem conclOpen_eq : conclOpen = [' ', ' ', '{', ' '] := by decide
theorem conclClose_eq : conclClose = [' ', '}'] := by decide
theorem braces_eq : "}{".toList = ['}', '{'] := by decide

/-- A line that ends in `%` is no keyword line. -/
theorem backslashLine_mark {l : List Char} (h : l.getLast? = some '%') :
    backslashLine l = markAfter (some l) := by
  have h1 : l ≠ "begin{mathpar}".toList := fun e => by rw [e, beginWord_eq] at h; simp at h
  have h2 : l ≠ "end{mathpar}".toList := fun e => by rw [e, endWord_eq] at h; simp at h
  have h3 : l ≠ "and".toList := fun e => by rw [e, andWord_eq] at h; simp at h
  rw [backslashLine, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h]

/-- A line that ends in `]` after `\inferrule[` is a header. -/
theorem backslashLine_header (label : List Char) :
    backslashLine ("inferrule[".toList ++ (label ++ [']'])) = some (.header label) := by
  have h1 : "inferrule[".toList ++ (label ++ [']']) ≠ "begin{mathpar}".toList := by
    rw [inferWord_eq, beginWord_eq]; simp
  have h2 : "inferrule[".toList ++ (label ++ [']']) ≠ "end{mathpar}".toList := by
    rw [inferWord_eq, endWord_eq]; simp
  have h3 : "inferrule[".toList ++ (label ++ [']']) ≠ "and".toList := by
    rw [inferWord_eq, andWord_eq]; simp
  have h4 : ¬ ("inferrule[".toList ++ (label ++ [']'])).getLast? = some '%' := by
    rw [← List.append_assoc, getLast?_append_singleton]; decide
  rw [backslashLine, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4,
    dropPrefix_append, headerOf, dropSuffix_append, Option.map_some]

/-- The conclusion's line, after `  {`. -/
theorem braceLine_concl : ∀ (f : List Char), braceLine (' ' :: (f ++ conclClose)) = some (.concl f)
  | [] => by rw [conclClose_eq]; rfl
  | c :: f => by
    have h : dropSuffix conclClose (c :: (f ++ conclClose)) = some (c :: f) :=
      dropSuffix_append conclClose (c :: f)
    rw [conclClose_eq] at h
    simp [braceLine, conclClose_eq, h]

theorem lineOf_lineText : ∀ {t : Line}, LineWF t → lineOf (lineText t) = some t
  | .blank, _ => rfl
  | .beginK, _ => rfl
  | .endK, _ => rfl
  | .andK, _ => rfl
  | .openK, _ => rfl
  | .openEmpty, _ => rfl
  | .closeK, _ => rfl
  | .header label, _ => by
    rw [lineText, inferOpen_eq, List.cons_append]
    simp only [lineOf]
    exact backslashLine_header label
  | .mark m label, ⟨hm, _⟩ => by
    obtain ⟨name, key⟩ := m
    obtain ⟨_, hname, _, hkey⟩ := hm
    simp only [lineText, lineOf]
    have hl : (name ++ '{' :: (key ++ '}' :: '{' :: (label ++ ['}', '%']))).getLast? = some '%' := by
      rw [show name ++ '{' :: (key ++ '}' :: '{' :: (label ++ ['}', '%'])) =
        (name ++ '{' :: (key ++ '}' :: '{' :: (label ++ ['}']))) ++ ['%'] by simp]
      exact getLast?_append_singleton _ _
    rw [backslashLine_mark hl]
    simp only [markAfter, markKey]
    rw [takeWhile_until (not_mem_all hname) (by decide), drop_append_cons,
      takeWhile_until (not_mem_all hkey) (by decide), List.drop_left]
    rw [show '}' :: '{' :: (label ++ ['}', '%']) = "}{".toList ++ (label ++ ['}', '%']) by
      rw [braces_eq]; rfl]
    rw [dropPrefix_append]
    simp [markLabel, dropSuffix_append]
  | .line text, _ => by
    simp [lineText, indent_eq, lineOf, spaceLine]
  | .concl f, _ => by
    rw [lineText, conclOpen_eq]
    simp only [List.cons_append, List.nil_append, lineOf, spaceLine]
    exact braceLine_concl f

/-- The lines of a figure read back. -/
theorem lexLines_map : ∀ {ts : List Line}, (∀ t ∈ ts, LineWF t) → lexLines (ts.map lineText) = some ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [List.map_cons, lexLines]
    rw [lineOf_lineText (h t (List.mem_cons_self ..)),
      lexLines_map (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]
    rfl

theorem newline_not_mem_lineText : ∀ {t : Line}, LineWF t → '\n' ∉ lineText t
  | .blank, _ => by simp [lineText]
  | .beginK, _ => by decide
  | .endK, _ => by decide
  | .andK, _ => by decide
  | .openK, _ => by decide
  | .openEmpty, _ => by decide
  | .closeK, _ => by decide
  | .header _, h => by simp only [LineWF] at h; simp [lineText, inferOpen_eq, inferWord_eq, h]
  | .mark m _, ⟨⟨h1, _, h2, _⟩, h3⟩ => by simp [lineText, h1, h2, h3]
  | .line _, h => by simp only [LineWF] at h; simp [lineText, indent_eq, h]
  | .concl _, h => by simp only [LineWF] at h; simp [lineText, conclOpen_eq, conclClose_eq, h]

/-! ## The parser -/

theorem parsePremises_last (acc : List (List Char)) (p : List Char) (ls : List Line) :
    parsePremises acc (.line p :: .closeK :: ls) = some ((p :: acc).reverse, ls) := by
  rw [parsePremises, premiseNext]

theorem parsePremises_break (acc : List (List Char)) (p q : List Char) (ls : List Line) :
    parsePremises acc (.line (p ++ lineBreak) :: .line q :: ls) =
      parsePremises (p :: acc) (.line q :: ls) := by
  rw [parsePremises, premiseNext, dropSuffix_append, unbreak]

theorem premiseLines_cons (p : List Char) (ps : List (List Char)) :
    ∃ q ls, premiseLines (p :: ps) = .line q :: ls := by
  cases ps <;> simp [premiseLines]

/-- The premises are read back, onto `acc`. -/
theorem parsePremises_lines : ∀ (ps : List (List Char)) (p : List Char) (rest : List Line)
    (acc : List (List Char)),
    parsePremises acc (premiseLines (p :: ps) ++ .closeK :: rest) = some (acc.reverse ++ p :: ps, rest)
  | [], p, rest, acc => by simp [premiseLines, parsePremises_last]
  | p' :: ps, p, rest, acc => by
    have ih := parsePremises_lines ps p' rest (p :: acc)
    obtain ⟨q, ls, hq⟩ := premiseLines_cons p' ps
    simp only [premiseLines, List.cons_append, hq] at ih ⊢
    rw [parsePremises_break, ih]
    simp

/-- A rule's body is read back. -/
theorem parseBody_lines (mark : Option Mark) (label : List Char) (ps : List (List Char))
    (c : List Char) (rest : List Line) :
    parseBody mark label (bodyLines ps c ++ rest) = some (⟨mark, label, ps, c⟩, rest) := by
  cases ps with
  | nil => simp [bodyLines, parseBody]
  | cons p ps =>
    simp only [bodyLines, List.cons_append, List.append_assoc, List.nil_append, parseBody]
    rw [parsePremises_lines]
    simp [withPremises]

/-- A rule is read back, leaving what follows it. -/
theorem parseRule_lines (ru : Rule (List Char)) (rest : List Line) :
    parseRule (ruleLines ru ++ rest) = some (ru, rest) := by
  obtain ⟨mark, label, ps, c⟩ := ru
  cases mark with
  | none =>
    simp only [ruleLines, markLines, List.nil_append, List.cons_append, parseRule]
    exact parseBody_lines ..
  | some m =>
    simp only [ruleLines, markLines, List.cons_append, List.nil_append, parseRule, ↓reduceIte]
    exact parseBody_lines ..

/-- A rule's chunk of the figure: the rule between blank lines. -/
def chunkOf (r : Rule (List Char)) : List Line := .blank :: (ruleLines r ++ [.blank])

theorem parseChunk_chunkOf (r : Rule (List Char)) : parseChunk (chunkOf r) = some r := by
  simp only [chunkOf, parseChunk]
  rw [parseRule_lines]
  rfl

theorem parseChunks_map : ∀ (rs : List (Rule (List Char))), parseChunks (rs.map chunkOf) = some rs
  | [] => rfl
  | r :: rs => by
    simp only [List.map_cons, parseChunks]
    rw [parseChunk_chunkOf, parseChunks_map rs]
    rfl

/-- Chunks joined by `\and` lines. -/
def joinAnd : List (List Line) → List Line
  | [] => []
  | [ch] => ch
  | ch :: ch' :: chs => ch ++ .andK :: joinAnd (ch' :: chs)

theorem chunks_cons {l : Line} (hl : l ≠ .andK) (cur ls : List Line) :
    chunks cur (l :: ls) = chunks (l :: cur) ls := by
  cases l <;> simp [chunks] at hl ⊢

theorem chunks_append {ch : List Line} (h : .andK ∉ ch) : ∀ (rest cur : List Line),
    chunks cur (ch ++ .andK :: rest) = (cur.reverse ++ ch) :: chunks [] rest := by
  induction ch with
  | nil => intro rest cur; simp [chunks]
  | cons l ch ih =>
    intro rest cur
    have hl : l ≠ .andK := fun e => h (e ▸ List.mem_cons_self ..)
    rw [List.cons_append, chunks_cons hl, ih (fun e => h (List.mem_cons_of_mem _ e)) rest (l :: cur)]
    simp

theorem chunks_last {ch : List Line} (h : .andK ∉ ch) : ∀ (cur : List Line),
    chunks cur ch = [cur.reverse ++ ch] := by
  induction ch with
  | nil => intro cur; simp [chunks]
  | cons l ch ih =>
    intro cur
    have hl : l ≠ .andK := fun e => h (e ▸ List.mem_cons_self ..)
    rw [chunks_cons hl, ih (fun e => h (List.mem_cons_of_mem _ e)) (l :: cur)]
    simp

/-- Chunks with no `\and` line come apart again. -/
theorem chunks_joinAnd : ∀ {chs : List (List Line)}, chs ≠ [] → (∀ ch ∈ chs, .andK ∉ ch) →
    chunks [] (joinAnd chs) = chs
  | [], h, _ => absurd rfl h
  | [ch], _, h => by
    simp only [joinAnd]
    rw [chunks_last (h ch (by simp))]
    simp
  | ch :: ch' :: chs, _, h => by
    simp only [joinAnd]
    rw [chunks_append (h ch (by simp)), chunks_joinAnd (chs := ch' :: chs) (by simp)
      (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    simp

theorem mem_premiseLines : ∀ {ps : List (List Char)} {t : Line}, t ∈ premiseLines ps →
    ∃ p, p ∈ ps ∧ (t = .line p ∨ t = .line (p ++ lineBreak))
  | [], _, h => by simp [premiseLines] at h
  | [p], t, h => by
    simp only [premiseLines, List.mem_singleton] at h
    exact ⟨p, by simp, Or.inl h⟩
  | p :: p' :: ps, t, h => by
    simp only [premiseLines, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨p, by simp, Or.inr h⟩
    · obtain ⟨q, hq, hqt⟩ := mem_premiseLines h
      exact ⟨q, List.mem_cons_of_mem _ hq, hqt⟩

theorem andK_not_mem_ruleLines (r : Rule (List Char)) : Line.andK ∉ ruleLines r := by
  obtain ⟨mark, label, ps, c⟩ := r
  intro h
  simp only [ruleLines, List.mem_append, List.mem_cons] at h
  rcases h with h | h | h
  · cases mark <;> simp [markLines] at h
  · exact Line.noConfusion h
  · cases ps with
    | nil => simp [bodyLines] at h
    | cons p ps =>
      simp [bodyLines] at h
      obtain ⟨q, _, hq | hq⟩ := mem_premiseLines h <;> exact Line.noConfusion hq

theorem flatten_ruleItems : ∀ (rs : List (Rule (List Char))), rs ≠ [] →
    ((ruleItems rs).map itemLines).flatten = joinAnd (rs.map chunkOf) ++ [.andK]
  | [], h => absurd rfl h
  | [r], _ => by simp [ruleItems, itemLines, joinAnd, chunkOf]
  | r :: r' :: rs, _ => by
    have ih := flatten_ruleItems (r' :: rs) (by simp)
    simp only [ruleItems, List.map_cons, List.flatten_cons, itemLines] at ih ⊢
    rw [ih]
    simp [joinAnd, chunkOf]

theorem trimAnd_cons (l l' : Line) (x : List Line) : trimAnd (l :: l' :: x) = l :: trimAnd (l' :: x) := by
  simp [trimAnd]

theorem trimAnd_append : ∀ (x : List Line), trimAnd (x ++ [.andK]) = x
  | [] => rfl
  | [l] => by simp [trimAnd]
  | l :: l' :: x => by
    rw [List.cons_append, List.cons_append, trimAnd_cons, ← List.cons_append, trimAnd_append (l' :: x)]

theorem bodyOf_cons (l l' : Line) (x : List Line) : bodyOf (l :: l' :: x) = (bodyOf (l' :: x)).map (List.cons l) := by
  simp [bodyOf]

theorem bodyOf_append : ∀ (x : List Line), bodyOf (x ++ [.endK]) = some x
  | [] => rfl
  | [l] => by simp [bodyOf]
  | l :: l' :: x => by
    rw [List.cons_append, List.cons_append, bodyOf_cons, ← List.cons_append, bodyOf_append (l' :: x)]
    rfl

theorem figureOf_cons {ls : List Line} (h : ls ≠ [.endK]) : figureOf (.beginK :: ls) = rulesOf (bodyOf ls) := by
  match ls with
  | [] => rfl
  | [l] => cases l <;> first | exact absurd rfl h | rfl
  | l :: _ :: _ => cases l <;> rfl

/-- The figure's lines read back as its rules. -/
theorem figureOf_figureLines : ∀ (rs : List (Rule (List Char))),
    figureOf (figureLines (ruleItems rs)) = some rs
  | [] => rfl
  | r :: rs => by
    simp only [figureLines]
    rw [flatten_ruleItems (r :: rs) (by simp), trimAnd_append]
    have hne : joinAnd ((r :: rs).map chunkOf) ++ [Line.endK] ≠ [.endK] := by
      cases rs <;> simp [joinAnd, chunkOf]
    rw [List.cons_append, figureOf_cons hne, bodyOf_append, rulesOf,
      chunks_joinAnd (by simp) (fun ch hch => by
        obtain ⟨r', _, rfl⟩ := List.mem_map.mp hch
        simp only [chunkOf, List.mem_cons, List.mem_append]
        rintro (h | h | h | h)
        · exact Line.noConfusion h
        · exact andK_not_mem_ruleLines r' h
        · exact Line.noConfusion h
        · simp at h),
      parseChunks_map]

/-! ## Plain figures -/

theorem mem_trimAnd : ∀ {x : List Line} {t : Line}, t ∈ trimAnd x → t ∈ x
  | [], _, h => by simp [trimAnd] at h
  | [l], t, h => by cases l <;> simp [trimAnd] at h <;> simp [h]
  | l :: l' :: x, t, h => by
    rw [trimAnd_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_trimAnd h)

theorem lineBreak_eq : lineBreak = [' ', '\\', '\\'] := by decide

theorem wf_ruleLines {r : Rule (List Char)} (hr : r.Plain) : ∀ t ∈ ruleLines r, LineWF t := by
  obtain ⟨mark, label, ps, c⟩ := r
  obtain ⟨hl, hps, hc, hm⟩ := hr
  intro t ht
  simp only [ruleLines, List.mem_append, List.mem_cons] at ht
  rcases ht with ht | ht | ht
  · cases mark with
    | none => simp [markLines] at ht
    | some m =>
      simp only [markLines, List.mem_singleton] at ht
      subst ht
      exact ⟨hm, hl⟩
  · subst ht; exact hl
  · cases ps with
    | nil =>
      simp only [bodyLines, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · trivial
      · exact hc
    | cons p ps =>
      simp only [bodyLines, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | ht | rfl | rfl
      · trivial
      · obtain ⟨q, hq, rfl | rfl⟩ := mem_premiseLines ht
        · exact hps q hq
        · simp only [LineWF, lineBreak_eq, List.mem_append]
          rintro (h | h)
          · exact hps q hq h
          · simp at h
      · trivial
      · exact hc

theorem wf_figureLines {rs : List (Rule (List Char))} (h : ∀ ru ∈ rs, ru.Plain) :
    ∀ t ∈ figureLines (ruleItems rs), LineWF t := by
  intro t ht
  simp only [figureLines, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
  rcases ht with (rfl | ht) | rfl
  · trivial
  · have ht := mem_trimAnd ht
    simp only [List.mem_flatten, List.mem_map, ruleItems] at ht
    obtain ⟨ls, ⟨item, ⟨r, hr, rfl⟩, rfl⟩, ht⟩ := ht
    simp only [itemLines, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | ht | rfl | rfl
    · trivial
    · exact wf_ruleLines (h r hr) t ht
    · trivial
    · trivial
  · trivial

/-- **The figure parser undoes the layout.** A plain figure's text reads back
as its rules. -/
theorem figure_figureChars {rs : List (Rule (List Char))} (h : ∀ ru ∈ rs, ru.Plain) :
    figure (figureChars (ruleItems rs)) = some rs := by
  unfold figure figureChars
  rw [lines_joinLines (by simp [figureLines]) (fun x hx => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
      exact newline_not_mem_lineText (wf_figureLines h t ht)),
    lexLines_map (wf_figureLines h)]
  exact figureOf_figureLines rs

/-- The same, of the layout as the extractor writes it. -/
theorem figure_figureLayout {rs : List (Rule (List Char))} (h : ∀ ru ∈ rs, ru.Plain) :
    figure (figureLayout (ruleItems rs)).toList = some rs := by
  rw [figureLayout, String.toList_ofList]
  exact figure_figureChars h

end SpliceModel
