/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Layout
import SpliceModel.Basic

/-!
# The prose layout round-trips

Theorems about the extractor's prose layout, `Imprimatur.Layout`: the
module the extractor runs (docs/verified-extractor.md). The layout prints
tokens; the parser lexes the text back into tokens and reads the sentence
off them. Both halves are proved to undo the layout, when the formulas are
plain (`Prose.Plain`): the lexer recovers the tokens
(`lex_printToks`), and the parser recovers the sentence from its tokens
(`parseProse_proseToks`). Together: `proseSentence_proseChars`.
-/

namespace SpliceModel

open Imprimatur.Layout

/-! ## Lists -/

theorem isPrefixOf_self_append (l s : List Char) : l.isPrefixOf (l ++ s) = true := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [ih]

theorem takeWhile_until {p : Char → Bool} : ∀ {f : List Char} {d : Char} {s : List Char},
    (∀ x ∈ f, p x = true) → p d = false → (f ++ d :: s).takeWhile p = f
  | [], d, s, _, hd => by simp [hd]
  | c :: f, d, s, hf, hd => by
    have hc := hf c (List.mem_cons_self ..)
    simp only [List.cons_append, List.takeWhile, hc]
    rw [takeWhile_until (fun x hx => hf x (List.mem_cons_of_mem _ hx)) hd]

theorem not_mem_all {c : Char} {f : List Char} (h : c ∉ f) : ∀ x ∈ f, decide (x ≠ c) = true := by
  intro x hx
  apply decide_eq_true
  rintro rfl; exact h hx

/-! ## The lexer -/

/-- Every keyword has a character. -/
theorem kwText_pos (k : Kw) : 1 ≤ (kwText k).length := by cases k <;> decide

/-- A keyword at the front is found. -/
theorem kwAt_kw (k : Kw) (s : List Char) : kwAt (kwText k ++ s) = some k := by
  cases k <;> simp [kwAt, kws, kwText, List.find?, List.isPrefixOf]

/-- The lexer reads a keyword. -/
theorem lexGo_kw (k : Kw) (s : List Char) (acc : List Tok) :
    lexGo (kwText k ++ s) acc = lexGo s (.kw k :: acc) := by
  cases k <;> (conv => lhs; unfold lexGo) <;> simp [kwText, kwAt, kws, labelOpen, List.find?, List.isPrefixOf]

/-- The lexer reads a formula. -/
theorem lexGo_formula {f : List Char} (hf : '$' ∉ f) (s : List Char) (acc : List Tok) :
    lexGo ('$' :: f ++ '$' :: s) acc = lexGo s (.formula f :: acc) := by
  conv => lhs; unfold lexGo
  simp only [List.cons_append, ↓reduceIte]
  rw [takeWhile_until (not_mem_all hf) (by decide), List.drop_left]
  simp

/-- The lexer reads an item number. -/
theorem lexGo_item {ds : List Char} (hne : ds ≠ []) (hd : ')' ∉ ds) (s : List Char) (acc : List Tok) :
    lexGo ('(' :: ds ++ ')' :: '~' :: s) acc = lexGo s (.item ds :: acc) := by
  conv => lhs; unfold lexGo
  simp only [List.cons_append, ↓reduceIte, Char.reduceEq]
  rw [takeWhile_until (not_mem_all hd) (by decide), List.drop_left]
  simp [hne]

/-- The lexer reads a label. -/
theorem lexGo_label {n : List Char} (hn : '}' ∉ n) (s : List Char) (acc : List Tok) :
    lexGo (labelOpen ++ n ++ '}' :: ' ' :: s) acc = lexGo s (.label n :: acc) := by
  have hopen : labelOpen = ['\\', 'L', 'e', 'a', 'n', 'H', 'y', 'p', '{'] := by decide
  have h8 : ∀ l : List Char, List.drop 8 ('L' :: 'e' :: 'a' :: 'n' :: 'H' :: 'y' :: 'p' :: '{' :: l) = l :=
    fun _ => rfl
  conv => lhs; unfold lexGo
  simp only [hopen, List.cons_append, List.nil_append, ↓reduceIte, Char.reduceEq, List.isPrefixOf,
    BEq.rfl, Bool.and_self]
  rw [h8, takeWhile_until (not_mem_all hn) (by decide), List.drop_left]
  simp

/-- A token the lexer can read back: a formula with no dollar, a label with
no closing brace, an item number with a digit and no closing parenthesis. -/
def TokWF : Tok → Prop
  | .kw _ => True
  | .formula f => '$' ∉ f
  | .label n => '}' ∉ n
  | .item ds => ds ≠ [] ∧ ')' ∉ ds

theorem lexGo_tok {t : Tok} (h : TokWF t) (s : List Char) (acc : List Tok) :
    lexGo (tokChars t ++ s) acc = lexGo s (t :: acc) := by
  cases t with
  | kw k => exact lexGo_kw k s acc
  | formula f => simp only [tokChars, List.cons_append, List.append_assoc]; exact lexGo_formula h s acc
  | label n => simp only [tokChars, List.append_assoc, List.cons_append]; exact lexGo_label h s acc
  | item ds => simp only [tokChars, List.cons_append, List.append_assoc]; exact lexGo_item h.1 h.2 s acc

theorem printToks_cons (t : Tok) (ts : List Tok) : printToks (t :: ts) = tokChars t ++ printToks ts := by
  simp [printToks]

theorem lexGo_printToks : ∀ {ts : List Tok}, (∀ t ∈ ts, TokWF t) → ∀ (s : List Char) (acc : List Tok),
    lexGo (printToks ts ++ s) acc = lexGo s (ts.reverse ++ acc)
  | [], _, s, acc => by simp [printToks]
  | t :: ts, h, s, acc => by
    have ht := h t (List.mem_cons_self ..)
    have hts := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [printToks_cons, List.append_assoc, lexGo_tok ht, lexGo_printToks hts]
    simp

/-- **The lexer undoes printing.** -/
theorem lex_printToks {ts : List Tok} (h : ∀ t ∈ ts, TokWF t) : lex (printToks ts) = some ts := by
  unfold lex
  have := lexGo_printToks h [] []
  rw [List.append_nil] at this
  rw [this]
  simp [lexGo]

/-! ## Item numbers -/

theorem digitChar_ne_paren (m : Nat) : Nat.digitChar m ≠ ')' := by
  match m with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => decide
  | n + 16 => simp [Nat.digitChar]

theorem decimalGo_wf : ∀ (fuel n : Nat) (acc : List Char), ')' ∉ acc →
    ')' ∉ decimalGo fuel n acc ∧ (fuel ≠ 0 ∨ acc ≠ [] → decimalGo fuel n acc ≠ [])
  | 0, n, acc, h => by simp [decimalGo, h]
  | fuel + 1, n, acc, h => by
    simp only [decimalGo]
    have hd : ')' ∉ Nat.digitChar (n % 10) :: acc := by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => digitChar_ne_paren _ e.symm, h⟩
    split
    · exact ⟨hd, fun _ => by simp⟩
    · have := decimalGo_wf fuel (n / 10) _ hd
      exact ⟨this.1, fun _ => this.2 (Or.inr (by simp))⟩

/-- The digits of a number: at least one, and no parenthesis. -/
theorem decimal_wf (n : Nat) : decimal n ≠ [] ∧ ')' ∉ decimal n :=
  let h := decimalGo_wf (n + 1) n [] (by simp)
  ⟨h.2 (Or.inl (by omega)), h.1⟩

/-! ## Splitting names from their type -/

theorem hasSub_cons_false {sub : List Char} {c : Char} {cs : List Char} (h : hasSub sub (c :: cs) = false) :
    sub.isPrefixOf (c :: cs) = false ∧ hasSub sub cs = false := by
  simp only [hasSub, Bool.or_eq_false_iff] at h; exact h

theorem commaSep_eq : commaSep = [',', ' '] := by decide

theorem splitAllGo_piece : ∀ (n : List Char) (l cur : List Char) (acc : List (List Char)),
    hasSub commaSep n = false →
    splitAllGo commaSep (n ++ commaSep ++ l) cur acc = splitAllGo commaSep l [] ((cur.reverse ++ n) :: acc)
  | [], l, cur, acc, _ => by
    conv => lhs; unfold splitAllGo
    simp [commaSep_eq, List.isPrefixOf]
  | c :: n, l, cur, acc, h => by
    obtain ⟨h1, h2⟩ := hasSub_cons_false h
    have hnot : commaSep.isPrefixOf (c :: (n ++ commaSep ++ l)) = false := by
      rw [commaSep_eq] at h1 ⊢
      cases n with
      | nil => simp [List.isPrefixOf]
      | cons d n' => simpa [List.isPrefixOf] using h1
    simp only [List.cons_append]
    conv => lhs; unfold splitAllGo
    simp only [hnot, Bool.false_eq_true, ↓reduceIte]
    rw [splitAllGo_piece n l (c :: cur) acc h2]
    simp

theorem splitAllGo_last : ∀ (n : List Char) (cur : List Char) (acc : List (List Char)),
    hasSub commaSep n = false → splitAllGo commaSep n cur acc = ((cur.reverse ++ n) :: acc).reverse
  | [], cur, acc, _ => by unfold splitAllGo; simp
  | c :: n, cur, acc, h => by
    obtain ⟨h1, h2⟩ := hasSub_cons_false h
    conv => lhs; unfold splitAllGo
    simp only [h1, Bool.false_eq_true, ↓reduceIte]
    rw [splitAllGo_last n (c :: cur) acc h2]
    simp

theorem splitAllGo_join : ∀ {ns : List (List Char)}, ns ≠ [] → (∀ n ∈ ns, hasSub commaSep n = false) →
    ∀ (acc : List (List Char)), splitAllGo commaSep (joinComma ns) [] acc = acc.reverse ++ ns
  | [], h, _, _ => absurd rfl h
  | [n], _, h, acc => by
    simp only [joinComma]
    rw [splitAllGo_last n [] acc (h n (by simp))]
    simp
  | n :: m :: ns, _, h, acc => by
    have hn := h n (by simp)
    have hrest : ∀ x ∈ m :: ns, hasSub commaSep x = false := fun x hx => h x (by simp [hx])
    simp only [joinComma]
    rw [splitAllGo_piece n _ [] acc hn, splitAllGo_join (by simp) hrest]
    simp

/-- The names of a group come apart at `, `. -/
theorem splitAll_joinComma {ns : List (List Char)} (hne : ns ≠ []) (h : ∀ n ∈ ns, hasSub commaSep n = false) :
    splitAll commaSep (joinComma ns) = ns := by
  simp [splitAll, splitAllGo_join hne h]

/-- The names of a group come apart from its type at ` \in `. -/
theorem splitFirst_inSep : ∀ (a b : List Char), hasSub inWord a = false →
    splitFirst inSep (a ++ (inSep ++ b)) = some (a, b)
  | [], b, _ => by
    have hi : inSep = [' ', '\\', 'i', 'n', ' '] := by decide
    simp only [List.nil_append, hi]
    simp [splitFirst, List.isPrefixOf]
  | c :: a, b, h => by
    have hi : inSep = [' ', '\\', 'i', 'n', ' '] := by decide
    have hw : inWord = ['\\', 'i', 'n'] := by decide
    have hnot : inSep.isPrefixOf (c :: (a ++ (inSep ++ b))) = false := by
      rw [hi]
      rw [hw] at h
      rcases a with _ | ⟨d, _ | ⟨e, _ | ⟨f, a'⟩⟩⟩
      · simp [List.isPrefixOf]
      · simp [List.isPrefixOf]
      · simp [List.isPrefixOf]
      · by_cases hd : d = '\\'
        · by_cases he : e = 'i'
          · by_cases hf : f = 'n'
            · subst hd he hf
              simp [hasSub, List.isPrefixOf] at h
            · simp only [List.cons_append, List.isPrefixOf]
              simp
              intro _ _ _ h4; exact absurd h4.symm hf
          · simp only [List.cons_append, List.isPrefixOf]
            simp
            intro _ _ h3; exact absurd h3.symm he
        · simp only [List.cons_append, List.isPrefixOf]
          simp
          intro _ h2; exact absurd h2.symm hd
    simp only [List.cons_append]
    conv => lhs; unfold splitFirst
    simp only [hnot, Bool.false_eq_true, ↓reduceIte]
    rw [splitFirst_inSep a b (hasSub_cons_false h).2]
    rfl

/-! ## The parser -/

theorem parseGroups_beAType (f : List Char) (ts : List Tok) (acc : List (VarGroup (List Char))) :
    parseGroups acc (.formula f :: .kw .beAType :: ts) = afterGroup ⟨splitAll commaSep f, .type⟩ acc ts := by
  simp [parseGroups]
theorem parseGroups_beTypes (f : List Char) (ts : List Tok) (acc : List (VarGroup (List Char))) :
    parseGroups acc (.formula f :: .kw .beTypes :: ts) = afterGroup ⟨splitAll commaSep f, .type⟩ acc ts := by
  simp [parseGroups]
theorem parseGroups_beAProp (f : List Char) (ts : List Tok) (acc : List (VarGroup (List Char))) :
    parseGroups acc (.formula f :: .kw .beAProp :: ts) = afterGroup ⟨splitAll commaSep f, .prop⟩ acc ts := by
  simp [parseGroups]
theorem parseGroups_beProps (f : List Char) (ts : List Tok) (acc : List (VarGroup (List Char))) :
    parseGroups acc (.formula f :: .kw .beProps :: ts) = afterGroup ⟨splitAll commaSep f, .prop⟩ acc ts := by
  simp [parseGroups]
theorem parseGroups_ofType (f : List Char) (k : Kw) (hk : k = .comma ∨ k = .andK ∨ k = .dotSpace)
    (ts : List Tok) (acc : List (VarGroup (List Char))) :
    parseGroups acc (.formula f :: .kw k :: ts) = ofTypeGroup acc (.kw k :: ts) (splitFirst inSep f) := by
  rcases hk with rfl | rfl | rfl <;> simp [parseGroups]
theorem afterGroup_comma (g : VarGroup (List Char)) (ts : List Tok) (acc : List (VarGroup (List Char))) :
    afterGroup g acc (.kw .comma :: ts) = parseGroups (g :: acc) ts := by
  simp [afterGroup]
theorem afterGroup_andK (g : VarGroup (List Char)) (ts : List Tok) (acc : List (VarGroup (List Char))) :
    afterGroup g acc (.kw .andK :: ts) = parseGroups (g :: acc) ts := by
  simp [afterGroup]
theorem afterGroup_dotSpace (g : VarGroup (List Char)) (ts : List Tok) (acc : List (VarGroup (List Char))) :
    afterGroup g acc (.kw .dotSpace :: ts) = some ((g :: acc).reverse, ts) := by
  simp [afterGroup]

theorem groupToks_type_one (n : List Char) : groupToks ⟨[n], .type⟩ = [.formula n, .kw .beAType] := rfl
theorem groupToks_type_many (n n' : List Char) (ns : List (List Char)) :
    groupToks ⟨n :: n' :: ns, .type⟩ = [.formula (joinComma (n :: n' :: ns)), .kw .beTypes] := rfl
theorem groupToks_prop_one (n : List Char) : groupToks ⟨[n], .prop⟩ = [.formula n, .kw .beAProp] := rfl
theorem groupToks_prop_many (n n' : List Char) (ns : List (List Char)) :
    groupToks ⟨n :: n' :: ns, .prop⟩ = [.formula (joinComma (n :: n' :: ns)), .kw .beProps] := rfl

/-- A separator between groups, or the end of the *Let* sentence. -/
theorem parseGroups_group {g : VarGroup (List Char)} (hg : g.Plain) (k : Kw)
    (hk : k = .comma ∨ k = .andK ∨ k = .dotSpace) (ts : List Tok) (acc : List (VarGroup (List Char))) :
    parseGroups acc (groupToks g ++ .kw k :: ts) = afterGroup g acc (.kw k :: ts) := by
  obtain ⟨names, kind⟩ := g
  obtain ⟨hne, hnames, hkind⟩ := hg
  have hsplit := splitAll_joinComma hne (fun n hn => (hnames n hn).2)
  simp only at hsplit hkind
  cases kind with
  | ofType ty =>
    simp only [groupToks, List.append_assoc, List.cons_append, List.nil_append]
    rw [parseGroups_ofType _ k hk, splitFirst_inSep _ _ hkind.2]
    simp only [ofTypeGroup, hsplit]
  | type =>
    cases names with
    | nil => exact absurd rfl hne
    | cons n ns =>
      cases ns with
      | nil =>
        simp only [joinComma] at hsplit
        rw [groupToks_type_one, List.cons_append, List.cons_append, List.nil_append, parseGroups_beAType, hsplit]
      | cons n' ns' =>
        rw [groupToks_type_many, List.cons_append, List.cons_append, List.nil_append, parseGroups_beTypes, hsplit]
  | prop =>
    cases names with
    | nil => exact absurd rfl hne
    | cons n ns =>
      cases ns with
      | nil =>
        simp only [joinComma] at hsplit
        rw [groupToks_prop_one, List.cons_append, List.cons_append, List.nil_append, parseGroups_beAProp, hsplit]
      | cons n' ns' =>
        rw [groupToks_prop_many, List.cons_append, List.cons_append, List.nil_append, parseGroups_beProps, hsplit]

theorem andToks_cons (x : List Tok) (xs : List (List Tok)) : andToks (x :: xs) = x ++ andRestToks xs := rfl

/-- The groups of a *Let* sentence are read back. -/
theorem parseGroups_all : ∀ (gs : List (VarGroup (List Char))) (g : VarGroup (List Char)),
    (∀ x ∈ g :: gs, x.Plain) → ∀ (rest : List Tok) (acc : List (VarGroup (List Char))),
    parseGroups acc (andToks ((g :: gs).map groupToks) ++ .kw .dotSpace :: rest) =
      some (acc.reverse ++ g :: gs, rest)
  | [], g, h, rest, acc => by
    rw [List.map_cons, List.map_nil, andToks_cons, andRestToks, List.append_nil,
      parseGroups_group (h g (by simp)) .dotSpace (by simp), afterGroup_dotSpace]
    simp
  | g' :: gs', g, h, rest, acc => by
    have hg := h g (by simp)
    have hrest : ∀ x ∈ g' :: gs', x.Plain := fun x hx => h x (by simp [hx])
    have ih := parseGroups_all gs' g' hrest rest (g :: acc)
    rw [List.map_cons, andToks_cons] at ih ⊢
    cases gs' with
    | nil =>
      simp only [List.map_cons, List.map_nil, andRestToks, List.append_nil, List.append_assoc,
        List.cons_append] at ih ⊢
      rw [parseGroups_group hg .andK (by simp), afterGroup_andK, ih]
      simp
    | cons g'' gs'' =>
      simp only [List.map_cons, andRestToks, List.append_assoc, List.cons_append] at ih ⊢
      rw [parseGroups_group hg .comma (by simp), afterGroup_comma, ih]
      simp

/-- A hypothesis, then a separator or the end of the *Assume* sentence. -/
theorem parseHyps_hyp (h : Hyp (List Char)) (ts : List Tok) (acc : List (Hyp (List Char))) :
    parseHyps acc (hypToks h ++ .kw .comma :: ts) = parseHyps (h :: acc) ts ∧
    parseHyps acc (hypToks h ++ .kw .andK :: ts) = parseHyps (h :: acc) ts ∧
    parseHyps acc (hypToks h ++ .kw .dotSpace :: .kw .thenK :: ts) = some ((h :: acc).reverse, ts) := by
  obtain ⟨label, f⟩ := h
  cases label <;> simp [hypToks, parseHyps]

/-- The hypotheses of an *Assume* sentence are read back. -/
theorem parseHyps_all : ∀ (hs : List (Hyp (List Char))) (h : Hyp (List Char)) (rest : List Tok)
    (acc : List (Hyp (List Char))),
    parseHyps acc (andToks ((h :: hs).map hypToks) ++ .kw .dotSpace :: .kw .thenK :: rest) =
      some (acc.reverse ++ h :: hs, rest)
  | [], h, rest, acc => by
    rw [List.map_cons, List.map_nil, andToks_cons, andRestToks, List.append_nil, (parseHyps_hyp h rest acc).2.2]
    simp
  | h' :: hs', h, rest, acc => by
    have ih := parseHyps_all hs' h' rest (h :: acc)
    rw [List.map_cons, andToks_cons] at ih ⊢
    cases hs' with
    | nil =>
      simp only [List.map_cons, List.map_nil, andRestToks, List.append_nil, List.append_assoc,
        List.cons_append] at ih ⊢
      rw [(parseHyps_hyp h _ acc).2.1, ih]
      simp
    | cons h'' hs'' =>
      simp only [List.map_cons, andRestToks, List.append_assoc, List.cons_append] at ih ⊢
      rw [(parseHyps_hyp h _ acc).1, ih]
      simp

/-- The conjuncts after the first are read back. -/
theorem parseItems_rest : ∀ (fs : List (List Char)) (i : Nat) (acc : List (List Char)),
    parseItems acc (andRestToks (numbered i fs) ++ [.kw .endK]) = (.conjuncts (acc.reverse ++ fs), [.kw .endK])
  | [], _, acc => by simp [numbered, andRestToks, parseItems]
  | [f], i, acc => by simp [numbered, andRestToks, parseItems]
  | f :: f' :: fs, i, acc => by
    have ih := parseItems_rest (f' :: fs) (i + 1) (f :: acc)
    simp only [numbered, andRestToks, List.cons_append, List.nil_append] at ih ⊢
    simp only [parseItems]
    rw [ih]
    simp

/-- A conclusion is read back. -/
theorem parseConcl_concl : ∀ {c : Concl (List Char)}, c.Plain →
    parseConcl (conclToks c ++ [.kw .endK]) = some (c, [.kw .endK])
  | .formula f, _ => by simp [conclToks, parseConcl]
  | .conjuncts [], h => absurd rfl h.1
  | .conjuncts (f :: fs), _ => by
    simp only [conclToks, numbered, andToks_cons, List.cons_append, List.nil_append, parseConcl]
    rw [parseItems_rest]
    simp
  | .iff lhs rhs, _ => by simp [conclToks, parseConcl]
  | .exists_ w body, h => by
    simp only [conclToks, List.cons_append, parseConcl, afterSuch]
    rw [parseConcl_concl h.2]

theorem finish_concl {c : Concl (List Char)} (h : c.Plain) (gs : List (VarGroup (List Char)))
    (hs : List (Hyp (List Char))) : finish gs hs (conclToks c ++ [.kw .endK]) = some ⟨gs, hs, c⟩ := by
  simp [finish, finishWith, parseConcl_concl h]

/-- A conclusion is never a *Let*, an *Assume* or a *We define*. -/
theorem conclToks_head : ∀ {c : Concl (List Char)}, c.Plain → ∀ (rest : List Tok),
    (∀ ts, conclToks c ++ rest ≠ .kw .letK :: ts) ∧ (∀ ts, conclToks c ++ rest ≠ .kw .assumeK :: ts) ∧
    (∀ ts, conclToks c ++ rest ≠ .kw .weDefine :: ts)
  | .formula f, _, rest => by simp [conclToks]
  | .conjuncts [], h, _ => absurd rfl h.1
  | .conjuncts (f :: fs), _, rest => by simp [conclToks, numbered, andToks_cons]
  | .iff lhs rhs, _, rest => by simp [conclToks]
  | .exists_ w body, _, rest => by simp [conclToks]

/-- A sentence that starts with neither *Let* nor *Assume* is a conclusion. -/
theorem parseStatement_default {l : List Tok} (h1 : ∀ ts, l ≠ .kw .letK :: ts)
    (h2 : ∀ ts, l ≠ .kw .assumeK :: ts) : parseStatement l = finish [] [] l := by
  cases l with
  | nil => rfl
  | cons t ts =>
    cases t with
    | kw k =>
      cases k
      all_goals first
        | rfl
        | exact absurd rfl (h1 ts)
        | exact absurd rfl (h2 ts)
    | formula _ => rfl
    | label _ => rfl
    | item _ => rfl

/-- A theorem's sentence is read back from its tokens. -/
theorem parseStatement_statementToks {s : Statement (List Char)}
    (hv : ∀ g ∈ s.vars, g.Plain) (hh : ∀ h ∈ s.hyps, h.Plain) (hc : s.concl.Plain) :
    parseStatement (statementToks s) = some s ∧
    ∀ ts, statementToks s ≠ .kw .weDefine :: ts := by
  obtain ⟨vars, hyps, concl⟩ := s
  simp only at hv hh hc
  cases vars with
  | nil =>
    cases hyps with
    | nil =>
      simp only [statementToks, letToks, assumeToks, thenToks, thenKw, List.nil_append, sentencesToks]
      obtain ⟨h1, h2, h3⟩ := conclToks_head hc [.kw .endK]
      exact ⟨by rw [parseStatement_default h1 h2, finish_concl hc], h3⟩
    | cons h hs =>
      simp only [statementToks, letToks, assumeToks, thenToks, thenKw, List.nil_append, sentencesToks,
        List.cons_append, List.append_assoc]
      refine ⟨?_, by simp⟩
      simp only [parseStatement]
      rw [parseHyps_all hs h _ []]
      simp [afterAssume, finish_concl hc]
  | cons g gs =>
    cases hyps with
    | nil =>
      simp only [statementToks, letToks, assumeToks, thenToks, thenKw, List.append_nil, List.nil_append,
        sentencesToks, List.cons_append, List.append_assoc]
      refine ⟨?_, by simp⟩
      simp only [parseStatement]
      rw [parseGroups_all gs g hv _ []]
      simp [afterLet, finish_concl hc]
    | cons h hs =>
      simp only [statementToks, letToks, assumeToks, thenToks, thenKw, sentencesToks, List.cons_append,
        List.append_assoc, List.nil_append]
      refine ⟨?_, by simp⟩
      simp only [parseStatement]
      rw [parseGroups_all gs g hv _ []]
      simp only [List.reverse_nil, List.nil_append, afterLet]
      rw [parseHyps_all hs h _ []]
      simp [afterAssume, finish_concl hc]

/-- **The parser undoes the layout, on tokens.** -/
theorem parseProse_proseToks : ∀ {p : Prose (List Char)}, p.Plain → parseProse (proseToks p) = some p
  | .define f, _ => by simp [proseToks, parseProse]
  | .statement s, ⟨hv, hh, hc⟩ => by
    obtain ⟨hp, hne⟩ := parseStatement_statementToks hv hh hc
    rw [proseToks]
    cases hb : statementToks s with
    | nil => simp [statementToks] at hb
    | cons t ts =>
      rw [hb] at hp hne
      cases t with
      | kw k =>
        cases k
        case weDefine => exact absurd rfl (hne ts)
        all_goals simp [parseProse, hp]
      | formula f => simp [parseProse, hp]
      | label n => simp [parseProse, hp]
      | item ds => simp [parseProse, hp]

/-! ## Plain sentences print well-formed tokens -/

theorem dollar_not_mem_joinComma : ∀ {ns : List (List Char)}, (∀ n ∈ ns, '$' ∉ n) → '$' ∉ joinComma ns
  | [], _ => by simp [joinComma]
  | [n], h => h n (by simp)
  | n :: m :: ns, h => by
    simp only [joinComma, List.mem_append, not_or]
    refine ⟨⟨h n (by simp), by decide⟩, dollar_not_mem_joinComma fun x hx => h x (by simp [hx])⟩

theorem wf_andRestToks : ∀ {xs : List (List Tok)}, (∀ x ∈ xs, ∀ t ∈ x, TokWF t) →
    ∀ t ∈ andRestToks xs, TokWF t
  | [], _, t, ht => by simp [andRestToks] at ht
  | [y], h, t, ht => by
    simp only [andRestToks, List.mem_cons] at ht
    rcases ht with rfl | ht
    · trivial
    · exact h y (by simp) t ht
  | y :: z :: zs, h, t, ht => by
    simp only [andRestToks, List.cons_append, List.mem_cons, List.mem_append] at ht
    rcases ht with rfl | ht | ht
    · trivial
    · exact h y (by simp) t ht
    · exact wf_andRestToks (fun x hx => h x (by simp [hx])) t ht

theorem wf_andToks {xs : List (List Tok)} (h : ∀ x ∈ xs, ∀ t ∈ x, TokWF t) : ∀ t ∈ andToks xs, TokWF t := by
  cases xs with
  | nil => simp [andToks]
  | cons x xs =>
    intro t ht
    simp only [andToks_cons, List.mem_append] at ht
    rcases ht with ht | ht
    · exact h x (by simp) t ht
    · exact wf_andRestToks (fun y hy => h y (by simp [hy])) t ht

theorem wf_groupToks {g : VarGroup (List Char)} (hg : g.Plain) : ∀ t ∈ groupToks g, TokWF t := by
  obtain ⟨names, kind⟩ := g
  obtain ⟨_, hnames, hkind⟩ := hg
  have hj : '$' ∉ joinComma names := dollar_not_mem_joinComma fun n hn => (hnames n hn).1
  cases kind with
  | ofType ty =>
    simp only at hkind
    intro t ht
    simp only [groupToks, List.mem_singleton] at ht
    subst ht
    simp only [TokWF, List.mem_append, not_or]
    exact ⟨⟨hj, by decide⟩, hkind.1⟩
  | type =>
    intro t ht
    rcases names with _ | ⟨n, _ | ⟨n', ns⟩⟩
    · simp only [groupToks, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp [TokWF]
    · simp only [groupToks, List.mem_cons, List.not_mem_nil, or_false] at ht
      simp only [joinComma] at hj
      rcases ht with rfl | rfl <;> simp [TokWF, hj]
    · simp only [groupToks, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp [TokWF, hj]
  | prop =>
    intro t ht
    rcases names with _ | ⟨n, _ | ⟨n', ns⟩⟩
    · simp only [groupToks, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp [TokWF]
    · simp only [groupToks, List.mem_cons, List.not_mem_nil, or_false] at ht
      simp only [joinComma] at hj
      rcases ht with rfl | rfl <;> simp [TokWF, hj]
    · simp only [groupToks, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp [TokWF, hj]

theorem wf_hypToks {h : Hyp (List Char)} (hh : h.Plain) : ∀ t ∈ hypToks h, TokWF t := by
  obtain ⟨label, f⟩ := h
  obtain ⟨hf, hl⟩ := hh
  cases label with
  | none =>
    intro t ht
    simp only [hypToks, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht; exact hf
  | some n =>
    intro t ht
    simp only [hypToks, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact hl
    · exact hf

theorem wf_numbered : ∀ {fs : List (List Char)} (i : Nat), (∀ f ∈ fs, '$' ∉ f) →
    ∀ x ∈ numbered i fs, ∀ t ∈ x, TokWF t
  | [], _, _ => by simp [numbered]
  | f :: fs, i, h => by
    intro x hx
    simp only [numbered, List.mem_cons] at hx
    rcases hx with rfl | hx
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact decimal_wf i
      · exact h f (by simp)
    · exact wf_numbered (i + 1) (fun y hy => h y (by simp [hy])) x hx

theorem wf_conclToks : ∀ {c : Concl (List Char)}, c.Plain → ∀ t ∈ conclToks c, TokWF t
  | .formula f, h => by
    intro t ht
    simp only [conclToks, List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht; exact h
  | .conjuncts fs, h => wf_andToks (wf_numbered 1 h.2)
  | .iff a b, h => by
    intro t ht
    simp only [conclToks, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact h.1
    · trivial
    · exact h.2
  | .exists_ v body, h => by
    intro t ht
    simp only [conclToks, List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | ht
    · trivial
    · exact h.1
    · trivial
    · exact wf_conclToks h.2 t ht

theorem wf_sentencesToks : ∀ {ss : List (List Tok)}, (∀ x ∈ ss, ∀ t ∈ x, TokWF t) →
    ∀ t ∈ sentencesToks ss, TokWF t
  | [], _ => by simp [sentencesToks]
  | [x], h => h x (by simp)
  | x :: y :: ys, h => by
    intro t ht
    simp only [sentencesToks, List.mem_append, List.mem_cons] at ht
    rcases ht with ht | rfl | ht
    · exact h x (by simp) t ht
    · trivial
    · exact wf_sentencesToks (fun z hz => h z (by simp [hz])) t ht

theorem wf_letToks {vars : List (VarGroup (List Char))} (hv : ∀ g ∈ vars, g.Plain) :
    ∀ x ∈ letToks vars, ∀ t ∈ x, TokWF t := by
  cases vars with
  | nil => simp [letToks]
  | cons g gs =>
    intro x hx
    simp only [letToks, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    intro t ht
    rw [List.mem_cons] at ht
    rcases ht with rfl | ht
    · trivial
    · exact wf_andToks (fun x hx => by
        obtain ⟨g', hg, rfl⟩ := List.mem_map.mp hx
        exact wf_groupToks (hv g' hg)) t ht

theorem wf_assumeToks {hyps : List (Hyp (List Char))} (hh : ∀ h ∈ hyps, h.Plain) :
    ∀ x ∈ assumeToks hyps, ∀ t ∈ x, TokWF t := by
  cases hyps with
  | nil => simp [assumeToks]
  | cons h hs =>
    intro x hx
    simp only [assumeToks, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    intro t ht
    rw [List.mem_cons] at ht
    rcases ht with rfl | ht
    · trivial
    · exact wf_andToks (fun x hx => by
        obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hx
        exact wf_hypToks (hh h' hh')) t ht

theorem wf_thenToks {c : Concl (List Char)} (hc : c.Plain) (before : List (List Tok)) :
    ∀ t ∈ thenToks before c, TokWF t := by
  intro t ht
  cases before with
  | nil =>
    simp only [thenToks, thenKw, List.nil_append] at ht
    exact wf_conclToks hc t ht
  | cons x xs =>
    simp only [thenToks, thenKw, List.cons_append, List.nil_append, List.mem_cons] at ht
    rcases ht with rfl | ht
    · trivial
    · exact wf_conclToks hc t ht

theorem wf_statementToks {s : Statement (List Char)}
    (hv : ∀ g ∈ s.vars, g.Plain) (hh : ∀ h ∈ s.hyps, h.Plain) (hc : s.concl.Plain) :
    ∀ t ∈ statementToks s, TokWF t := by
  intro t ht
  rw [statementToks, List.mem_append] at ht
  rcases ht with ht | ht
  · refine wf_sentencesToks ?_ t ht
    intro x hx
    rw [List.mem_append, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact wf_letToks hv x hx
    · exact wf_assumeToks hh x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      exact wf_thenToks hc _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht; trivial

theorem wf_proseToks : ∀ {p : Prose (List Char)}, p.Plain → ∀ t ∈ proseToks p, TokWF t
  | .define f, h => by
    intro t ht
    simp only [proseToks, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> trivial
  | .statement s, ⟨hv, hh, hc⟩ => by
    intro t ht
    rw [proseToks, List.mem_cons] at ht
    rcases ht with rfl | ht
    · trivial
    · exact wf_statementToks hv hh hc t ht

/-! ## The theorem -/

theorem proseSentence_proseChars {pr : Prose (List Char)} (h : pr.Plain) :
    proseSentence (proseChars pr) = some pr := by
  unfold proseSentence proseChars
  rw [lex_printToks (wf_proseToks h)]
  simp only [Option.bind_some]
  exact parseProse_proseToks h

/-- **The prose parser undoes the layout**, when the sentence is plain. This
is the extractor's layout and the extractor's parser. -/
theorem proseSentence_proseLayout {pr : Prose (List Char)} (h : pr.Plain) :
    proseSentence (proseLayout pr).toList = some pr := by
  rw [proseLayout, String.toList_ofList]
  exact proseSentence_proseChars h

end SpliceModel
