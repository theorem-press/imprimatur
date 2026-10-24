/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice
import SpliceModel.Splicer

/-!
# Theorem 1, of the code that runs

What a clean `imprimatur check` guarantees (DESIGN §18.2), stated of
`Splice.checkDoc`, which is what `check` reports (docs/verified-splicer.md,
"Theorem 1, precisely"). If the bundle is true of a world and `check`
reports nothing, warnings included, then:

- every block and `\leaninline` shows a statement Lean proved: its key is
  declared and trusted, its view of the statement is the world's rendering,
  its region is, after normalisation, that rendering as the splicer sets it
  (the alias's template, the authors' slot text merged by the model's
  `fill`, line endings); and, if it is typeset, the rendering reads back as
  the statement (`checkDoc_block`);
- every `\leanref` and `\leancheck` names a declared, trusted statement, and
  a `\leancheck`'s recorded hash is the statement's (`checkDoc_ref`,
  `checkDoc_check`).
-/

namespace SpliceModel.Theorem1

open Splice Imprimatur

/-- The bundles the splicer reads. -/
abbrev B := Imprimatur.Bundle (Imprimatur.Image Imprimatur.TeX) Imprimatur.Verdict

/-! ## Folds of diagnostics -/

theorem foldl_append_init {α : Type} (g : α → Array Splice.Diag) :
    ∀ (xs : List α) (init : Array Splice.Diag),
      xs.foldl (fun ds x => ds ++ g x) init = init ++ xs.foldl (fun ds x => ds ++ g x) #[]
  | [], init => by simp
  | x :: xs, init => by
    simp only [List.foldl_cons]
    rw [foldl_append_init g xs (init ++ g x), foldl_append_init g xs (#[] ++ g x)]
    simp [Array.append_assoc]

theorem foldl_append_empty {α : Type} (g : α → Array Splice.Diag) :
    ∀ (xs : List α), xs.foldl (fun ds x => ds ++ g x) #[] = #[] ↔ ∀ x ∈ xs, g x = #[]
  | [] => by simp
  | x :: xs => by
    simp only [List.foldl_cons]
    rw [foldl_append_init g xs, Array.append_eq_empty_iff, foldl_append_empty g xs]
    simp

theorem foldl_concat_empty : ∀ (l : List (Array Splice.Diag)) (init : Array Splice.Diag),
    l.foldl (· ++ ·) init = #[] ↔ init = #[] ∧ ∀ a ∈ l, a = #[]
  | [], init => by simp
  | a :: l, init => by
    simp only [List.foldl_cons]
    rw [foldl_concat_empty l, Array.append_eq_empty_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem foldl_concat_empty' {β : Type} : ∀ (l : List (Array β)) (init : Array β),
    l.foldl (· ++ ·) init = #[] ↔ init = #[] ∧ ∀ a ∈ l, a = #[]
  | [], init => by simp
  | a :: l, init => by
    simp only [List.foldl_cons]
    rw [foldl_concat_empty' l, Array.append_eq_empty_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-! ## A clean check is a clean plan and a clean audit -/

theorem sortDiags_empty {doc : Splice.Doc} {ds : Array Splice.Diag} (h : sortDiags doc ds = #[]) :
    ds = #[] := by
  unfold sortDiags at h
  have := congrArg Array.size h
  simp only [List.size_toArray, List.length_mergeSort, Array.length_toList] at this
  exact Array.size_eq_zero_iff.mp this

theorem staleDiags_empty {changes : Array Change} {diff : Bool} (h : staleDiags changes diff = #[]) :
    changes = #[] := by
  unfold staleDiags at h
  have := congrArg Array.size h
  simp only [Array.size_map, Array.size_empty] at this
  exact Array.size_eq_zero_iff.mp this

/-- A clean check: the plan reports nothing and changes nothing, and the
audit finds nothing. -/
theorem checkDoc_parts {doc : Splice.Doc} {b : B} {opts : ApplyOpts} {extra : Array String} {diff : Bool}
    (hc : checkDoc doc b opts extra diff = #[]) :
    (plan doc b opts).diags = #[] ∧ (plan doc b opts).changes = #[] ∧ audit doc b = #[] := by
  unfold checkDoc at hc
  have h := sortDiags_empty hc
  simp only [Array.append_eq_empty_iff] at h
  obtain ⟨⟨⟨h1, h2⟩, _⟩, h4⟩ := h
  exact ⟨h1, staleDiags_empty h4, h2⟩

/-! ## A clean plan is clean items -/

/-- When `planOnce` changes nothing, it writes nothing, so `plan` is
`planOnce`. -/
theorem planOnce_quiet {doc : Splice.Doc} {b : B} {o : ApplyOpts}
    (h : (planOnce doc b o).changes = #[]) : (planOnce doc b o).outputs = #[] := by
  unfold planOnce at *
  simp only at *
  rw [foldl_concat_empty'] at h
  obtain ⟨_, h⟩ := h
  apply Array.size_eq_zero_iff.mp
  simp only [List.size_toArray, List.length_eq_zero_iff, List.filterMap_eq_nil_iff]
  intro ⟨f, fi, r⟩ hm
  simp only [List.mem_map] at hm
  obtain ⟨⟨f', fi'⟩, _, heq⟩ := hm
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  have hch := h _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, by assumption, rfl⟩, rfl⟩)
  unfold planFile at hch ⊢
  simp only at hch ⊢
  have hnone : ∀ x ∈ f'.scan.items.toList.zipIdx, (planItem doc.cfg (blockLabels doc) b o f'.src fi'
      (dominantEol f'.src.chars) x.1 x.2).change = none := by
    intro x hx
    have := congrArg Array.toList hch
    simp only [List.filterMap_eq_nil_iff, List.mem_map] at this
    exact this _ ⟨x, hx, rfl⟩
  split
  · rfl
  · rename_i hne
    exfalso; apply hne
    simp only [List.isEmpty_iff, List.filterMap_eq_nil_iff, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    simp [hnone x hx]

/-! ## A clean item -/

theorem push_ne_empty {α : Type} (a : Array α) (x : α) : a.push x ≠ #[] := by
  intro h; have := congrArg Array.size h; simp at this

/-- What a block or inline item that plans cleanly (no diagnostics, no
change) is: its key's entry has its view, the alias's template applies, and
its region is, after normalisation, what the splicer would write there. -/
theorem planItem_clean {cfg : Config} {labels : Array (Nat × Nat × String)} {b : B} {o : ApplyOpts}
    {s : Src} {fi : Nat} {eol : String} {it : Item} {ii : Nat}
    (hk : it.kind = .block ∨ it.kind = .inline)
    (hd : (planItem cfg labels b o s fi eol it ii).diags = #[])
    (hc : (planItem cfg labels b o s fi eol it ii).change = none) :
    ∃ e g new, b.find? it.key = some e ∧ e.statement.view? (itemView cfg it) = some g ∧
      renderItem cfg labels o (s.locString it.start) fi ii it e g = .ok new ∧
      normalize (s.slice it.regionStart it.regionEnd) =
        normalize (regionContent cfg o (s.locString it.start) eol it new
          (s.slice it.regionStart it.regionEnd)).content := by
  have hskip : (it.kind == .check || it.kind == .index || it.kind == .leanok || it.kind == .hypref) = false := by
    rcases hk with h | h <;> rw [h] <;> rfl
  have hnref : (it.kind == .ref) = false := by rcases hk with h | h <;> rw [h] <;> rfl
  unfold planItem at hd hc
  rw [hskip] at hd hc
  simp only [Bool.false_eq_true, ↓reduceIte] at hd hc
  cases he : b.find? it.key with
  | none => rw [he] at hd; simp at hd
  | some e =>
    rw [he] at hd hc
    simp only at hd hc
    have hg : ∀ x, generatedOf cfg o (s.locString it.start) it e = .ok x →
        e.statement.view? (itemView cfg it) = some x := by
      intro x hx
      unfold generatedOf at hx
      rw [hnref] at hx
      simp only [Bool.false_eq_true, ↓reduceIte] at hx
      split at hx
      · cases hx; assumption
      · cases hx
    cases hgen : generatedOf cfg o (s.locString it.start) it e with
    | error d => rw [hgen] at hd; simp at hd
    | ok g =>
      rw [hgen] at hd hc
      simp only at hd hc
      cases hr : renderItem cfg labels o (s.locString it.start) fi ii it e g with
      | error d => rw [hr] at hd; simp at hd
      | ok new =>
        rw [hr] at hd hc
        simp only at hd hc
        refine ⟨e, g, new, rfl, hg g hgen, hr, ?_⟩
        generalize hrc : regionContent cfg o (s.locString it.start) eol it new
          (s.slice it.regionStart it.regionEnd) = rc at hd hc
        cases hbad : badContent? cfg (s.locString it.start) it rc.content with
        | some d => rw [hbad] at hd; exact absurd hd (push_ne_empty _ _)
        | none =>
          rw [hbad] at hd hc
          simp only at hd hc
          generalize hsame : (normalize (s.slice it.regionStart it.regionEnd) == normalize rc.content) = same
            at hd hc
          cases hhe : handEdited? o (itemSlots cfg it) (s.locString it.start) it
              (s.slice it.regionStart it.regionEnd) same with
          | some d => rw [hhe] at hd; exact absurd hd (push_ne_empty _ _)
          | none =>
            rw [hhe] at hc
            simp only at hc
            split at hc
            · rename_i hedits
              cases same with
              | true => simpa using hsame
              | false => simp [itemRewrite] at hedits
            · cases hc

/-- A clean plan: every item of every file plans with no diagnostics and no
change. -/
theorem items_clean {doc : Splice.Doc} {b : B} {o : ApplyOpts}
    (hd : (plan doc b o).diags = #[]) (hc : (plan doc b o).changes = #[])
    {f : SourceFile} {fi : Nat} (hf : (f, fi) ∈ doc.files.toList.zipIdx)
    {it : Item} {ii : Nat} (hi : (it, ii) ∈ f.scan.items.toList.zipIdx) :
    let r := planItem doc.cfg (blockLabels doc) b o f.src fi (dominantEol f.src.chars) it ii
    r.diags = #[] ∧ r.change = none := by
  intro r
  rw [SpliceModel.Splicer.plan_changes] at hc
  rw [SpliceModel.Splicer.plan_of_quiet (planOnce_quiet hc)] at hd
  unfold planOnce at hd hc
  simp only at hd hc
  rw [foldl_concat_empty] at hd
  rw [foldl_concat_empty'] at hc
  have hfd := hd.2 _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, hf, rfl⟩, rfl⟩)
  have hfc := hc.2 _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, hf, rfl⟩, rfl⟩)
  unfold planFile at hfd hfc
  simp only at hfd hfc
  rw [foldl_concat_empty] at hfd
  refine ⟨hfd.2 _ (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨_, hi, rfl⟩, rfl⟩), ?_⟩
  have := congrArg Array.toList hfc
  simp only [List.filterMap_eq_nil_iff, List.mem_map] at this
  exact this _ ⟨_, hi, rfl⟩

/-! ## A clean audit -/

theorem foldl_array_append {α : Type} (g : α → Array Splice.Diag) (xs : Array α) (init : Array Splice.Diag) :
    xs.foldl (fun ds x => ds ++ g x) init = init ++ xs.foldl (fun ds x => ds ++ g x) #[] := by
  rw [← Array.foldl_toList, ← Array.foldl_toList, foldl_append_init]

theorem foldl_array_empty {α : Type} (g : α → Array Splice.Diag) (xs : Array α) :
    xs.foldl (fun ds x => ds ++ g x) #[] = #[] ↔ ∀ x ∈ xs, g x = #[] := by
  rw [← Array.foldl_toList, foldl_append_empty]
  simp

/-- A clean audit: every key of every item audits clean. -/
theorem keys_clean {doc : Splice.Doc} {b : B} (h : audit doc b = #[]) {f : SourceFile}
    (hf : f ∈ doc.files) {it : Item} (hi : it ∈ f.scan.items) {key : String} (hk : key ∈ it.allKeys) :
    auditKey doc.cfg b it (f.src.locString it.start) key = #[] := by
  unfold audit at h
  rw [Array.append_eq_empty_iff] at h
  have hF : (fun (ds : Array Splice.Diag) (f : SourceFile) =>
      f.scan.items.foldl (init := ds) (fun ds it => ds ++ auditItem doc.cfg b f it) ++ auditLeanok doc.cfg b f) =
      (fun ds f => ds ++ (f.scan.items.foldl (init := #[]) (fun ds it => ds ++ auditItem doc.cfg b f it) ++
        auditLeanok doc.cfg b f)) := by
    funext ds f
    rw [foldl_array_append, Array.append_assoc]
  have h1 := h.1
  rw [hF, foldl_array_empty] at h1
  have h2 := Array.append_eq_empty_iff.mp (h1 f hf)
  rw [foldl_array_empty] at h2
  have h3 := h2.1 it hi
  unfold auditItem at h3
  simp only [Array.append_eq_empty_iff] at h3
  rw [foldl_array_empty] at h3
  exact h3.1 key hk

/-- No trust problems: the verdict is trusted. -/
theorem trusted_of_trustProblems {allowed : Array String} {key : String} {e : Imprimatur.Entry (Image TeX) Verdict}
    (h : trustProblems allowed key e = #[]) : Verdict.trusted allowed e.verdict = true := by
  unfold trustProblems at h
  simp only [Array.append_eq_empty_iff] at h
  obtain ⟨⟨hs, ha⟩, hc⟩ := h
  unfold Verdict.trusted
  have hs' : e.verdict.usesSorry = false := by
    cases hu : e.verdict.usesSorry
    · rfl
    · rw [hu] at hs; simp at hs
  have ha' : e.verdict.axioms.all (fun a => a == "sorryAx" || allowed.contains a) = true := by
    split at ha
    · rename_i hbad
      rw [Array.isEmpty_iff] at hbad
      rw [Array.all_eq_true]
      intro i hi
      have := congrArg (·.size) hbad
      simp only [Array.size_empty] at this
      by_cases hx : (e.verdict.axioms[i] == "sorryAx" || allowed.contains e.verdict.axioms[i]) = true
      · exact hx
      · exfalso
        have hmem : e.verdict.axioms[i] ∈ e.verdict.axioms.filter
            (fun a => a != "sorryAx" && !allowed.contains a) := by
          rw [Array.mem_filter]
          refine ⟨Array.getElem_mem hi, ?_⟩
          simp only [Bool.not_eq_true, Bool.or_eq_false_iff] at hx
          have hp : ¬e.verdict.axioms[i] = "sorryAx" ∧ ¬e.verdict.axioms[i] ∈ allowed := by
            refine ⟨fun h => ?_, fun h => ?_⟩
            · rw [h] at hx; exact absurd hx.1 (by decide)
            · have := Array.contains_iff_mem.mpr h; rw [hx.2] at this; cases this
          simpa using hp
        rw [hbad] at hmem
        simp at hmem
    · simp at ha
  have hc' : (e.verdict.cone.map fun c => (c.problems allowed).isEmpty).getD true = true := by
    cases hco : e.verdict.cone with
    | none => rfl
    | some c =>
      rw [hco] at hc
      simp only at hc
      split at hc
      · rename_i hemp
        simp only [Option.map_some, Option.getD_some]
        rw [Array.isEmpty_iff] at hemp ⊢
        have := congrArg Array.size hemp
        simp only [Array.size_map, Array.size_empty] at this
        exact Array.size_eq_zero_iff.mp this
      · simp at hc
  rw [hs', ha', hc']
  rfl

/-- What a key that audits clean says: unless it is a blueprint `\lean`,
its proof has no trust problems; if it is a typeset block or inline item,
its rendering has no formula that fails to read back; and a check's key is
in the bundle. -/
theorem auditKey_clean {cfg : Config} {b : B} {it : Item} {loc key : String}
    (h : auditKey cfg b it loc key = #[]) :
    (it.kind = .check → (b.find? key).isSome) ∧
    ∀ e, b.find? key = some e →
      (¬(it.kind = .check ∧ it.name = "lean") → trustProblems cfg.allowedAxioms key e = #[]) ∧
      ((it.kind = .block ∨ it.kind = .inline) → it.live = true →
        e.statement.problems (itemView cfg it) = #[]) := by
  unfold auditKey at h
  refine ⟨fun hk => ?_, fun e he => ?_⟩
  · cases hf : b.find? key with
    | some _ => rfl
    | none => rw [hf] at h; simp [hk] at h
  · rw [he] at h
    simp only [Array.append_eq_empty_iff] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hn => ?_, fun hk hl => ?_⟩
    · have : (it.kind == .check && it.name == "lean") = false := by
        simpa using hn
      rw [this] at h1
      simp only [Bool.false_eq_true, ↓reduceIte] at h1
      have := congrArg Array.size h1
      simp only [Array.size_map, Array.size_empty] at this
      exact Array.size_eq_zero_iff.mp this
    · have : ((it.kind == .block || it.kind == .inline) && it.live) = true := by
        rcases hk with hk | hk <;> simp [hk, hl]
      rw [this] at h2
      simp only [↓reduceIte] at h2
      have := congrArg Array.size h2
      simp only [Array.size_map, Array.size_empty] at this
      exact Array.size_eq_zero_iff.mp this

theorem mem_of_zipIdx {α : Type} {xs : Array α} {x : α} {i : Nat} (h : (x, i) ∈ xs.toList.zipIdx) :
    x ∈ xs := by
  have := List.mem_zipIdx_iff_getElem?.mp h
  exact Array.mem_toList_iff.mp (List.mem_of_getElem? this)

/-! ## Theorem 1 -/

/-- **Theorem 1, generated mathematics, of the code that runs.** If the
bundle is true of a world, under the configuration's rule for trusted
proofs, and `check` reports nothing, warnings included, then every block and
`\leaninline` of the document shows a statement Lean proved: its key is
declared and trusted; its view of the statement is the world's rendering
`t`; its region is, after normalisation, `t` as the splicer sets it (the
alias's template and label, the authors' slot text, the file's line
endings); and, if it is typeset, `t` reads back as the statement. -/
theorem checkDoc_block {W : Imprimatur.World Imprimatur.TeX} {doc : Splice.Doc} {b : B} {opts : ApplyOpts}
    {extra : Array String} {diff : Bool}
    (hb : b.True W (Verdict.trusted doc.cfg.allowedAxioms))
    (hc : checkDoc doc b opts extra diff = #[])
    {f : SourceFile} {fi : Nat} (hf : (f, fi) ∈ doc.files.toList.zipIdx)
    {it : Item} {ii : Nat} (hi : (it, ii) ∈ f.scan.items.toList.zipIdx)
    (hk : it.kind = .block ∨ it.kind = .inline) :
    ∃ e S t new, b.find? it.key = some e ∧ W.stmt it.key = some S ∧ W.trusted it.key = true ∧
      W.render (itemView doc.cfg it) S = some t ∧
      renderItem doc.cfg (blockLabels doc) opts (f.src.locString it.start) fi ii it e t = .ok new ∧
      normalize (f.src.slice it.regionStart it.regionEnd) =
        normalize (regionContent doc.cfg opts (f.src.locString it.start) (dominantEol f.src.chars) it new
          (f.src.slice it.regionStart it.regionEnd)).content ∧
      (it.live = true → W.Reads t S) := by
  obtain ⟨hpd, hpc, ha⟩ := checkDoc_parts hc
  obtain ⟨hd, hch⟩ := items_clean hpd hpc hf hi
  obtain ⟨e, t, new, he, hv, hr, hn⟩ := planItem_clean hk hd hch
  obtain ⟨S, hS, hrend, hreads⟩ := Bundle.True.view hb he hv
  have hkey : it.key ∈ it.allKeys := by
    unfold Item.allKeys; rcases hk with hk | hk <;> simp [hk]
  have hclean := (auditKey_clean (keys_clean ha (mem_of_zipIdx hf) (mem_of_zipIdx hi) hkey)).2 e he
  have htrust : W.trusted it.key = true := by
    rw [← (hb it.key e he).verdict]
    apply trusted_of_trustProblems
    apply hclean.1
    rintro ⟨hc', _⟩; rcases hk with hk | hk <;> rw [hk] at hc' <;> cases hc'
  exact ⟨e, S, t, new, he, hS, htrust, hrend, hr, hn, fun hl => hreads (hclean.2 hk hl)⟩

/-- **Theorem 1, references.** If the bundle is true and `check` reports
nothing, every `\leanref` names a declared, trusted statement. -/
theorem checkDoc_ref {W : Imprimatur.World Imprimatur.TeX} {doc : Splice.Doc} {b : B} {opts : ApplyOpts}
    {extra : Array String} {diff : Bool}
    (hb : b.True W (Verdict.trusted doc.cfg.allowedAxioms))
    (hc : checkDoc doc b opts extra diff = #[])
    {f : SourceFile} (hf : f ∈ doc.files) {it : Item} (hi : it ∈ f.scan.items) (hk : it.kind = .ref)
    (he : (b.find? it.key).isSome) :
    ∃ S, W.stmt it.key = some S ∧ W.trusted it.key = true := by
  obtain ⟨_, _, ha⟩ := checkDoc_parts hc
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp he
  have hkey : it.key ∈ it.allKeys := by unfold Item.allKeys; simp [hk]
  have hclean := (auditKey_clean (keys_clean ha hf hi hkey)).2 e he
  obtain ⟨S, hS, _⟩ := (hb it.key e he).statement
  refine ⟨S, hS, ?_⟩
  rw [← (hb it.key e he).verdict]
  apply trusted_of_trustProblems
  apply hclean.1
  rintro ⟨hc', _⟩; rw [hk] at hc'; cases hc'

/-- **Theorem 1, attested prose.** If the bundle is true and `check` reports
nothing, every key of a `\leancheck` names a declared, trusted statement,
whose hash, if the bundle has one, is the statement's. -/
theorem checkDoc_check {W : Imprimatur.World Imprimatur.TeX} {doc : Splice.Doc} {b : B} {opts : ApplyOpts}
    {extra : Array String} {diff : Bool}
    (hb : b.True W (Verdict.trusted doc.cfg.allowedAxioms))
    (hc : checkDoc doc b opts extra diff = #[])
    {f : SourceFile} (hf : f ∈ doc.files) {it : Item} (hi : it ∈ f.scan.items)
    (hk : it.kind = .check) (hn : it.name = "leancheck") {key : String} (hkey : key ∈ it.keys) :
    ∃ e S, b.find? key = some e ∧ W.stmt key = some S ∧ W.trusted key = true ∧
      ∀ h, e.statement.stmtHash = some h → h = W.hash S := by
  obtain ⟨_, _, ha⟩ := checkDoc_parts hc
  have hkey' : key ∈ it.allKeys := by unfold Item.allKeys; simp [hk, hkey]
  have hclean := auditKey_clean (keys_clean ha hf hi hkey')
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (hclean.1 hk)
  obtain ⟨S, hS, hio⟩ := (hb key e he).statement
  refine ⟨e, S, he, hS, ?_, hio.stmtHash⟩
  rw [← (hb key e he).verdict]
  apply trusted_of_trustProblems
  apply (hclean.2 e he).1
  rintro ⟨_, hl⟩; rw [hn] at hl; exact absurd hl (by decide)

/-! ## Blueprint `\leanok`, and the recorded hashes -/

/-- A clean audit, file by file: every item audits clean, and so do its
`\leanok`s. -/
theorem file_clean {doc : Splice.Doc} {b : B} (h : audit doc b = #[]) {f : SourceFile} (hf : f ∈ doc.files) :
    (∀ it ∈ f.scan.items, auditItem doc.cfg b f it = #[]) ∧ auditLeanok doc.cfg b f = #[] := by
  unfold audit at h
  rw [Array.append_eq_empty_iff] at h
  have hF : (fun (ds : Array Splice.Diag) (f : SourceFile) =>
      f.scan.items.foldl (init := ds) (fun ds it => ds ++ auditItem doc.cfg b f it) ++ auditLeanok doc.cfg b f) =
      (fun ds f => ds ++ (f.scan.items.foldl (init := #[]) (fun ds it => ds ++ auditItem doc.cfg b f it) ++
        auditLeanok doc.cfg b f)) := by
    funext ds f
    rw [foldl_array_append, Array.append_assoc]
  have h1 := h.1
  rw [hF, foldl_array_empty] at h1
  have h2 := Array.append_eq_empty_iff.mp (h1 f hf)
  rw [foldl_array_empty] at h2
  exact h2

/-- **Theorem 1, blueprint.** If the bundle is true and `check` reports
nothing, every key of a blueprint `\lean` in an environment marked
`\leanok` names a declared, trusted statement. -/
theorem checkDoc_leanok {W : Imprimatur.World Imprimatur.TeX} {doc : Splice.Doc} {b : B} {opts : ApplyOpts}
    {extra : Array String} {diff : Bool}
    (hb : b.True W (Verdict.trusted doc.cfg.allowedAxioms))
    (hc : checkDoc doc b opts extra diff = #[])
    {f : SourceFile} (hf : f ∈ doc.files) {ok : Item} (hok : ok ∈ f.scan.items) (hko : ok.kind = .leanok)
    (henv : ok.env ≠ 0) {it : Item} (hi : it ∈ f.scan.items) (hk : it.kind = .check) (hn : it.name = "lean")
    (he : it.env = ok.env) {key : String} (hkey : key ∈ it.keys) :
    ∃ S, W.stmt key = some S ∧ W.trusted key = true := by
  obtain ⟨_, _, ha⟩ := checkDoc_parts hc
  have hkey' : key ∈ it.allKeys := by unfold Item.allKeys; simp [hk, hkey]
  obtain ⟨e, hfe⟩ := Option.isSome_iff_exists.mp
    ((auditKey_clean (keys_clean ha hf hi hkey')).1 hk)
  obtain ⟨S, hS, _⟩ := (hb key e hfe).statement
  refine ⟨S, hS, ?_⟩
  rw [← (hb key e hfe).verdict]
  apply trusted_of_trustProblems
  -- The `\leanok`'s audit found nothing for this key.
  have hl := (file_clean ha hf).2
  unfold auditLeanok at hl
  rw [foldl_array_empty] at hl
  have hlo := hl ok (Array.mem_filter.mpr ⟨hok, by simp [hko]⟩)
  unfold leanokDiags at hlo
  have h0 : (ok.env == 0) = false := by simpa using henv
  simp only [h0, Bool.false_eq_true, ↓reduceIte] at hlo
  rw [foldl_array_empty] at hlo
  have hit := hlo it (Array.mem_filter.mpr ⟨hi, by simp [hn, he]⟩)
  rw [foldl_array_empty] at hit
  have hkd := hit key hkey
  unfold leanokKeyDiags at hkd
  rw [hfe] at hkd
  simp only at hkd
  split at hkd
  · rename_i hemp; exact Array.isEmpty_iff.mp hemp
  · simp at hkd

/-- What `hashesOf` gives, of a true bundle: one hash for each key, the
statement hash of the key's statement. -/
theorem hashesOf_true {W : Imprimatur.World Imprimatur.TeX} {tr : Verdict → Bool} {b : B} (hb : b.True W tr) :
    ∀ {ks : List String} {hs : List String}, hashesOf b (·.stmtHash) ks = some hs →
      hs.length = ks.length ∧ ∀ p ∈ ks.zip hs, ∃ S, W.stmt p.1 = some S ∧ p.2 = W.hash S
  | [], hs, h => by simp [hashesOf] at h; subst h; simp
  | k :: ks, hs, h => by
    simp only [hashesOf, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨e, he, h', hh, hs', hrest, hcons⟩ := h
    simp only [Option.pure_def, Option.some.injEq] at hcons
    subst hcons
    obtain ⟨hlen, hall⟩ := hashesOf_true hb hrest
    obtain ⟨S, hS, hio⟩ := (hb k e he).statement
    refine ⟨by simp [hlen], ?_⟩
    intro p hp
    simp only [List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨S, hS, hio.stmtHash h' hh⟩
    · exact hall p hp

/-- **Theorem 1, the recorded hash.** If the bundle is true and `check`
reports nothing, a `\leancheck` that records `stmt=r` records the statement
hashes of its keys' statements, as `shortOf` writes them: the first 12
digits of the one hash, or of the hash of all of them. -/
theorem checkDoc_stmt {W : Imprimatur.World Imprimatur.TeX} {doc : Splice.Doc} {b : B} {opts : ApplyOpts}
    {extra : Array String} {diff : Bool}
    (hb : b.True W (Verdict.trusted doc.cfg.allowedAxioms))
    (hc : checkDoc doc b opts extra diff = #[])
    {f : SourceFile} (hf : f ∈ doc.files) {it : Item} (hi : it ∈ f.scan.items)
    (hk : it.kind = .check) (hn : it.name = "leancheck") {r : String} (hr : it.opt? "stmt" = some r) :
    ∃ hs, r = shortOf hs ∧ hs.length = it.keys.size ∧
      ∀ p ∈ it.keys.toList.zip hs, ∃ S, W.stmt p.1 = some S ∧ p.2 = W.hash S := by
  obtain ⟨_, _, ha⟩ := checkDoc_parts hc
  have hitem := (file_clean ha hf).1 it hi
  unfold auditItem at hitem
  rw [Array.append_eq_empty_iff] at hitem
  obtain ⟨hkeys, hdrift⟩ := hitem
  rw [foldl_array_empty] at hkeys
  have hfound : ∀ k ∈ it.keys, (b.find? k).isSome := by
    intro k hkm
    exact (auditKey_clean (hkeys k (by unfold Item.allKeys; simp [hk, hkm]))).1 hk
  unfold driftDiags at hdrift
  have hck : (it.kind == .check && it.name == "leancheck") = true := by simp [hk, hn]
  simp only [hck, ↓reduceIte] at hdrift
  rw [hr] at hdrift
  cases hch : checkHashes b it.keys with
  | none =>
    rw [hch] at hdrift
    simp only at hdrift
    have hallk : (it.keys.all fun k => (b.find? k).isSome) = true := by
      simpa [Array.all_eq_true] using fun i hi' => hfound _ (Array.getElem_mem hi')
    simp only [hallk, ↓reduceIte] at hdrift
    simp at hdrift
  | some p =>
    rw [hch] at hdrift
    obtain ⟨stmt, sig⟩ := p
    simp only at hdrift
    have hrs : r = stmt := by
      cases hne : (r != stmt) with
      | true => rw [hne] at hdrift; simp at hdrift
      | false => simpa using hne
    unfold checkHashes at hch
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hch
    obtain ⟨stmts, hstmts, sigs, _, hpair⟩ := hch
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hpair
    obtain ⟨hlen, hall⟩ := hashesOf_true hb hstmts
    refine ⟨stmts, by rw [hrs, ← hpair.1], by simpa using hlen, hall⟩

end SpliceModel.Theorem1
