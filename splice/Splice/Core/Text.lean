/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The text kernel

Text as a list of characters, which is what the proofs about the splicer
reason about (docs/verified-splicer.md). Each function is defined simply,
by structural recursion, and the theorems are about that definition. Where
the recursion is once per character, so that its depth would be the length
of a file, a tail-recursive version runs instead: a `@[csimp]` theorem
proves the two equal, and the compiler uses it to replace the one by the
other. Nothing here is `partial`.
-/

namespace Splice.Core

/-! ## Line endings -/

/-- Replace `\r\n` and lone `\r` by `\n`. -/
def toLf : List Char → List Char
  | [] => []
  | [c] => [if c = '\r' then '\n' else c]
  | c :: tl@(d :: cs) =>
    if c = '\r' then
      if d = '\n' then '\n' :: toLf cs else '\n' :: toLf tl
    else c :: toLf tl

/-- `toLf`, tail-recursively: the characters done so far, reversed. -/
def toLfTR.go : List Char → List Char → List Char
  | [], acc => acc.reverse
  | [c], acc => ((if c = '\r' then '\n' else c) :: acc).reverse
  | c :: tl@(d :: cs), acc =>
    if c = '\r' then
      if d = '\n' then go cs ('\n' :: acc) else go tl ('\n' :: acc)
    else go tl (c :: acc)

/-- `toLf`, tail-recursively. -/
def toLfTR (cs : List Char) : List Char := toLfTR.go cs []

theorem toLfTR.go_eq : ∀ (cs acc : List Char), toLfTR.go cs acc = acc.reverse ++ toLf cs
  | [], acc => by simp [toLfTR.go, toLf]
  | [c], acc => by simp [toLfTR.go, toLf]
  | c :: d :: cs, acc => by
    simp only [toLfTR.go, toLf]
    split
    · split
      · rw [toLfTR.go_eq cs]; simp
      · rw [toLfTR.go_eq (d :: cs)]; simp
    · rw [toLfTR.go_eq (d :: cs)]; simp

@[csimp] theorem toLf_eq_toLfTR : @toLf = @toLfTR := by
  funext cs; simp [toLfTR, toLfTR.go_eq]

/-- Write each `\n` as `\r\n`. -/
def withCrlf : List Char → List Char
  | [] => []
  | c :: cs => if c = '\n' then '\r' :: '\n' :: withCrlf cs else c :: withCrlf cs

/-- `withCrlf`, tail-recursively: the characters done so far, reversed. -/
def withCrlfTR.go : List Char → List Char → List Char
  | [], acc => acc.reverse
  | c :: cs, acc => if c = '\n' then go cs ('\n' :: '\r' :: acc) else go cs (c :: acc)

/-- `withCrlf`, tail-recursively. -/
def withCrlfTR (cs : List Char) : List Char := withCrlfTR.go cs []

theorem withCrlfTR.go_eq : ∀ (cs acc : List Char), withCrlfTR.go cs acc = acc.reverse ++ withCrlf cs
  | [], acc => by simp [withCrlfTR.go, withCrlf]
  | c :: cs, acc => by
    simp only [withCrlfTR.go, withCrlf]
    split <;> (rw [withCrlfTR.go_eq cs]; simp)

@[csimp] theorem withCrlf_eq_withCrlfTR : @withCrlf = @withCrlfTR := by
  funext cs; simp [withCrlfTR, withCrlfTR.go_eq]

/-- How many line endings are `\r\n`, and how many a lone `\n`, counted on
from `crlf` and `lf`. -/
def eolCounts : List Char → Nat → Nat → Nat × Nat
  | [], crlf, lf => (crlf, lf)
  | [c], crlf, lf => if c = '\n' then (crlf, lf + 1) else (crlf, lf)
  | c :: tl@(d :: cs), crlf, lf =>
    if c = '\r' ∧ d = '\n' then eolCounts cs (crlf + 1) lf
    else if c = '\n' then eolCounts tl crlf (lf + 1)
    else eolCounts tl crlf lf

/-- Whether a text mostly ends its lines with `\r\n`: strictly more often
than with a lone `\n`. -/
def mostlyCrlf (cs : List Char) : Bool :=
  let (crlf, lf) := eolCounts cs 0 0
  crlf > lf

/-! ## Lines -/

/-- Put text at the front of the first line. -/
def prependFirst (p : List Char) : List (List Char) → List (List Char)
  | [] => [p]
  | l :: ls => (p ++ l) :: ls

/-- The lines of a text, split at each `\n`; there is always at least one. -/
def lines : List Char → List (List Char)
  | [] => [[]]
  | c :: cs => if c = '\n' then [] :: lines cs else prependFirst [c] (lines cs)

/-- `lines`, tail-recursively: the current line, reversed, and the lines
done, reversed. -/
def linesTR.go : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => (cur.reverse :: acc).reverse
  | c :: cs, cur, acc => if c = '\n' then go cs [] (cur.reverse :: acc) else go cs (c :: cur) acc

/-- `lines`, tail-recursively. -/
def linesTR (cs : List Char) : List (List Char) := linesTR.go cs [] []

theorem prependFirst_append (p q : List Char) (ls : List (List Char)) :
    prependFirst p (prependFirst q ls) = prependFirst (p ++ q) ls := by
  cases ls <;> simp [prependFirst]

theorem lines_ne_nil : ∀ (cs : List Char), lines cs ≠ []
  | [] => by simp [lines]
  | c :: cs => by
    simp only [lines]
    split
    · simp
    · cases h : lines cs with
      | nil => exact absurd h (lines_ne_nil cs)
      | cons l ls => simp [prependFirst]

theorem prependFirst_nil {ls : List (List Char)} (h : ls ≠ []) : prependFirst [] ls = ls := by
  cases ls with
  | nil => exact absurd rfl h
  | cons l ls => simp [prependFirst]

theorem linesTR.go_eq : ∀ (cs cur : List Char) (acc : List (List Char)),
    linesTR.go cs cur acc = acc.reverse ++ prependFirst cur.reverse (lines cs)
  | [], cur, acc => by simp [linesTR.go, lines, prependFirst]
  | c :: cs, cur, acc => by
    simp only [linesTR.go, lines]
    split
    · rw [linesTR.go_eq cs, List.reverse_nil, prependFirst_nil (lines_ne_nil cs)]; simp [prependFirst]
    · rw [linesTR.go_eq cs, prependFirst_append]; simp

@[csimp] theorem lines_eq_linesTR : @lines = @linesTR := by
  funext cs; simp [linesTR, linesTR.go_eq, prependFirst_nil (lines_ne_nil cs)]

/-! ## Normalisation -/

/-- A space or a tab. -/
def isBlank (c : Char) : Bool := c == ' ' || c == '\t'

/-- A line without its trailing spaces and tabs. -/
def rstrip (l : List Char) : List Char := (l.reverse.dropWhile isBlank).reverse

/-- Normalise text for comparison and checksums (DESIGN §10.2): line endings
become `\n`, trailing spaces and tabs are removed from every line, and blank
lines at the start and end are dropped. -/
def normalize (cs : List Char) : List Char :=
  let ls := (lines (toLf cs)).map rstrip
  let ls := ls.dropWhile List.isEmpty
  let ls := (ls.reverse.dropWhile List.isEmpty).reverse
  ['\n'].intercalate ls

/-! ## Laws -/

/-- `toLf` leaves no `\r`. -/
theorem not_mem_toLf : ∀ (cs : List Char), '\r' ∉ toLf cs
  | [] => by simp [toLf]
  | [c] => by
    simp only [toLf]
    split
    · simp
    · rename_i h; simpa using Ne.symm h
  | c :: d :: cs => by
    simp only [toLf]
    split
    · split
      · simpa using not_mem_toLf cs
      · simpa using not_mem_toLf (d :: cs)
    · rename_i h; simpa [Ne.symm h] using not_mem_toLf (d :: cs)

/-- Text with no `\r` is its own `toLf`. -/
theorem toLf_of_not_mem : ∀ {cs : List Char}, '\r' ∉ cs → toLf cs = cs
  | [], _ => by simp [toLf]
  | [c], h => by
    have hc : c ≠ '\r' := fun e => h (e ▸ List.mem_cons_self ..)
    simp [toLf, hc]
  | c :: d :: cs, h => by
    have hc : c ≠ '\r' := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : '\r' ∉ d :: cs := fun m => h (List.mem_cons_of_mem _ m)
    simp only [toLf, hc, ite_false, toLf_of_not_mem hcs]

/-- `toLf` is idempotent. -/
theorem toLf_toLf (cs : List Char) : toLf (toLf cs) = toLf cs :=
  toLf_of_not_mem (not_mem_toLf cs)

/-- Writing `\r\n` line endings, then reading them as `\n`, gives back text
that had no `\r`. -/
theorem toLf_withCrlf : ∀ {cs : List Char}, '\r' ∉ cs → toLf (withCrlf cs) = cs
  | [], _ => by simp [withCrlf, toLf]
  | c :: cs, h => by
    have hc : c ≠ '\r' := fun e => h (e ▸ List.mem_cons_self ..)
    have hcs : '\r' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    simp only [withCrlf]
    split
    · rename_i hn; subst hn; simp [toLf, toLf_withCrlf hcs]
    · cases hw : withCrlf cs with
      | nil =>
        have h0 := toLf_withCrlf hcs
        rw [hw] at h0
        simp only [toLf] at h0
        subst h0
        simp [toLf, hc]
      | cons e es => simp only [toLf, hc, ite_false]; rw [← hw, toLf_withCrlf hcs]

end Splice.Core
