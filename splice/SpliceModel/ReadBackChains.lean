/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpliceModel.ReadBack

/-!
# Chains of coercions: the rule against unbounded chains

The parser's grammar (`Exp`) applies a hidden coercion only where the chain
rule allows it (`Imprimatur.Validate.Chain`): no coercion whose argument
sort is on the chain already, and no cast below a cast. The unrestricted
grammar (`ExpFree`) applies one whatever the chain. Two facts relate them
(docs/coercion-chains.md, route A):

- **The rule only narrows** (`Exp.free`): every reading in the parser's
  grammar is a reading in the unrestricted one, so the theorems about
  `Exp` are about a part of what Lean's types allow.
- **It narrows on purpose** (`pun_free`, `pun_rule`): with `Option.some`
  hidden, the unrestricted grammar reads `g ( x )` both as `g[x]`, through
  `some (some (some x))`, and as `h[x]`, so the text is ambiguous; the
  parser's grammar reads `x` as no `Option(Option(Option(Nat)))`, so `g[x]`
  is not a reading of it. What makes that sound is that the renderer obeys
  the same rule: it shows a coercion the rule would not read, so
  `g (some (some (some x)))` never prints as `g(x)`.
-/

namespace SpliceModel

open Imprimatur.Validate

section
variable {A : SortAlgebra} {g : Grammar} {ts : Array String}

/-- The rule only narrows: a derivation in the parser's grammar is one in
the unrestricted grammar. -/
theorem Reads.free {q : Question} {a : Answer} (h : Reads A g ts false q a) : Reads A g ts true q a := by
  induction h with
  | prod hk hvar hcompat hex hcoe hprec hij _ hc ih => exact .prod hk hvar hcompat hex hcoe hprec hij ih hc
  | coe hk hvar hcompat hcoe _ hb _ hc ih => exact .coe hk hvar hcompat hcoe (Or.inl rfl) hb ih hc
  | paren h3 hl hr _ ih => exact .paren h3 hl hr ih
  | group h3 hl hr _ ih => exact .group h3 hl hr ih
  | done hpos => exact .done hpos
  | tok hb hij ht _ ih => exact .tok hb hij ht ih
  | hole hb him hmj _ _ ih₁ ih₂ => exact .hole hb him hmj ih₁ ih₂
  | var hb him hmj hv _ ih => exact .var hb him hmj hv ih
  | tail hb him hmj _ _ ih₁ ih₂ => exact .tail hb him hmj ih₁ ih₂
  | nil => exact .nil
  | more hl hij _ ih => exact .more hl hij ih

/-- A reading in the parser's grammar is a reading in the unrestricted one. -/
theorem Exp.free {s : String} {prec : Nat} {excl : Option Nat} {ch : Chain} {i j : Nat} {rd : Reading}
    {σ : String} (h : Exp A g ts s prec excl ch i j rd σ) : ExpFree A g ts s prec excl ch i j rd σ :=
  Reads.free h

end

/-! ## The counterexample -/

namespace Pun

/-- `Option` of a sort, for the sorts the counterexample meets. -/
def option : String → String
  | "Nat" => "Option(Nat)"
  | "Option(Nat)" => "Option(Option(Nat))"
  | "Option(Option(Nat))" => "Option(Option(Option(Nat)))"
  | _ => "Option(*)"

/-- A toy algebra of sorts, total and small: `?α` is the one type
variable, and `Option(?α)` the one sort that mentions it. -/
def toy : SortAlgebra where
  compat a b := b == "*" || a == b ||
    (a == "Option(?α)" && [option "Nat", option (option "Nat"), option (option (option "Nat")), "Option(*)"].contains b)
  expected env s :=
    let α := ((env.find? (·.1 == "?α")).map (·.2)).getD "*"
    if s == "?α" then α else if s == "Option(?α)" then option α else s
  bind env s σ := if s == "?α" then env.push ("?α", σ) else env
  anySort s := s == "*"

/-- `x : Nat`. -/
def px : Imprimatur.Validate.Prod := { name := "x", sort := "Nat", prec := 1024, syms := [.tok "x"] }

/-- `Option.some`, hidden. -/
def psome : Imprimatur.Validate.Prod :=
  { name := "Option.some", sort := "Option(?α)", prec := 1024, syms := [.hole "?α" 0], coercion := true }

/-- `g ( _ )`, of an `Option(Option(Option(Nat)))`. -/
def pg : Imprimatur.Validate.Prod :=
  { name := "g", sort := "Prop", prec := 1024, syms := [.tok "g", .tok "(", .hole "Option(Option(Option(Nat)))" 0, .tok ")"] }

/-- `h`, which prints as `g ( _ )` too, of a `Nat`. -/
def ph : Imprimatur.Validate.Prod :=
  { name := "h", sort := "Prop", prec := 1024, syms := [.tok "g", .tok "(", .hole "Nat" 0, .tok ")"] }

/-- The grammar of the counterexample, compiled. -/
def G : Grammar :=
  { prods := #[(px, #[.tok "x"]), (psome, #[.hole "?α" 0 none]),
      (pg, #[.tok "g", .tok "(", .hole "Option(Option(Option(Nat)))" 0 none, .tok ")"]),
      (ph, #[.tok "g", .tok "(", .hole "Nat" 0 none, .tok ")"])],
    lists := #[] }

/-- The text `g ( x )`. -/
def T : Array String := #["g", "(", "x", ")"]

/-- `Option(Option(Option(Nat)))`. -/
def O3 : String := "Option(Option(Option(Nat)))"

/-- The reading `g[x]`. -/
def gx : Reading := mkReading "g" none #[mkReading "x" none #[]]

/-- The reading `h[x]`. -/
def hx : Reading := mkReading "h" none #[mkReading "x" none #[]]

/-- `x`, read at a sort `s` that its own is compatible with. -/
theorem x_reads {free : Bool} {s : String} {ch : Chain} (hs : toy.compat "Nat" s = true) :
    Reads toy G T free (.expr s 0 none ch 2 3) (.one (mkReading "x" none #[]) "Nat") :=
  .prod (kp := 0) (pr := px) (body := #[.tok "x"]) (env := #[]) (p := 0) (i := 2) (j := 3) rfl rfl hs (by simp) rfl (by decide) (by decide)
    (.tok rfl (by decide) rfl (.done rfl)) hs

/-- In the unrestricted grammar `x` reads as an `Option(Option(Option(Nat)))`,
through three hidden `some`s. -/
theorem x_reads_O3 {ch : Chain} :
    Reads toy G T true (.expr O3 0 none ch 2 3) (.one (mkReading "x" none #[]) O3) :=
  .coe (kp := 1) (pr := psome) (body := #[.hole "?α" 0 none]) rfl rfl (by decide) rfl (Or.inl rfl) rfl
    (.coe (kp := 1) (pr := psome) (body := #[.hole "?α" 0 none]) rfl rfl (by decide) rfl (Or.inl rfl) rfl
      (.coe (kp := 1) (pr := psome) (body := #[.hole "?α" 0 none]) rfl rfl (by decide) rfl (Or.inl rfl) rfl
        (x_reads (by decide)) (by decide))
      (by decide))
    (by decide)

/-- The pun, in the unrestricted grammar: `g ( x )` reads as `g[x]`. -/
theorem pun_free_g : ExpFree toy G T "Prop" 0 none G.chain0 0 4 gx "Prop" :=
  .prod (kp := 2) (pr := pg) (i := 0) (j := 4) (body := #[.tok "g", .tok "(", .hole O3 0 none, .tok ")"]) (env := toy.bind #[] O3 O3)
    rfl rfl (by decide) (by simp) rfl (by decide) (by decide)
    (.tok rfl (by decide) rfl (.tok rfl (by decide) rfl
      (.hole (m := 3) rfl (by decide) (by decide) x_reads_O3
        (.tok rfl (by decide) rfl (.done rfl)))))
    (by decide)

/-- And as `h[x]`, in either grammar. -/
theorem pun_h {free : Bool} : Reads toy G T free (.expr "Prop" 0 none G.chain0 0 4) (.one hx "Prop") :=
  .prod (kp := 3) (pr := ph) (i := 0) (j := 4) (body := #[.tok "g", .tok "(", .hole "Nat" 0 none, .tok ")"]) (env := toy.bind #[] "Nat" "Nat")
    rfl rfl (by decide) (by simp) rfl (by decide) (by decide)
    (.tok rfl (by decide) rfl (.tok rfl (by decide) rfl
      (.hole (m := 3) rfl (by decide) (by decide) (x_reads (by decide))
        (.tok rfl (by decide) rfl (.done rfl)))))
    (by decide)

/-- The unrestricted grammar reads `g ( x )` two ways: the text is
ambiguous there. -/
theorem pun_free : ExpFree toy G T "Prop" 0 none G.chain0 0 4 gx "Prop" ∧
    ExpFree toy G T "Prop" 0 none G.chain0 0 4 hx "Prop" :=
  ⟨pun_free_g, pun_h⟩

/-- The productions of `G`. -/
theorem G_prods {k : Nat} {pr : Imprimatur.Validate.Prod} {body : Array ASym} (h : G.prods[k]? = some (pr, body)) :
    (pr = px ∧ body = #[.tok "x"]) ∨ (pr = psome ∧ body = #[.hole "?α" 0 none]) ∨
    (pr = pg ∧ body = #[.tok "g", .tok "(", .hole O3 0 none, .tok ")"]) ∨
    (pr = ph ∧ body = #[.tok "g", .tok "(", .hole "Nat" 0 none, .tok ")"]) := by
  rcases k with _ | _ | _ | _ | k <;> simp [G] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp [O3]

/-- Under the rule, `x` read below a hidden `some` (a chain that has the
unknown sort on it) is read by a production, not by another `some`: its
sort is `Nat`, or `Prop` (which no reading has, but which the inversion
does not rule out). -/
theorem x_below_some {s : String} {p : Nat} {excl : Option Nat} {ch : Chain} {r : Reading} {σ : String}
    (hc : ch.count = none) (hv : ch.visited.contains "*" = true)
    (h : Reads toy G T false (.expr s p excl ch 2 3) (.one r σ)) : σ = "Nat" ∨ σ = "Prop" := by
  cases h with
  | prod hk _ _ _ hcoe =>
    rcases G_prods hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; simp [toy, px]
    · simp [psome] at hcoe
    · right; simp [toy, pg]
    · right; simp [toy, ph]
  | coe hk _ _ hcoe hallow hb =>
    rcases G_prods hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [px] at hcoe
    · simp at hb
      obtain ⟨rfl, -, -⟩ := hb
      simp [Chain.allows, hc, toy] at hallow
      exact absurd (by simpa using hv) hallow.1
    · simp [pg] at hcoe
    · simp [ph] at hcoe
  | paren h3 => simp at h3
  | group h3 => simp at h3

/-- Under the rule, `x` has no reading as an `Option(Option(Option(Nat)))`:
one hidden `some` is allowed, a second is not, and one does not reach. -/
theorem x_not_O3 {r : Reading} {σ : String} :
    ¬ Reads toy G T false (.expr O3 0 none G.chain0 2 3) (.one r σ) := by
  intro h
  cases h with
  | prod hk _ hcompat _ hcoe =>
    rcases G_prods hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | simp [psome] at hcoe | simp [toy, px, pg, ph, O3, option] at hcompat
  | coe hk _ _ hcoe _ hb hexp hc =>
    rcases G_prods hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [px] at hcoe
    · simp at hb
      obtain ⟨rfl, -, -⟩ := hb
      rcases x_below_some (by rfl) (by simp [Chain.push, G, Grammar.chain0, toy, chainWith]) hexp with rfl | rfl <;>
        simp [toy, psome, O3, option] at hc
    · simp [pg] at hcoe
    · simp [ph] at hcoe
  | paren h3 => simp at h3
  | group h3 => simp at h3

/-- `)` stands at 3 only. -/
theorem close_at {m : Nat} (h : T[m]? = some ")") : m = 3 := by
  rcases m with _ | _ | _ | _ | m <;> simp [T] at h ⊢

/-- Under the rule, every reading of `g ( x )` is made by `h`: the hole of
`g` asks for an `Option(Option(Option(Nat)))`, and `x` is not one. -/
theorem only_h {r : Reading} {σ : String} (h : Exp toy G T "Prop" 0 none G.chain0 0 4 r σ) :
    ∃ cs, r = mkReading "h" none cs := by
  cases h with
  | prod hk _ _ _ hcoe _ _ hseq =>
    rcases G_prods hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · cases hseq with
      | tok hb _ ht => simp at hb; subst hb; simp [T] at ht
      | hole hb => simp at hb
      | var hb => simp at hb
      | tail hb => simp at hb
    · simp [psome] at hcoe
    · -- `g`, `(`, then the hole, which must end where `)` stands.
      cases hseq with
      | hole hb => simp at hb
      | var hb => simp at hb
      | tail hb => simp at hb
      | tok _ _ _ hseq =>
      cases hseq with
      | hole hb => simp at hb
      | var hb => simp at hb
      | tail hb => simp at hb
      | tok _ _ _ hseq =>
      cases hseq with
      | tok hb => simp at hb
      | var hb => simp at hb
      | tail hb => simp at hb
      | hole hb him hmj hexp hrest =>
        simp at hb
        obtain ⟨rfl, rfl, rfl⟩ := hb
        cases hrest with
        | done hpos => simp at hpos
        | hole hb => simp at hb
        | var hb => simp at hb
        | tail hb => simp at hb
        | tok hb _ ht =>
          simp at hb
          subst hb
          -- `)` stands at 3 only, so the hole is `x`.
          obtain rfl := close_at ht
          have he : toy.expected #[] O3 = O3 := by simp [toy, O3]
          exact absurd (by simpa [he] using hexp) x_not_O3
    · exact ⟨_, rfl⟩
  | coe hk _ hcompat hcoe =>
    rcases G_prods hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      first | simp [px, pg, ph] at hcoe | simp [toy, psome, option] at hcompat
  | paren _ hl => simp [T] at hl
  | group _ hl => simp [T] at hl

/-- The pun, closed: under the rule, `g ( x )` does not read as `g[x]`, though
the unrestricted grammar reads it so (`pun_free`). -/
theorem pun_rule {σ : String} : ¬ Exp toy G T "Prop" 0 none G.chain0 0 4 gx σ := by
  intro h
  obtain ⟨cs', hr⟩ := only_h h
  simp [gx, mkReading, appNames] at hr

end Pun

end SpliceModel
