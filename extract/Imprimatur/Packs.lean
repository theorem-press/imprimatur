/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Notation

/-!
# Notation packs

Rules shipped with imprimatur (DESIGN §7.5), selected with `notation_packs`
in `imprimatur.toml`; all five are selected by default. They name constants
rather than elaborate them, so imprimatur needs no library to define them: a
rule whose constant isn't in the environment is dropped when the rules are
assembled (`Entry.renderCtx`), so it costs the read-back grammar nothing.
Every rule is used by a fixture's golden bundle: the `Notation` fixture for
the first four packs, and `MathlibPack`, which stubs Mathlib's names with
their explicit arities, for `mathlib`.

| Pack | Covers |
|---|---|
| `core` | equality, arithmetic, order relations, numerals, `Nat.succ`, composition, pairs, `ℕ`, `ℤ`, `ℚ`, `∣`, gcd and lcm of naturals, injective and surjective, Booleans, and coercions, which are not shown |
| `logic` | `∧`, `∨`, `¬`, `↔`, `True`, `False` (`∀`, `∃` and `→` are built in) |
| `sets` | `∈`, `⊆`, `⊂`, `∪`, `∩`, `\`, `∅`, singletons, `{a, b}` and `insert` |
| `order` | `max`, `min` |
| `mathlib` | what the sweep of formal-conjectures (2026-11-21) found left bare most often: `ℝ`, `ℂ`, the coercions `DFunLike.coe`, `Rat.cast`, `NNReal.toReal`, `PNat.val`, `Real.toEReal`; `log`, `exp`, `√`, `π`, `sin`, `cos`, `log_b`, `ℜ`, `ℑ`, `|x|`, `‖x‖`, `n!`, binomials, `φ`, `π(n)`, floors and ceilings; cardinalities `|s|`; primality, parity, irrationality, finiteness, monotonicity, coprimality, squarefreeness, congruences of integers; intervals, set-builder notation, `{a, …, b}`, filtered finsets; sums and products over finsets and series; limits and "for all sufficiently large" along `atTop`; graphs (`χ`, `Δ`, `δ`, `ω`, `K_n`, `C_n`, adjacency, connectedness); polynomial evaluation, `X`, degree; `ℤ/nℤ` |

Precedences follow Lean's: 50 for relations, 65 for `+`, 70 for `*`, 75 for
`^`, 35 for `∧`, 30 for `∨`, 20 for `↔`.
-/

namespace Imprimatur.Packs

open Lean

/-- A rule over a constant's explicit arguments, named `#a`, `#b`, … in order.
Packs are not elaborated, so the sorts the validator reads them at
(DESIGN §18.3) are given: what the rule renders, and its arguments. -/
def rule (pack : String) (head : Name) (arity : Nat) (template : String)
    (prec : Nat := 1024) (assoc : String := "left") (breakBefore : Bool := false)
    (sort : String := "*") (holes : String := "*") : NotationRule :=
  let vars := #[`a, `b, `c, `d].extract 0 arity
  { pat := .app head (vars.map .var), template, prec, assoc, breakBefore,
    origin := s!"pack {pack}", sort, holeSorts := vars.map (·, holes) }

/-- A rule over a pattern with binders or nested constants, for variables
named in the template; `holes` gives the sorts of those with a known one. -/
def rule' (pack : String) (pat : Pat) (template : String) (prec : Nat := 1024)
    (assoc : String := "left") (sort : String := "*") (holes : Array (Name × String) := #[]) :
    NotationRule :=
  { pat, template, prec, assoc, origin := s!"pack {pack}", sort, holeSorts := holes }

/-- `fun x => body`, as a pattern. -/
def lam (x body : Name) : Pat := .lam x (.var body)

/-- A class applied to a type, written as a sentence, `α \text{ is …}`: an
instance binder of it is then a hypothesis the paper states (DESIGN §7.6).
Its sort is `Sort*`, a class being a type or a proposition. -/
def classRule (pack : String) (head : Name) (what : String) : NotationRule :=
  rule pack head 1 s!"#a \\text\{ is {what}}" 50 (sort := "Sort*") (holes := "Sort")

/-- A class of two types, likewise; the template names them `#a` and `#b`. -/
def classRule2 (pack : String) (head : Name) (template : String) : NotationRule :=
  rule pack head 2 template 50 (sort := "Sort*") (holes := "Sort")

/-- The `core` pack. -/
def core : Array NotationRule := #[
  rule "core" ``Eq 2 "#a = #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``Ne 2 "#a \\ne #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  -- Arithmetic is homogeneous as Lean uses it (`Add α` gives `HAdd α α α`),
  -- so an operation is of its operands' sort, and `n / 2` of naturals is a
  -- natural, not also the floor of a real. A cast operand is read as the
  -- unknown sort, which binds nothing, so `↑n + x` still reads.
  rule "core" ``HAdd.hAdd 2 "#a + #b" 65 (sort := "?α") (holes := "?α"),
  rule "core" ``HSub.hSub 2 "#a - #b" 65 (sort := "?α") (holes := "?α"),
  rule "core" ``HMul.hMul 2 "#a \\cdot #b" 70 (sort := "?α") (holes := "?α"),
  -- Division of natural numbers rounds down, so it is written `⌊a/b⌋` with
  -- the fraction stacked: a reader takes `n^2 / 4` for a fraction, which it
  -- is not; and `⌊a / b⌋` with a slash is the floor of a real division (the
  -- `mathlib` pack's `Int.floor`), which a cast operand would let this read
  -- as too. The braces keep the operands' parentheses needless.
  rule' "core" (.constrained (.app ``HDiv.hDiv #[.var `a, .var `b]) #[(0, .lit (mkConst ``Nat))])
    "\\lfloor \\tfrac{#a}{#b} \\rfloor" (sort := "Nat") (holes := #[(`a, "Nat"), (`b, "Nat")]),
  rule "core" ``HDiv.hDiv 2 "#a / #b" 70 (sort := "?α") (holes := "?α"),
  rule "core" ``HMod.hMod 2 "#a \\bmod #b" 70 (sort := "?α") (holes := "?α"),
  { rule "core" ``HPow.hPow 2 "#a^{#b}" 75 "right" (sort := "?α") with holeSorts := #[(`a, "?α"), (`b, "*")] },
  rule "core" ``Neg.neg 1 "-#a" 75 (sort := "?α") (holes := "?α"),
  rule "core" ``LT.lt 2 "#a < #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``LE.le 2 "#a \\le #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``GT.gt 2 "#a > #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  rule "core" ``GE.ge 2 "#a \\ge #b" 50 "none" true (sort := "Prop") (holes := "?α"),
  -- Divisibility is between data (`!`), never propositions: `{p ∣ q}` does
  -- not read as the singleton of `p` dividing the proposition `q`.
  rule "core" ``Dvd.dvd 2 "#a \\mid #b" 50 "none" true (sort := "Prop") (holes := "!"),
  rule "core" ``OfNat.ofNat 1 "#a" (holes := "Nat"),
  -- `n + 1` is `Nat.succ n` by definition, and Lean writes it so.
  { rule "core" ``Nat.succ 1 "#a + 1" 65 (sort := "Nat") (holes := "Nat") with synonym := true },
  rule "core" ``Function.comp 2 "#a \\circ #b" 90,
  rule "core" ``Prod.mk 2 "(#a, #b)" (sort := "Prod"),
  rule "core" ``Nat 0 "\\mathbb{N}" (sort := "Sort"),
  rule "core" ``Int 0 "\\mathbb{Z}" (sort := "Sort"),
  rule "core" `Rat 0 "\\mathbb{Q}" (sort := "Sort"),
  rule "core" ``Nat.cast 1 "#a" (holes := "Nat"),
  rule "core" ``Int.cast 1 "#a" (holes := "Int"),
  rule "core" ``Subtype.val 1 "#a" (holes := "Subtype"),
  rule "core" ``Nat.gcd 2 "\\gcd(#a, #b)" (sort := "Nat") (holes := "Nat"),
  rule "core" ``Nat.lcm 2 "\\operatorname{lcm}(#a, #b)" (sort := "Nat") (holes := "Nat"),
  rule "core" `Function.Injective 1 "#a \\text{ is injective}" 50 (sort := "Prop"),
  rule "core" `Function.Surjective 1 "#a \\text{ is surjective}" 50 (sort := "Prop"),
  -- A class of core Lean, so that an instance binder `[Nonempty α]` is a
  -- hypothesis the paper states (DESIGN §7.6). `[NeZero n]` needs no rule: a
  -- class in `Prop` with one field is that field's statement, `n ≠ 0`.
  classRule "core" ``Nonempty "nonempty",
  rule "core" ``Bool.true 0 "\\mathrm{true}",
  rule "core" ``Bool.false 0 "\\mathrm{false}"]

/-- The `logic` pack. -/
def logic : Array NotationRule := #[
  rule "logic" ``And 2 "#a \\wedge #b" 35 "right" true (sort := "Prop") (holes := "Prop"),
  rule "logic" ``Or 2 "#a \\vee #b" 30 "right" true (sort := "Prop") (holes := "Prop"),
  rule "logic" ``Not 1 "\\neg #a" 40 (sort := "Prop") (holes := "Prop"),
  rule "logic" ``Iff 2 "#a \\iff #b" 20 "none" true (sort := "Prop") (holes := "Prop"),
  rule "logic" ``True 0 "\\top" (sort := "Prop"),
  rule "logic" ``False 0 "\\bot" (sort := "Prop")]

/-- The `sets` pack. `Membership.mem` takes the collection first. A set
literal `{a, b}` is `insert a {b}`; a longer one, `insert a s`, is written
`{a} ∪ s`. -/
def sets : Array NotationRule := #[
  { rule "sets" ``Membership.mem 2 "#b \\in #a" 50 "none" (sort := "Prop") with },
  rule "sets" ``HasSubset.Subset 2 "#a \\subseteq #b" 50 "none" (sort := "Prop") (holes := "?α"),
  rule "sets" ``HasSSubset.SSubset 2 "#a \\subset #b" 50 "none" (sort := "Prop") (holes := "?α"),
  rule "sets" ``Union.union 2 "#a \\cup #b" 65 (sort := "?α") (holes := "?α"),
  rule "sets" ``Inter.inter 2 "#a \\cap #b" 70 (sort := "?α") (holes := "?α"),
  rule "sets" ``SDiff.sdiff 2 "#a \\setminus #b" 70 (sort := "?α") (holes := "?α"),
  rule "sets" ``EmptyCollection.emptyCollection 0 "\\emptyset",
  rule "sets" ``Singleton.singleton 1 "\\{#a\\}",
  rule' "sets" (.app ``Insert.insert #[.var `a, .app ``Singleton.singleton #[.var `b]]) "\\{#a, #b\\}",
  -- `insert a s` is `{a} ∪ s`: a synonym, read back as the union it is written as.
  { rule' "sets" (.app ``Insert.insert #[.var `a, .var `s]) "\\{#a\\} \\cup #s" 65
      (sort := "?α") (holes := #[(`s, "?α")]) with synonym := true }]

/-- The `order` pack. -/
def order : Array NotationRule := #[
  rule "order" ``Max.max 2 "\\max(#a, #b)" (sort := "?α") (holes := "?α"),
  rule "order" ``Min.min 2 "\\min(#a, #b)" (sort := "?α") (holes := "?α")]

/-- A predicate written as a sentence, `x \text{ is …}`, of a datum unless
said otherwise (a function is monotone; a proposition is nothing). -/
def isRule (pack : String) (head : Name) (what : String) (holes : String := "!") : NotationRule :=
  rule pack head 1 s!"#a \\text\{ is {what}}" 50 (sort := "Prop") (holes := holes)

/-- The `mathlib` pack. Its rules name Mathlib's constants as the names
alone; the sorts given are those of the read-back (DESIGN §18.3), so that
`|s|` for a finset and `|α|` for a type are told apart by what fills them.
Chosen from the sweep of google-deepmind/formal-conjectures (2026-11-21):
the constants that were left bare most often, where a rule renders them
without a choice a paper would want to make itself, and reads back without
a pun: so not `IsBigO`, whose two functions share a variable the template
cannot bind; not `Set.Ioo`, which `(a, b)` would confuse with a pair; not
`EuclideanSpace ℝ (Fin n)` as `ℝ^n`, which reads as a power; and not
`Nat.ModEq` beside `Int.ModEq`, since `a ≡ b (mod n)` over naturals also
reads as the integer congruence of their casts (as `Int.gcd` would beside
`Nat.gcd`). A `Set` is a function type by definition, so its holes are
`(?α → Prop)`. A coercion names the sorts it coerces from and to, since one
from any sort to any sort would let anything fill any hole: `DFunLike.coe`
takes a datum (`!`: not a type, not a function) to a function into data, so
a finset is not read as a set through it, nor a type as anything.
`SetLike.coe`, from any bundled set to a set, is left out for that reason,
as `|H|` would then read as the cardinality of a type or of a set alike; and
`Set.Elem`, from a set to its subtype, since `|s|` would then read as the
cardinality of the set or of the type. -/
def mathlib : Array NotationRule :=
  let atTop : Pat := .app `Filter.atTop #[]
  #[
  -- Types.
  rule "mathlib" `Real 0 "\\mathbb{R}" (sort := "Sort"),
  rule "mathlib" `Complex 0 "\\mathbb{C}" (sort := "Sort"),
  rule "mathlib" `ZMod 1 "\\mathbb{Z}/#a\\mathbb{Z}" (sort := "Sort") (holes := "Nat"),
  -- Coercions, which are not shown.
  rule "mathlib" `DFunLike.coe 1 "#a" (sort := "(?α → !)") (holes := "!"),
  rule "mathlib" `Rat.cast 1 "#a" (holes := "Rat"),
  rule "mathlib" `NNReal.toReal 1 "#a" (sort := "Real") (holes := "NNReal"),
  rule "mathlib" `PNat.val 1 "#a" (sort := "Nat") (holes := "PNat"),
  rule "mathlib" `Real.toEReal 1 "#a" (sort := "EReal") (holes := "Real"),
  -- Functions of the reals and the complex numbers. A prefix function is at
  -- precedence 72: below `^` (75), so `(\log N)^{2}` keeps its parentheses
  -- and `\log N^{2}` is the logarithm of the square, as a reader takes it;
  -- above `+`, so `\log N + 1` is as written.
  rule "mathlib" `Real.log 1 "\\log #a" 72 (sort := "Real") (holes := "Real"),
  rule "mathlib" `Real.exp 1 "\\exp #a" 72 (sort := "Real") (holes := "Real"),
  rule "mathlib" `Real.sqrt 1 "\\sqrt{#a}" (sort := "Real") (holes := "Real"),
  rule "mathlib" `Real.pi 0 "\\pi" (sort := "Real"),
  rule "mathlib" `Real.sin 1 "\\sin #a" 72 (sort := "Real") (holes := "Real"),
  rule "mathlib" `Real.cos 1 "\\cos #a" 72 (sort := "Real") (holes := "Real"),
  rule "mathlib" `Real.logb 2 "\\log_{#a} #b" 72 (sort := "Real") (holes := "Real"),
  rule "mathlib" `Complex.re 1 "\\Re #a" 72 (sort := "Real") (holes := "Complex"),
  rule "mathlib" `Complex.im 1 "\\Im #a" 72 (sort := "Real") (holes := "Complex"),
  rule "mathlib" `Complex.I 0 "\\mathrm{i}" (sort := "Complex"),
  rule "mathlib" `abs 1 "\\lvert #a \\rvert" (sort := "?α") (holes := "?α"),
  rule "mathlib" `Norm.norm 1 "\\lVert #a \\rVert" (sort := "Real"),
  -- Arithmetic functions.
  rule "mathlib" `Nat.factorial 1 "#a!" 1023 (sort := "Nat") (holes := "Nat"),
  rule "mathlib" `Nat.choose 2 "\\binom{#a}{#b}" (sort := "Nat") (holes := "Nat"),
  rule "mathlib" `Nat.totient 1 "\\varphi(#a)" (sort := "Nat") (holes := "Nat"),
  rule "mathlib" `Nat.primeCounting 1 "\\pi(#a)" (sort := "Nat") (holes := "Nat"),
  -- Floors and ceilings of reals: their holes are `Real`, so that `⌊a / b⌋`
  -- of two naturals (`core`'s rounding division) is not also read as a floor.
  rule "mathlib" `Int.floor 1 "\\lfloor #a \\rfloor" (sort := "Int") (holes := "Real"),
  rule "mathlib" `Int.ceil 1 "\\lceil #a \\rceil" (sort := "Int") (holes := "Real"),
  rule "mathlib" `Nat.floor 1 "\\lfloor #a \\rfloor_{+}" (sort := "Nat") (holes := "Real"),
  rule "mathlib" `Nat.ceil 1 "\\lceil #a \\rceil_{+}" (sort := "Nat") (holes := "Real"),
  -- Cardinalities: of a finset, a set, a type.
  rule "mathlib" `Finset.card 1 "|#a|" (sort := "Nat") (holes := "Finset"),
  rule "mathlib" `Set.ncard 1 "|#a|" (sort := "Nat") (holes := "(?α → Prop)"),
  rule "mathlib" `Fintype.card 1 "|#a|" (sort := "Nat") (holes := "Sort"),
  -- Predicates, as sentences.
  isRule "mathlib" `Nat.Prime "prime" "Nat",
  isRule "mathlib" `Odd "odd",
  isRule "mathlib" `Even "even",
  isRule "mathlib" `Irrational "irrational" "Real",
  isRule "mathlib" `Squarefree "squarefree",
  isRule "mathlib" `IsSquare "a square",
  isRule "mathlib" `Set.Infinite "infinite" "(?α → Prop)",
  isRule "mathlib" `Set.Finite "finite" "(?α → Prop)",
  isRule "mathlib" `Set.Nonempty "nonempty" "(?α → Prop)",
  isRule "mathlib" `Finset.Nonempty "nonempty" "Finset",
  isRule "mathlib" `StrictMono "strictly increasing" "*",
  isRule "mathlib" `Monotone "monotone" "*",
  isRule "mathlib" `Function.Bijective "bijective" "*",
  isRule "mathlib" `SimpleGraph.Connected "connected" "SimpleGraph",
  rule "mathlib" `Nat.Coprime 2 "#a \\text{ and } #b \\text{ are coprime}" 50 (sort := "Prop") (holes := "Nat"),
  rule "mathlib" `Int.ModEq 3 "#b \\equiv #c \\pmod{#a}" 50 "none" (sort := "Prop") (holes := "Int"),
  -- Sets and finsets.
  rule "mathlib" `Set.Icc 2 "[#a, #b]" (sort := "(?α → Prop)") (holes := "?α"),
  rule "mathlib" `Finset.Icc 2 "\\{#a, \\dots, #b\\}" (sort := "Finset"),
  -- `{0, 1, …, n − 1}`, with the `1`, so it is not also read as `Finset.Icc 0 (n − 1)`.
  -- (`range (n + 1)` prints as `{0, 1, …, n + 1 − 1}`: a rule for it would read
  -- `{0, 1, …, b − 1}` as `range b` and as `range ((b − 1) + 1)` alike.)
  rule "mathlib" `Finset.range 1 "\\{0, 1, \\dots, #a - 1\\}" (sort := "Finset") (holes := "Nat"),
  rule' "mathlib" (.app `Set.ofPred #[lam `x `p]) "\\{#x \\mid #p\\}" (sort := "(?α → Prop)") (holes := #[(`p, "Prop")]),
  rule' "mathlib" (.app `Finset.filter #[lam `x `p, .var `s]) "\\{#x \\in #s \\mid #p\\}"
    (sort := "Finset") (holes := #[(`p, "Prop"), (`s, "Finset")]),
  -- Sums and products.
  rule' "mathlib" (.app `Finset.sum #[.app `Finset.univ #[], lam `i `f]) "\\sum_{#i} #f" 67,
  rule' "mathlib" (.app `Finset.sum #[.var `s, lam `i `f]) "\\sum_{#i \\in #s} #f" 67 (holes := #[(`s, "Finset")]),
  rule' "mathlib" (.app `Finset.prod #[.app `Finset.univ #[], lam `i `f]) "\\prod_{#i} #f" 67,
  rule' "mathlib" (.app `Finset.prod #[.var `s, lam `i `f]) "\\prod_{#i \\in #s} #f" 67 (holes := #[(`s, "Finset")]),
  rule' "mathlib" (.app `tsum #[lam `n `f, .app `SummationFilter.unconditional #[.wild]]) "\\sum_{#n}^{\\infty} #f" 67,
  -- Limits along `atTop`, and what holds eventually or frequently there.
  rule' "mathlib" (.app `Filter.Tendsto #[lam `n `f, atTop, .app `nhds #[.var `a]])
    "\\lim_{#n \\to \\infty} #f = #a" 50 "none" (sort := "Prop"),
  rule' "mathlib" (.app `Filter.Tendsto #[lam `n `f, atTop, atTop])
    "\\lim_{#n \\to \\infty} #f = \\infty" 50 "none" (sort := "Prop"),
  rule' "mathlib" (.app `Filter.Tendsto #[lam `n `f, atTop, .app `Filter.atBot #[]])
    "\\lim_{#n \\to \\infty} #f = -\\infty" 50 "none" (sort := "Prop"),
  rule' "mathlib" (.app `Filter.Eventually #[lam `n `p, atTop])
    "\\text{for all sufficiently large } #n,\\ #p" 0 (sort := "Prop") (holes := #[(`p, "Prop")]),
  rule' "mathlib" (.app `Filter.Frequently #[lam `n `p, atTop])
    "\\text{for infinitely many } #n,\\ #p" 0 (sort := "Prop") (holes := #[(`p, "Prop")]),
  -- Graphs.
  rule "mathlib" `SimpleGraph.chromaticNumber 1 "\\chi(#a)" (holes := "SimpleGraph"),
  rule "mathlib" `SimpleGraph.maxDegree 1 "\\Delta(#a)" (sort := "Nat") (holes := "SimpleGraph"),
  rule "mathlib" `SimpleGraph.minDegree 1 "\\delta(#a)" (sort := "Nat") (holes := "SimpleGraph"),
  rule "mathlib" `SimpleGraph.cliqueNum 1 "\\omega(#a)" (sort := "Nat") (holes := "SimpleGraph"),
  rule "mathlib" `SimpleGraph.edgeFinset 1 "\\mathrm{E}(#a)" (sort := "Finset") (holes := "SimpleGraph"),
  rule "mathlib" `SimpleGraph.completeGraph 1 "K_{#a}" (sort := "SimpleGraph") (holes := "Sort"),
  rule "mathlib" `SimpleGraph.cycleGraph 1 "C_{#a}" (sort := "SimpleGraph") (holes := "Nat"),
  rule' "mathlib" (.app `SimpleGraph.Adj #[.var `G, .var `u, .var `v]) "#u \\sim_{#G} #v" 50 "none"
    (sort := "Prop") (holes := #[(`G, "SimpleGraph")]),
  -- Classes, so that instance binders are hypotheses: the sweep's judge found
  -- `[Fintype V]`, `[Group G]` and `[Field k]` left out of the prose, which
  -- generalises a statement. (`[Fact p]` needs no rule: it is `p`.)
  -- `Fintype α` and `Finite α` both say α is finite, as do `CommGroup` and
  -- `AddCommGroup` that it is abelian: the second of each pair reads for both.
  { classRule "mathlib" `Fintype "finite" with synonym := true },
  classRule "mathlib" `Finite "finite",
  classRule "mathlib" `Infinite "infinite",
  classRule "mathlib" `Nontrivial "nontrivial",
  classRule "mathlib" `Group "a group",
  classRule "mathlib" `CommGroup "an abelian group",
  { classRule "mathlib" `AddCommGroup "an abelian group" with synonym := true },
  classRule "mathlib" `Ring "a ring",
  classRule "mathlib" `CommRing "a commutative ring",
  classRule "mathlib" `Field "a field",
  classRule "mathlib" `CharZero "of characteristic zero",
  classRule "mathlib" `IsNoetherianRing "Noetherian",
  classRule "mathlib" `IsLocalRing "local",
  classRule "mathlib" `TopologicalSpace "a topological space",
  classRule "mathlib" `MetricSpace "a metric space",
  classRule "mathlib" `CompleteSpace "complete",
  classRule "mathlib" `ConnectedSpace "connected",
  classRule "mathlib" `NormedAddCommGroup "a normed abelian group",
  classRule2 "mathlib" `Module "#b \\text{ is an } #a\\text{-module}",
  classRule2 "mathlib" `Module.Finite "#b \\text{ is a finitely generated } #a\\text{-module}",
  classRule2 "mathlib" `FiniteDimensional "#b \\text{ is finite-dimensional over } #a",
  classRule2 "mathlib" `Algebra "#b \\text{ is an } #a\\text{-algebra}",
  classRule2 "mathlib" `NormedSpace "#b \\text{ is a normed } #a\\text{-vector space}",
  -- Polynomials.
  rule' "mathlib" (.app `Polynomial.eval #[.var `x, .var `p]) "#p(#x)" 1023 (holes := #[(`p, "Polynomial")]),
  rule "mathlib" `Polynomial.X 0 "\\mathrm{X}" (sort := "Polynomial"),
  rule "mathlib" `Polynomial.degree 1 "\\deg #a" 72 (holes := "Polynomial")]

/-- The packs by name. -/
def all : List (String × Array NotationRule) :=
  [("core", core), ("logic", logic), ("sets", sets), ("order", order), ("mathlib", mathlib)]

/-- The rules of the named packs, in the order given. -/
def select (names : Array String) : Array NotationRule :=
  names.foldl (fun acc n => acc ++ ((all.find? (·.1 == n)).map (·.2)).getD #[]) #[]

end Imprimatur.Packs
