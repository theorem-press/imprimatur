# Proposal: chains of invisible coercions, closed

Status: route B chosen (25 October 2026); its phases below. Follows
docs/pollack-consistency.md (PR #83), whose theorem
`SpliceModel.pollack` is about the grammar `SpliceModel.Reads`. That
grammar limits chains of invisible coercions, for speed, and the question
this proposal answers is whether the limit loses readings.

## The answer

It does. The restricted grammar and the unrestricted one have different
readings, and the difference can hide an ambiguity. The real parser, with
Lean's sort algebra, shows it on this grammar:

| Production | Sort | Body |
|---|---|---|
| `x` | `Nat` | `x` |
| `Option.some`, invisible | `Option(?α)` | `#a : ?α` |
| `g` | `Prop` | `g ( #a : Option(Option(Option(Nat))) )` |
| `h` | `Prop` | `g ( #a : Nat )` |

On the tokens `g ( x )` the parser returns one reading, `h[x]`, with no
flag, so the formula is validated. But `g (some (some (some x)))` prints
as `g(x)` too. In the unrestricted grammar the text has two readings, and
the theorem's "every reading in the grammar is the expected one" is false
of it. The same happens with a cast under a cast when the casts project,
as with `unwrap : Wrap(?α) → ?α` over `unbox : Box(?β) → ?β`.

So the gap cannot be closed by proving the two grammars equal as they
stand. Two routes close it. Route A makes the renderer obey the parser's
chain rule, so that no rendering needs a chain the parser does not read.
Route B, the one taken, keeps the renderer and changes the parser's chain
rule to one that is complete for Lean's algebra of sorts, proving for
that algebra that a bounded chain reads everything an unbounded one
does. Route A is kept below for the record.

## The restriction, exactly

The parser's question carries `used`, the sorts asked above it on the
chain of coercions it is the argument of (`Imprimatur.Validate.coes`,
`SpliceModel.Reads.coe`). A coercion `k` has a result sort `T_k` and one
hole of sort `s'_k`. Its argument is asked at `e_k := expected [] s'_k`,
which depends on `k` alone. At a question of sort `s`, coercion `k` is
tried only when:

- `e_k` is not in `used`; and
- if `k` is a *cast* (its result sort stands for any sort,
  `SortAlgebra.anySort`), no cast is above it on the chain (`castMark` is
  not in `used`).

The argument's question then has `used' = s :: used`, plus `castMark`
after a cast. A hole, the emitter's parentheses and a TeX group start a
new chain (`used = []`).

"Each sort once" is loose. The rule compares the argument's sort with
the sorts above it, the top question's included. So the top sort is
never revisited, and the first argument sort may repeat once,
immediately. At a concrete hole two hidden `some`s are read. At a hole of
unknown sort only one is: `x = y` with `y : Option(Option(Nat))` has no
reading if it was printed from `some (some x) = y`.

## Where readings are lost, and why

One fact organises the analysis. **An answer's sort never depends on the
sort asked for.** A production's reading has sort `expected env T`, with
`env` from its body, which is read under no bindings. A coercion's
reading has sort `f_k(σ) := expected (bind [] s'_k σ) T_k`, where `σ` is
its argument's sort. Parentheses pass their inside through. The sort
asked for, and the chain, only *filter* answers, through `compat T_k s`
and `compat (f_k σ) s`. So a chain is a path through the finite set of
argument sorts `E = {e_k}`, and the sort it ends with is
`f_{k_1}(f_{k_2}(… σ))`.

Coercions fall into three kinds by `f_k`:

- **Forgetful.** `T_k` shares no type variable with `s'_k`, so `f_k` is
  constant. The core pack's casts are of this kind (`Nat.cast`,
  `Int.cast`, `Subtype.val`, result sort `*`).
- **Growing.** `T_k` puts a variable of `s'_k` under a constructor:
  `Option.some : ?α → Option(?α)`, which the paper's own notation hides.
  Each application makes the sort deeper.
- **Projecting.** `T_k` is a variable that sits under a constructor in
  `s'_k`: `unwrap : Wrap(?α) → ?α`.

Readings are lost in three ways:

1. **A growing coercion reapplied.** `some^n(x)` has sort
   `Option^n(Nat)` for every `n`. The rule stops at two, or one at an
   unknown-sort hole. A context that needs more, such as a concrete hole
   `Option³(Nat)` or a binding that a later hole checks, finds nothing.
   This is the counterexample above.
2. **A projecting cast under a cast.** The cast rule blocks it, and the
   inner projection changes the sort the outer one sees.
3. **A path back to the top sort.** A chain that returns to the question's
   own sort reaches answers that a direct path also reaches, but under a
   different first coercion, and so with a different sort. Answer sets
   differ. I have not found a formula whose *readings* differ this way.

One case loses nothing. A forgetful cast under a forgetful cast,
`((n : ℤ) : ℝ)` printed `n`, is read by the inner cast alone, with the
same reading and the same sort `*`. The probe confirms it.

## Why no proof covers every algebra

The theorems hold for any sort algebra. For this gap that generality is
fatal. An algebra may accept `Option^n(Nat)` only for `n = 1000`, so no
bounded search is complete for every algebra. An unbounded search does
not end: at an unknown-sort question, `some^n` gives a new answer for
every `n`. A parser complete for the unrestricted grammar, for every
algebra, would have to set a flag on every formula with an unknown-sort
hole and a growing coercion, which is most formulas of the paper.

So closing the gap needs one of two things. Either laws of Lean's algebra
that bound the chains that matter (route B), or a target grammar that is
not the unrestricted one (route A).

## Route A: the renderer obeys the chain rule (not taken)

The theorem needs the grammar to contain the renderings, not Lean's
types. Every reading the unrestricted grammar has and `Reads` lacks is a
term printed with a chain the rule does not read. If the renderer never
prints such a chain, those terms print differently. Then they are not
readings of the text, and they cannot collide with it.

### The shared rule

A new structure in `bundle/ReadBack.lean`:

```lean
/-- Which invisible coercions a chain may stack: decided from the coercions
on it alone, never from the sort asked for at its top. -/
structure ChainRule where
  allows : List String → Nat → Bool   -- the chain so far, the coercion
  push   : List String → Nat → List String
```

The production rule, `ChainRule.std A g`, is the current one with one
change. The chain starts with the argument sort of the first coercion,
not with the sort asked at the hole. The renderer cannot know that sort,
since it comes from the parser's bindings. A rule that mentions it could
not be obeyed by construction.

- `allows used k := !used.contains e_k && !(cast k && used.contains castMark)`
- `push used k := chainWith e_k (if cast k then chainWith castMark used else used)`

Chains stay finite, of length at most `|E| + 1`.

### What changes

- **Parser.** `coes` takes the rule. `Reads.coe` takes it as a premise,
  `R.allows used k = true`, with the argument at `R.push used k`. The
  soundness and completeness proofs become generic in `R`, which is a
  mechanical change.
- **Renderer.** `RenderM` carries the chain of invisible coercions above
  the term being rendered. A coercion rule is applied invisibly only when
  `ChainRule.std.allows` permits it. Otherwise the application is
  rendered as for a constant without notation, `\LeanMathConst{Option.some}\,x`,
  which the grammar already reads. Any other node resets the chain. Both
  sides compute `e_k` and `cast k` from `Validate.ofRule` of the same rule.
- **Paper.** The conventions say what a reader needs: an invisible
  coercion never hides another whose argument has the same sort. Where
  one would, it is written.

### What is proved

- `Reads.mono_rule`: a more permissive rule has more readings. The
  unrestricted grammar is `Reads` under the rule that allows every
  chain, so `Reads (std)` is contained in it, and soundness carries over.
- `pollack`, generic in `R`, and for `R = std` as now.
- **The counterexample**, under a total toy algebra in `SpliceModel`:
  the unrestricted grammar reads `g ( x )` as both `g[x]` and `h[x]`, and
  `Reads (std)` only as `h[x]`. This records in Lean why the target is the
  renderer's grammar.

What stays trusted is unchanged in kind. "The grammar follows the
renderer" now covers coercion chains, and their structure holds by
construction, through the one function both call, as the holes'
precedences do through `Doc.holeNeeds`. Whether a chain's sorts pass the
filters remains the existing assumption that the algebra models Lean's
types.

### Every other narrowing, audited

Route A is only as good as the claim that `Reads` holds every rendering.
The other premises of `Reads` that are narrower than Lean:

| Premise | Renderer's side | Status |
|---|---|---|
| A coercion passes the precedence asked for | A coercion returns its argument's `Doc`, so its precedence too | By construction |
| A coercion passes the exclusion (an operand of a chain is not the chain) | `collect` and the emitter's parentheses around a coerced chain operand | **To check**: `a + ↑(b + c)` |
| Parentheses reset the precedence, the exclusion and the chain | The emitter's parentheses | By construction |
| A TeX group keeps the precedence | Braces in templates | By construction |
| A body is read under no bindings | None: this is the grammar's model of elaboration | Trusted, under "sorts" |
| A lone type variable is unknown | Only widens the grammar | Safe for uniqueness |
| Caps, budget, lists, cuts | Flagged, so never validated | Safe |

The exclusion row gets a fixture in phase A2.

### Cost and risk

Rendering changes only where the renderer hides a chain that `std`
forbids. Most such formulas are "not validated" today, since the parser
cannot read them. Three cases are validated today and would change, and
phase A0 counts each:

- Two consecutive `some`s at a concrete hole. The current rule reads
  them; `std` without repeats does not (decision 2).
- A forgetful cast under a forgetful cast, `((n : ℤ) : ℝ)`. The parser
  reads it today through the inner cast alone; `std` with the cast clause
  would make the renderer show one cast (decision 3).
- None other that I know of. A0's comparison is what establishes this.

Making the rule independent of the top sort also lets the parser explore
one more step at the top of each chain. That costs time, also measured
in A0.

## Route B: prove that long chains add nothing (chosen)

Keep the renderer as it is. Take the unrestricted grammar as the target
of the theorem, for Lean's algebra of sorts, and prove that the parser
finds every reading the unrestricted grammar has, with a chain bound that
the grammar determines.

### The target

Write `Reads∞` for `Reads` with `Reads.coe` freed of its chain premises.
The theorem to reach is

> **Small model.** For Lean's algebra, any grammar, any text: if
> `Reads∞ (.expr s 0 none 0 n) (.one r σ)`, then
> `Reads (.expr s 0 none [] 0 n) (.one r σ')` for some `σ'`, where `Reads`
> is the parser's grammar with the chain bound of this plan.

With `readBack_complete`, a formula the parser validates then has no
reading tree in the unrestricted grammar but the expected one, and
`pollack` is Pollack-consistency against the grammar as Lean's types
define it, with nothing narrowed. The renderer, the goldens and the paper
do not change.

The theorem is false for an arbitrary algebra of sorts, since an algebra
may accept `Option^n(Nat)` for one `n` only, and false for the parser's
present chain rule, by the counterexample above. So Route B changes the
parser's chain rule to one that is complete for Lean's algebra, and proves
that completeness of Lean's algebra alone. Soundness and
`readBack_complete` stay generic.

### The idea of the proof

Three facts about Lean's algebra, each a probe today and a lemma in phase
B3:

1. **An answer's sort does not depend on the sort asked for.** A
   production's sort is `expected env T` with `env` from its body, read
   under no bindings; a coercion's is `f_k(σ) = expected (bind [] s'_k σ) T_k`
   from its argument's sort `σ`. The question only filters.
2. **Compatibility is structural, with wildcards.** `compat σ e` compares
   sort trees node by node; `*` and a type variable match anything below
   them. So against a sort `e`, `compat (Option^n(Nat)) e` is the same for
   every `n` beyond the depth of `e`: the probe gives
   `[false, true, true, true, true]` against `Option(*)`.
3. **Binding is structural.** `bind` binds the type variables of a hole's
   sort to the parts of the filler's sort at the same positions, and binds
   nothing to `*`. Two towers compared through a shared type variable
   must be of equal height: `?α := Option(Nat)` rejects `Option²(Nat)`.

Let `D` be the depth of the deepest sort written in the grammar: a
production's sort, a hole's sort, an atom's sort. Every sort in a
derivation is built from these by binding and by coercions. A sort deeper
than `D + 1` has, below depth `D + 1`, structure that no grammar sort
reaches: it can be compared only with another such sort, through a type
variable, and then for equality. Define the **truncation** `φ_D` on sorts:
replace every subterm at depth `D + 1` by `*`. Then:

- `compat σ e → compat (φ_D σ) (φ_D e)`: the comparison agrees above
  depth `D + 1` and `*` matches anything below.
- `φ_D (bind env s σ) ⊑ bind (φ_D env) s (φ_D σ)` and
  `φ_D (expected env s) = expected (φ_D env) s` up to `*` at depth `D + 1`,
  where `⊑` says the left binds whatever the right binds, to sorts that
  agree above `D + 1`. (Grammar sorts `s` are unchanged by `φ_D`, having
  depth at most `D`.)

**Normalisation.** Given a `Reads∞` derivation, apply `φ_D` to every sort
in it. Every premise `compat …` still holds, by the first law, since it
held before. Every `bind` and `expected` still computes the written
sorts, by the second. The reading trees are untouched. The result is a
`Reads∞` derivation in which every sort has depth at most `D + 1`. In
such a derivation a chain of coercions at one span applies each growing
coercion at most `D + 1` times, each projecting coercion at most `D + 1`
times, and visits each sort at most as often as sorts of depth
`≤ D + 1` over the grammar's constructors allow, which is finite.

**The bound.** The parser's chain rule becomes: a chain may hold at most
`N_g` coercions, where `N_g` is computed from the grammar as the number
of distinct argument sorts reachable, each allowed `D + 1` times. A chain
this long or shorter is what the normalised derivation uses, so
`Reads∞ → Reads`, and the parser is complete for the unrestricted grammar.
The bound is loose; phase B0 measures its cost and phase B3 tightens it
where the proof allows (a forgetful cast under a forgetful cast reads as
the inner cast alone, so casts need not chain at all).

### Where it can fail

- **A law may be false** of Lean's algebra as written. The rules for
  `Prop` below `Sort` and `Sort*`, a named type where a function is
  expected, and a type parameter `'x` are the places to look. Each is
  tested in phase B2 before any proof; a failing law is either an
  honest restriction of the theorem (the formulas it excludes, counted on
  the paper and project B) or a fix to the algebra, with goldens reviewed.
- **Truncation may not commute with binding** where a hole's sort is
  itself deep. `bind env (Option(Option(?α))) σ` reads `σ` two levels
  down, and `φ_D σ` may have `*` there. Since hole sorts have depth at
  most `D`, the read stays above `D + 1` and the law holds; the proof
  must track that invariant, which is the delicate part.
- **The bound may be too loose to run.** `N_g` multiplies the question
  space. The chain-independent memo (`exprDirect`) keeps bodies shared,
  so the cost is the coercion passes alone; B0 measures it on the paper.
- **Towers through productions.** `Option` as a visible production
  (`some x` written) builds depth by tokens, not by chains; the depth
  bound counts them too, but they are bounded by the text's length, so
  normalisation is only ever needed for invisible chains.

### Phases

Each phase keeps the goldens, the end-to-end suite and the paper
byte-identical unless it says otherwise.

| Phase | Work | Exit |
|---|---|---|
| B0 | **A bounded chain, measured.** The chain rule becomes a count against `N_g`; `D` and `N_g` computed by `Grammar.of`. Readings compared with the present rule on the fixtures, the paper, the examples; extraction time of the paper; the counterexample grammar validated correctly (`g(x)` ambiguous). | A table of differences and times; the bound settled or the plan revised. |
| B1 | **Lean's algebra, total and in the module.** `STerm.parse`, `compat`, `expected`, `bind` move to `bundle/ReadBack.lean` as total functions (`partial` gone, by a size measure on the string or a fuel on the parser); the extractor's `algebra` is their instance; `lint/verified` covers them. | Goldens byte-identical. |
| B2 | **The laws, tested.** Properties for the three facts and the two truncation laws, on random sorts over random constructors, 10,000 cases per CI run; every clause of the algebra that fails is listed with the formulas it affects. | The laws hold, or the theorem's hypotheses name the clauses. |
| B3 | **The laws, proved**, for the total algebra: structural compatibility, structural binding, the two truncation laws. | Proved; `lint/axioms` clean. |
| B4 | **Normalisation.** `Reads∞` in `SpliceModel`; `φ_D` on derivations; the small-model theorem; `Reads∞ → Reads` under the bound. | Proved. |
| B5 | **Paper and docs.** `pollack∞`; §9 and the trusted base say the grammar is Lean's types with nothing narrowed; DESIGN §18.3 condition 2 and §18.4; this document's status. | `check` clean. |

B0 is a day and decides whether to continue; B1 two or three days; B2 a
week, the one that finds out; B3 and B4 two to three weeks together, B4
the hard one; B5 a few days. Phases B0–B2 leave value if B3 or B4 stall:
a parser whose chain bound is complete in practice, with the laws it
relies on tested, and the counterexample closed.

### Decisions needed

1. **The algebra's clauses that fail a law** (phase B2): restrict the
   theorem, or change the clause and review the goldens. Recommended:
   decide per clause, and prefer a change where it only reads more.
2. **Casts.** Keep the cast clause and prove the forgetful short-cut (that
   a cast under a cast reads as the inner cast alone), or drop it and let
   the bound cover casts too. Recommended: prove the short-cut, since the
   probe shows it holds and it keeps the parser's cost down.
3. **`N_g` in the paper.** State the bound, or only that chains are
   bounded by the grammar. Recommended: state it, in DESIGN.

## The probe

These results come from `lake env lean --run` in `extract/`, on grammars
built with `Grammar.of`, using the same coercion shapes as the core pack
and the paper's notation:

| Grammar | Tokens | Parser | Unrestricted grammar |
|---|---|---|---|
| `g` at `Option^d(Nat)`, `d = 1, 2` | `g ( x )` | `g[x]` | `g[x]` |
| `g` at `Option^d(Nat)`, `d = 3, 4` | `g ( x )` | none | `g[x]` |
| the pun above | `g ( x )` | `h[x]`, no flag | `g[x]`, `h[x]` |
| the same pun, nothing hidden | `g ( x )` | `g[x]`, `h[x]` | `g[x]`, `h[x]` |
| `unwrap` over `unbox`, `n` at `Nat` | `n ( y )` | none | `n[y]` |
| `((n : ℤ) : ℝ)`, both casts hidden | `r ( n )` | `r[n]` | `r[n]` |
| `x = y`, `y : Option(Nat)` | `x = y` | `Eq[x; y]` | `Eq[x; y]` |
| `x = y`, `y : Option²(Nat)` | `x = y` | none | `Eq[x; y]` |

The unrestricted column is from hand derivations. Phase A3 proves the
pun row in Lean.
