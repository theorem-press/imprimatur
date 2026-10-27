# Plan: Pollack-consistency, proved

**Status: done**, on branch `pollack-plan` (phases A–G), with these changes
to the plan below, each taken because the proof asked for it:

- **Layer 2 is gone.** The parser keeps one of each *variant* of a reading
  (the same reading tree, the same sort or bindings), not a most general
  one, so no order on sorts, no `Lawful` laws and no `Reads.mono` are
  needed: the completeness theorem holds for every algebra of sorts, and
  phase F (the laws for Lean's algebra) has nothing left to prove. The
  property tests of phase B found `bind_mono` false of Lean's `bind`
  (a variable already bound keeps its binding), which is what decided it.
- **Coercion chains, not `Acyclic`.** A question carries the argument
  sorts of the coercions above it on the chain of coercions it is the
  argument of, and a chain applies a coercion only if no coercion above
  has its argument sort (route A of docs/coercion-chains.md, which
  replaced the first rule here, the sorts asked above): chains are finite, so no cycle of coercions is entered and
  nothing is cut. The specification says the same (`Reads.coe`). A real
  notation's coercion graph is cyclic as soon as it has a coercion with a
  type variable (`Nat → * → Nat`), so `Acyclic` as a notation error would
  have refused ordinary notations. A first version recorded the coercions
  applied instead, which let a chain revisit a sort (`Nat → Int → Nat`) and
  made one clause view of the paper ask 300,000 questions of one formula.
  And a cast (a coercion whose sort stands for any sort, as the `core`
  pack's `Nat.cast`, `Int.cast`, `Subtype.val`) is not applied below a
  cast, a cast of a cast being a cast: otherwise the casts chained through
  every sort in every order, and the same span was asked a hundred times.
  The cut, which only a production whose body is a bare hole can now bring
  about, is a flag like `over` and `pruned`, reported as "not validated",
  and the cut bookkeeping (answers remembered with the questions they were
  cut on) is gone.
- **A production's body is read under no bindings**, whatever the sort
  asked for, as before. Binding its type variables from the sort asked for
  first was tried on the way: it asks each hole at a sort of its context
  (`* → Nat`, `* → Int`, …) and so reads each span once per context rather
  than once, which cost the chart parser its sharing, and the paper took
  fifteen times longer to extract.
- **The grammar's lists are checked**, not assumed: the search for a
  list's rest is complete only when each element takes a token (`listsWF`,
  a flag), so the theorem has no hypothesis about the grammar.
- **Completeness triples** carry their precondition inside
  (`CTriple m P Q`), so that the monotonicity of the flags, which the
  conditional triple needs at every bind, is proved in the same induction
  as completeness rather than in a second one.
- **Phase E** instantiates the model with a world whose `Reads` is that the
  validator accepts each formula printed of a statement (`Validated`), and
  proves `Anatomy.Sound`'s two reading-back assumptions of it
  (`Validated.sound`, `document_pollack`); the renderer's expected reading
  stays the hypothesis it was.

The theorems are `SpliceModel.readBack_complete`, `readBack_unique`,
`pollack` (`splice/SpliceModel/ReadBackComplete.lean`), and
`Validated.sound`, `document_pollack`, `document_pollack_rules`
(`Validator.lean`); the goldens are byte-identical throughout, and
`lint/axioms` finds the standard axioms only.

Status: proposal. Continues docs/verified-validator.md, whose phases 0–3
are done (the parser is sound, `SpliceModel.readBack_sound`; the matcher
decides matching; a validated formula reads as what it was rendered from,
`validated_sound`) and whose phase 4, completeness, it replans. Companion
to docs/verified-splicer.md and docs/verified-extractor.md.

## The theorem

Wiedijk's Pollack-consistency: parsing what the system printed gives back
what it printed. For imprimatur the reader is the notation's grammar `G_N`,
which the paper's Appendix A gives its reader, and the statement is per
formula:

> **Pollack-consistency of a validated formula.** Let `e` be an expression
> the extractor rendered as TeX `t`, with expected reading `E`, under
> notation whose coercions form no cycle. If the check reports nothing of
> `t`, then `t` has exactly one reading in `G_N`, and it matches `E`: it is
> `E` wherever `E` is definite.

and, through Theorem 1 of the splicer, for a document: every formula a
document that checks clean shows has exactly one reading in the notation's
grammar, the reading of the expression it was rendered from.

What this adds to what is proved today is the word *exactly*: that the one
reading the parser returns is the only one. What it does not add, and what
stays trusted afterwards, is said at the end.

The theorem, in Lean, will read

```
theorem pollack (hA : A.Lawful) (hg : Acyclic A g) (ex rd : Reading)
    (h : readBackWith A g ts s = (#[rd], flags)) (hf : flags.any = false)
    (hm : ex.matches rd = true) :
    (∀ rd' σ, Exp A g ts s 0 none 0 ts.size rd' σ → rd' = rd) ∧ Matches ex rd
```

with `Exp` the grammar's readings as specified in `SpliceModel.ReadBack`,
`A.Lawful` the laws of the sort algebra (below), and `Acyclic` the side
condition on coercions.

## Why the proof is not routine, and the shape that makes it short

Completeness of a chart parser against an inductive semantics is routine
when the parser keeps everything. This one prunes: two readings per
question, a cap on the sorts a reading can have, and the rule that a
reading of unknown sort stands for all its other sorts. The first proof
attempt (verified-validator.md, "Phase 4") showed that the pruning is what
has to be understood, and that the understanding is one notion: *generality*
of sorts. A reading kept in place of a dropped one must be at least as
general, and a more general reading must admit every continuation the
dropped one did. Once that is a theorem about the semantics, the parser's
every shortcut is an instance of one lemma, and the main proof is a single
induction on derivations with no case analysis on fuel, cuts or caps.

The plan therefore has five layers, each with one idea:

| Layer | Idea | Result |
|---|---|---|
| 1. Semantics | One inductive family of questions and answers; readings carry their own sort | `Reads Q a`, replacing `Exp`/`Seq`/`Tail` |
| 2. Generality | A preorder on sorts and bindings; the algebra's laws; monotonicity of the semantics | `Reads.mono` |
| 3. Pruning | One abstract operation, "keep a dominating subset or say so" | `keep_dominates` |
| 4. The parser | Every step dominates the derivations of its question; memo entries dominate when valid | `complete` |
| 5. The formula | Uniqueness from domination; the model's `reads` is the parser's | `pollack`, `document_pollack` |

Three small changes to the parser make layers 3 and 4 clean; they are
listed with the layers that need them, and each keeps the goldens.

## Layer 1: the semantics as one family

Today `Exp`, `Seq` and `Tail` are three mutual inductives. Mutual induction
in Lean is awkward (`induction` does not apply; the recursor takes three
motives), and every lemma about derivations would pay for it three times.
Replace them by one family indexed by a *question*:

```
inductive Question
  | expr (s : String) (p : Nat) (excl : Option Nat) (i j : Nat)
  | body (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat)
  | rest (l n : Nat) (env : Env) (i j : Nat)

/-- An answer: a reading with its sort, or children with their bindings. -/
inductive Answer
  | one (r : Reading) (σ : String)
  | many (cs : Array Reading) (env : Env)

inductive Reads : Question → Answer → Prop
```

with the same constructors as now (`prod`, `coe`, `paren`, `group`, `done`,
`tok`, `hole`, `var`, `tail`, `nil`, `more`), each typed by the question it
answers. `induction h` then works, and every lemma is stated once. The
soundness proof moves over by renaming: its triples take `Reads (.expr …)`
where they took `Exp`.

**The answer's sort is its own.** Today a reading found for a question of a
known sort `s` is given sort `s` (`variantOf`); only for an unknown sort does
it keep the production's sort. This makes the semantics depend on the
question in a way that layer 2 would have to compensate for, with a law
relating `compat` to generality that the sort algebra does not satisfy (a
named type is compatible with a function type, but neither is more general
than the other). Give every reading its own sort, the production's sort
under its bindings, or the coercion's. Then monotonicity in the question
(layer 2) holds with the *same* answer, and one case of every proof goes.
Change in the parser: `variantOf s so` becomes `so`. More sort variants are
kept at known sorts, up to the cap; the goldens gate it.

## Layer 2: generality, and the laws of sorts

The parser's parameter `SortAlgebra` gains a preorder and its laws:

```
structure SortAlgebra.Lawful (A : SortAlgebra) : Prop where
  le : String → String → Prop                 -- s ⊑ s': s' is at least as general
  refl : ∀ s, le s s
  trans : ∀ s t u, le s t → le t u → le s u
  top : ∀ s, le s "*"
  accept : ∀ f f' e e', le f f' → le e e' → A.compat f e = true → A.compat f' e' = true
  expected_mono : ∀ env env' s, Env.le env env' → le (A.expected env s) (A.expected env' s)
  bind_mono : ∀ env env' s f f', Env.le env env' → le f f' → Env.le (A.bind env s f) (A.bind env' s f')
  bind_top : ∀ env s, A.bind env s "*" = env
```

where `Env.le env env'` says `env'` binds a subset of what `env` binds, each
to a sort at least as general. The laws say exactly what the pruning
assumes: an unknown sort accepts what any sort accepts (`top`, `accept`),
binds nothing (`bind_top`), and a more general context makes more general
demands (`expected_mono`, `bind_mono`). `accept` in the second argument is
what makes a more general *question* no harder; in the first, what makes a
more general *answer* no worse.

**Monotonicity of the semantics**, the heart of the plan:

```
theorem Reads.mono (hA : A.Lawful) :
    Reads A g ts q a → Question.le q q' → ∃ a', Answer.le a a' ∧ Reads A g ts q' a'
```

where `Question.le` is `⊑` on the sort of an expression question and
`Env.le` on the bindings of a body question (same span, precedence,
exclusion, position), and `Answer.le` is `⊑` on a reading's sort, `Env.le`
on children's bindings, with the reading and the children equal. One
induction on the derivation; each constructor's case is the corresponding
law. With the answer's sort its own (layer 1), the `prod` case is `accept`
and `expected_mono`; `coe` is `bind_mono` then `accept`; `hole` is the
induction hypothesis for the hole's question (more general by
`expected_mono`) followed by `bind_mono`; the rest is reflexivity.

**Proving the laws for Lean's sorts.** `STerm.compat`, `expected` and `bind`
are the extractor's and are `partial`; they stay in the extractor. The plan
is: (1) state `le` for `STerm` (`*` and type variables above everything,
`Sort*` above `Prop` and `Sort`, a type without arguments above itself with
any, parts pointwise, and nothing else comparable); (2) *test* the laws by
property tests on random sorts, in `extract/test` beside `HashProps`,
before proving anything, since a false law is cheaper to find by testing
and the algebra has clauses written for cases (`named`, `univFits`) that may
not be monotone; (3) totalise `STerm.parse` and prove the laws, or, where a
clause breaks one, change the clause. Until (3), the theorem is conditional
on `A.Lawful`, which is still a theorem about the search; the paper says so.

## Layer 3: pruning as one operation

`keep2` keeps two readings, caps variants, and lets an unknown sort stand
alone. Restate it as one operation with one specification:

```
/-- Keep a dominating subset, or say that a reading was dropped. -/
def keep (le : α → α → Prop) [DecidableRel le] (key : α → String) (xs : Array α) : Array α × Bool

theorem keep_subset : ∀ x ∈ (keep le key xs).1, x ∈ xs
theorem keep_dominates : (keep le key xs).2 = false → ∀ x ∈ xs, ∃ y ∈ (keep le key xs).1, key x = key y ∧ le x y
```

Its definition is today's: a third key is dropped (flag), a variant past the
cap is dropped (flag), a variant below one kept (`le`) is dropped (no flag),
a variant kept drops those below it. `le` is `Answer.le` restricted to the
same reading; `"*"` and the empty environment are its tops, which is the
"stands alone" rule as an instance. `keep_dominates` is the only fact the
parser proof uses about pruning. The two shortcuts the first attempt
found, the parentheses guard and the snapshot in same-sort coercion
chains, go: parentheses are always read, and `coes` iterates to a
fixpoint, which `keep_dominates` keeps finite (nothing below a kept variant
is added, and the cap flags the rest). Both changes gate on the goldens;
the second was tried and is safe *with* the stands-alone rule, which `le`
now is.

## Layer 4: the parser dominates

Soundness was proved in Hoare triples `{Inv} m {Inv ∧ Q}`. Completeness is
the same discipline with two more ingredients.

**Flags are monotone.** Each function only sets `over`, `pruned`, `cut`;
`flags_mono : (m.run st).2.flags ≥ st.flags`. The completeness triple is
conditional on the *final* flags being clear, which by monotonicity means
no step set one:

```
def CTriple (m : CountM α) (Q : α → Prop) : Prop :=
  ∀ st, CInv st → st.flags = clear → (m.run st).2.flags = clear → CInv (m.run st).2 ∧ Q (m.run st).1
```

**Domination of a question.** The postcondition of every step:

```
def Dominates (q : Question) (res : Array Answer) : Prop :=
  ∀ a, Reads A g ts q a → ∃ a' ∈ res, Answer.le a a'
```

and the completeness invariant `CInv`: every remembered answer dominates its
question when its cut keys are active (the bookkeeping already there), and
`reach[s]` is `reachSplit s`. The step theorems have the form of the
soundness ones with `Dominates` for `∀ x ∈ res, Reads q x`; the same
`SoundAll` conjunction, the same induction on fuel.

**No cuts under acyclicity.** A cut loses derivations that return to a
question being asked, which only a cycle of coercions makes. Rather than
prove loop derivations dominated, which is false in general, take the
side condition DESIGN §18.3 already states: `Acyclic A g`, the graph with
an edge from `s` to `A.expected #[] s'` for each coercion with hole sort
`s'` whose sort is compatible with `s` has no cycle. It is decidable on the
grammar (finitely many coercions, finitely many targets), the extractor
checks it when it builds the grammar and reports a cycle as a notation
error, and the theorem assumes it. Two lemmas: `Acyclic → ¬cut` (the
active keys along any call path form a strictly descending chain in the
coercion order, within a span), and so memo entries are always valid; and
derivations are simple. The `cut` flag stays as a safety net and is not
part of the theorem.

**The two "found" lemmas** carry the weight of the main induction:

- *Body completeness*: if `Reads (.body body pos env i j) (.many cs env')`
  then `seq` on that question returns, when flags stay clear, an answer
  `(cs, env'')` with `Env.le env' env''`. The `hole` case: the hole's
  question is asked; by the induction hypothesis its answer dominates the
  derivation's reading with a more general sort; `bind_mono` makes the
  continuation's bindings more general; `Reads.mono` (layer 2) turns the
  derivation's continuation into one from the more general bindings;
  the induction hypothesis for the continuation finishes. This is the one
  place the whole plan converges, and it is six lines.
- *Expression completeness*: the `prod` case is body completeness and
  `keep_dominates`; `coe` is the fixpoint's invariant and `accept`; `paren`
  and `group` are the recursive call, now unguarded.

**Fuel.** `over` means the budget or the fuel ran out, and the theorem
assumes neither. The budget is a resource bound and is meant to be
assumed. The fuel is set so that it cannot run out before the budget
(each unit of fuel is a step, and the fuel exceeds the budget), so one
flag is enough; a lemma says so, and the theorem's hypothesis is the
budget alone.

## Layer 5: the formula, and the document

**Uniqueness.** From soundness and domination: if `readBackWith` returns
`#[rd]` with clear flags, every derivation `Reads (.expr s 0 none 0 n)
(.one rd' σ)` is dominated by some element of the result, which is `rd`
with some sort, and `Answer.le` keeps the reading, so `rd' = rd`. With
`matches_iff`, that is the theorem `pollack` above. Two readings in the
result are two derivations, by soundness, so the extractor's "ambiguous" is
exact too.

**The model's `reads` is the parser's.** `World.Reads r S` is an abstract
field. Give the paper's anatomy a `expect : Part → Reading` (what the
renderer builds, `Render.Expect`) and define, for a rendering whose
formulas are the parts' prints,

```
ReadsPart t q := ∀ rd σ, Reads A G_N (tokenize t) (.expr (sort q) 0 none 0 _) (.one rd σ) → Matches (expect q) rd
```

Then `Anatomy.Sound.formulas`, today the assumption that a rendering which
reads back reads back formula by formula, is *proved* from the bundle's
validation being empty, by `pollack`; what remains assumed of the anatomy
is `expect q` being the part's reading up to `≈_N`, which is the renderer's
construction and the one link that stays in `MetaM`. `prose_true` and
`rules_true` then say, of a document that checks clean, that each formula
of each block has exactly one reading in the notation's grammar, the
renderer's expected one: `document_pollack`.

**The paper.** §9 states `pollack` in place of its sound half, Theorem 1.1's
"reads back" becomes this, and the trusted base loses "the parser that
reads formulas back" and gains "the laws of the sort algebra" until layer 2
step (3) is done, and "coercions form no cycle", now checked.

## What stays trusted afterwards

- That the expected reading `E` is the expression `e` up to what the
  notation declares invisible: the renderer's construction of `E` in
  `MetaM`, alongside the rendering. Proving it is verifying the renderer.
- Forms given no expected reading (`⁇`, #41): there `E` is `any` and the
  theorem says only that below them the reading is as expected. #41 closes
  the gap form by form, and is independent of this plan.
- The grammar's built-in productions (`∀`, `∃`, `λ`, application, the
  styles' forms) being what the renderer prints: the rules' productions
  share `Doc.holeNeeds` with the renderer; the built-ins are written by hand.
- The tokenizer against TeX's own tokenization, and glyphs that print alike
  (#43).
- The notation's meaning: Wiedijk's weak failures, as intended.

## Phases

Each phase keeps the golden bundles, the end-to-end suite and the about
paper byte-identical unless it says otherwise, and each ends with
`lake build --wfail`, `lint/axioms` and the paper's `check` clean.

| Phase | Work | Exit |
|---|---|---|
| A | **One family.** `Question`, `Answer`, `Reads`; soundness moved over; answers' sorts their own (`variantOf` gone). | Soundness proved for `Reads`; goldens byte-identical, or the differences reviewed and accepted (more variants at known sorts). |
| B | **Generality.** `Lawful`, `Env.le`, `Question.le`, `Answer.le`; `Reads.mono`. Property tests of the laws on `STerm` (10,000 random sorts per CI run); each failing law either fixed in the algebra or weakened with the proof's consent. | `Reads.mono` proved; the laws hold on the tests. |
| C | **Pruning.** `keep` with `keep_subset`, `keep_dominates`; the parentheses guard removed; `coes` to a fixpoint; `Acyclic` defined, decided, checked by the extractor with a notation error. | Lemmas proved; goldens byte-identical; the fixtures' notations acyclic. |
| D | **Domination.** `flags_mono`, `CTriple`, `CInv`, `Dominates`; the step theorems; `Acyclic → ¬cut`; fuel exceeds budget. | `complete` proved. |
| E | **The theorem.** `pollack`; `expect` in the anatomy, `ReadsPart` instantiated, `Sound.formulas` proved, `document_pollack`. | Proved; `lint/axioms` clean. |
| F | **Lean's sorts.** `STerm.parse` total; `Lawful` proved for the extractor's algebra. | Proved, or the clauses that fail rewritten. |
| G | **Paper and docs.** §9, the trusted base, §6.1's soundness paragraph, Theorem 1.1's "reads back"; DESIGN §18.3–18.5; the changelog; #22 closed. | `check` clean; lint passes. |

Sizes, from the soundness proof as the yardstick (about 850 lines for
layers 1 and 4's sound half): A one week; B two, most of it the laws and
`Reads.mono`; C one; D two to three; E one; F one to two, the uncertain one,
since the algebra was written clause by clause and may need changing; G a
few days. Phases A–E give the theorem conditional on `Lawful`; F removes
the condition.

## Risks

- **A law is false of Lean's sorts.** The most likely outcome of phase B's
  tests, for the clauses that accept a named type where a function is
  expected, or `Sort*`. Each such clause is a choice the validator made to
  read more formulas; the remedy is to weaken the law to what the clause
  needs and check that `Reads.mono` survives, or to drop the clause and
  count the formulas it stops reading on the two projects.
- **Giving answers their own sort changes readings.** More variants at
  known sorts can only add readings a stricter variant hid, so a golden
  that changes reveals a formula the old parser read incompletely; review
  each.
- **The fixpoint's cost.** Bounded by the cap and by `keep_dominates`, and
  tried once; measure on the two projects as before.
- **Acyclicity bites a real notation.** A cycle of coercions is a notation
  that writes two types as each other's; report it as the error it is.

## Decisions needed

1. Answers carry their own sort (recommended), accepting that goldens may
   change where the old parser hid a reading; or keep `variantOf` and
   prove a weaker monotonicity with a law relating `compat` to generality,
   which the algebra does not satisfy today.
2. `Acyclic` as a checked notation error (recommended), or as a theorem
   hypothesis only, with cuts kept in the theorem.
3. Phase F in scope (the theorem unconditional), or the theorem left
   conditional on `Lawful` with the laws tested, and F a later design.
