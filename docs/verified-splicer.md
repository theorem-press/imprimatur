# Proposal: theorems about the splicer that runs

Status: proposal, not yet started.

## Goal

The splicer's laws and Theorem 1 (DESIGN §18.2) are proved today for a model
of the splicer, `about/lean/SpliceModel`. The model is a separate program,
written by hand. Nothing relates it to `splice/`, the code users run, except
property tests. This proposal makes the theorems be about the code that runs:

- every theorem the paper states names a function the `imprimatur` binary
  executes;
- the model stays, as an abstraction that keeps the proofs readable and
  maintainable, but a proved refinement ties it to the code;
- what remains unproved is a small, named shell (IO, the command line) and
  the trusted base of §18.5.

A theorem *about the code that runs* here means a Lean theorem whose subject
is a constant that `Splice.Cli.runIn` calls on the command's path, with no
reimplementation between the two.

## Where things stand

From an inventory of `splice/` (about 4,200 lines):

- **The pure core is already pure.** `apply`, `check` and `migrate-slots`
  call `plan (doc : Doc) (bundle) (o : ApplyOpts) : Outcome` (Apply.lean).
  `check` adds `audit`, `macroDiags`, `staleDiags` and `sortDiags`. Loading
  a document, `Doc.load`, is generic over the monad, with `Doc.ofFiles`
  running it in `Id`. IO happens only in `Cli`, `Wrapper`, `Doc.loadIO` and
  `Manifests`.
- **But it is written in a style Lean cannot reason about.**
  - There are 30 `while` loops, in the scanner, `Doc.load`, `Slots`,
    `Check`, `Strip`, `Text` and `Sha256`. All of them compile through
    `Loop.forIn`, which is `partial`, so their bodies are opaque to proofs.
  - There are about 100 `let mut`s and about 50 uses of `!` indexing.
  - Positions are `Nat` indices into `Array Char`, and edits are spliced by
    `applyEdits`, which assumes without checking that they don't overlap.
- **There is no `unsafe`, `implemented_by`, `extern` or `native_decide`,**
  and no global state. The packages share one toolchain (v4.35.0) and depend
  on Lean core only.
- **The model and the code diverge.** The model's document is a list of
  pieces with bodies already parsed. The code works on strings, and does many
  things the model doesn't:
  - templates, labels and wraps;
  - `\leanref` source links;
  - the meta source marker;
  - positional slots, renames and `migrate`;
  - `dflt=` digests;
  - normalisation and line endings;
  - comment-delimited blocks, conditionals and verbatim;
  - `--force`, `--keep-stale` and `bad-content`;
  - several files.

## Design

### Three layers, one source of truth

```
  L0  Splice.Model     abstract: Piece, Seg, fill, apply, check, Doc.True, laws
                         ▲  abstraction function + refinement theorems
  L1  Splice.Core      the real algorithms, total and structural, on List Char:
                         scanner, slots, merge, options, edits, plan, check
                         ▲  called directly, nothing in between
  L2  Shell            Cli, Wrapper, Doc.loadIO, Manifests, Toml, JSON, SHA-256
```

- **L0, the model,** moves from `about/lean` into the splice package, with
  its laws. (Done, phase 1: the library `SpliceModel`, keeping its module and
  namespace names, so the paper and its slots are unchanged.) It stays small and readable, because the
  paper presents it.
- **L1, the core,** replaces today's `Scan`, `Slots`, `Text`, `Apply` and the
  pure part of `Check`. The binary runs it, and the theorems are about it.
- **L2, the shell,** is unchanged. It is the only unverified code on the
  command's path, besides the parsers for configuration and bundle files
  (below).

The rule that keeps the layers honest is to **share definitions, not mirror
them.** Wherever L1 does what the model does, it calls the model's function.
For example, slot merging in L1 is

    mergeBody old new = Body.print (Model.fill (Model.slots (parseBody old)) (parseBody new))

so slot preservation is the model's theorem applied to the code's own
function. L1 adds only what the model leaves out (raw text, positions,
options, line endings), each piece with its own small lemmas.

### The lossless scanner

The scanner is the heart of the work. Today it returns items with indices
into the source. The new scanner returns a **lossless** structure, from which
the source can be rebuilt exactly:

```lean
inductive Chunk where
  | text  (cs : List Char)                 -- prose, comments, verbatim: anything not an item
  | item  (syn : ItemSyn)                  -- a block, inline item, ref, check, …

structure ItemSyn where
  kind   : ItemKind
  opener : List Char                       -- "\begin{leandef}", "%LEANROW", "\leaninline", …
  opts   : Option OptsSyn                  -- raw "[…]", each option with its raw spelling
  key    : Arg                             -- raw braces and text
  title  : Option Arg
  gap    : List Char                       -- header to region: "", "\n", " % comment\n"
  body   : List Char                       -- the generated region
  closer : List Char                       -- "\end{leandef}", "%ENDLEANROW", "}"

def print : List Chunk → List Char         -- concatenation, nothing else
def scan (cfg : Config) : ScanState → List Char → Except Diag (List Chunk × ScanState)
```

Its theorems are as follows.

- **Lossless:** `scan cfg st s = .ok (cs, st') → print cs = s`. Every byte is
  in exactly one chunk, so nothing can be dropped or duplicated.
- **Compositional:** the scanner is a state machine, and a scan of `a ++ b`
  from a state where `a` ends at top level is the scan of `a`, then the scan
  of `b` from `a`'s final state. Here *top level* means outside every comment,
  verbatim, group and item. The state records conditionals, switches, open
  environments and liveness.
- **Stable under regeneration:** replacing an item's body with content that
  `plan` accepts leaves the scan's shape unchanged. *Accepts* means content
  that passes `bad-content`: no `\end{env}`, or `%ENDNAME` for a comment
  block, and balanced braces for inline items. The scan keeps the same items,
  options, keys and closers, with only the body replaced. This is the lemma
  idempotence and the fixed point rest on, and it is where `bad-content`
  stops being a heuristic and becomes a proved precondition.
- **Complete:** no text chunk contains a live opener of an alias,
  `\leaninline`, `\leanref` or `\leancheck`, outside comments and verbatim.
  So no item escapes `check`.

The scanner keeps today's behaviour exactly: comments and `%NAME` blocks,
`\verb`, verbatim environments, defining commands, `\newif` switches,
conditionals and liveness, `\input` and its variants, options, and the rule
for where a region starts. Diagnostic positions (`path:line:col`) are
computed from chunk lengths, so they need no index arithmetic.

**Representation.** The core works on `List Char`. Strings are converted at
the boundary, where `String.toList_append`, `String.ofList_toList` and
`toList_ofList` are available in core. `List Char` makes structural recursion
and its lemmas cheap, and is linear for a 300 KB paper. Appends are built
with accumulators, never left-nested, to stay linear.

### Bodies and slots

`parseBody : Option SlotSpec → List Char → Body` (with `Body := List Seg`,
L0's type) is lossless too: `Body.print (parseBody spec s) = s`. It covers
both `\leanslot{id}{text}` and positional slots, including a `\leanslot`
nested in a positional slot (`outer`). The checksum and the default digest
are defined on bodies:

- `sum` is the hash of the normalised print of the body, with its slot texts
  emptied;
- `dflt` is the hash of the list of (id, normalised text) pairs.

SHA-256 stays an opaque function in L2. No theorem needs it to be collision
resistant, only to be a function. Hand-edit detection, which does rely on
collisions being rare, guards writing and is outside the laws.

`dflt` enters the model, so the model's `fill` gains the rule the code now
has: when `digest (slots old) = recorded`, the new defaults are taken.
Otherwise the old text is kept. Slot preservation becomes: *if the recorded
digest doesn't match the old slots, every slot present before and after
keeps its text*. That needs no assumption about collisions. A collision
could only cause untouched-looking text to be refreshed, which is the safe
direction.

### `plan` as a map over chunks

```lean
def planItem (cfg) (b) (o) (labels) (syn : ItemSyn) : ItemResult   -- new syn, change?, diags
def planFile (cfg) (b) (o) (cs : List Chunk) : List Chunk × List Change × List Diag
def applyFiles (cfg) (b) (o) (files : List (Path × String)) : Except (List Diag) (List (Path × String))
def checkFiles (cfg) (b) (o) (files : List (Path × String)) (extra : MacroEnv) : List Diag
```

- **`planItem`** makes today's decisions in today's order: the view; the
  template with its label; the meta source marker; the ref; `dflt`;
  `mergeBody`; shaping and line endings; `bad-content`; normalised
  comparison; hand edits; option edits.
- **Option edits** become a function on `OptsSyn` that replaces the values
  of `sum` and `dflt`, or appends them, and leaves every other option's raw
  text alone. They replace position-based edits, so `applyEdits`, with its
  unchecked no-overlap assumption, disappears from the core.
- **`applyFiles` and `checkFiles`** are what the command line calls. The
  shell reads files, calls one of them, and writes or prints the result.

Labels count occurrences per (alias, key) in document order. They are a fold
over the chunks of all files, computed before `planFile`.

### Abstraction and refinement

The abstraction function maps the core's chunks to the model's pieces:

```lean
def abs (cfg) : Chunk → Option Model.Piece
  | .text _ => some (.text …)
  | .item syn => match syn.kind with
    | .block | .inline => some (.block key (view cfg syn) (parseBody spec syn.body))
    | .check => some (.check key stmtHash)          -- one per key of a \leancheck
    | _ => none                                     -- index, leanok, hypref: no claim
```

The bundle is abstracted by `Entry.map` (already in `Bundle.lean`, with
`map_id` and `map_map`), with each view's TeX parsed into a body. A world
over TeX gives a world over bodies the same way. The refinement theorems are:

- **Apply refines:** `abs (planFile cs) = Model.apply (absBundle b) (abs cs)`,
  up to normalisation of bodies and with labels and templates folded into
  the bundle's renderings. The model's rendering becomes the function L1
  uses, `renderItem cfg labels syn e`, so the two can't drift.
- **Check refines:** `checkFiles … = []` implies `Model.check (absBundle b)
  (abs cs) = []`.

The model's laws then carry over to the code.

### The theorems, about the code

These are stated on `applyFiles` and `checkFiles`, the functions the binary
calls, quantified over every configuration, bundle and set of files:

1. **Lossless reading:** if scanning succeeds, the files print back exactly.
2. **Locality:** `applyFiles … = .ok fs'` implies that each file of `fs'`
   has the same skeleton as before. The skeleton is the file with its bodies
   and its `sum=` and `dflt=` values masked.
3. **Idempotence:** `applyFiles … fs = .ok fs'` implies
   `applyFiles … fs' = .ok fs'`.
4. **Fixed point:** after `applyFiles`, `checkFiles` reports nothing stale.
5. **Slot preservation:** with the `dflt` caveat above.
6. **Theorem 1:** what a clean `check` guarantees, stated in full below.

### Theorem 1, precisely

```lean
theorem checkFiles_sound
    (W : World TeX) (b : Bundle (Image TeX) Verdict)
    (cfg : Config) (o : ApplyOpts) (fs : List (Path × String)) (env : MacroEnv)
    (hb : b.True W (Verdict.trusted cfg.allowedAxioms))
    (hc : checkFiles cfg b o fs env = []) :
    Files.True W cfg fs
```

Its pieces, in words:

- **`W : World TeX`** is the development as the extractor presents it, with
  renderings as TeX. This is `Imprimatur.World`, today's type.
- **`hb`** says the bundle is true of the world. Each entry names what its
  key names, its hashes and views are those of the key's statement, and its
  verdict is the world's. The verdict counts as *trusted* by the
  configuration's own rule, `Verdict.trusted cfg.allowedAxioms`: no
  `sorry`, no axioms outside `allowed_axioms`, and nothing untrusted in the
  cone, which is what `audit` checks through `trustProblems`. Nothing in the
  splicer establishes `hb`. It is the extractor's claim, and
  `bundleOf_true` shows that an honest extractor makes it true.
- **`hc`** says that `check` reports nothing, warnings included, for exactly
  the files the command line read. The warnings must be included because
  `unfaithful-rendering`, a rendering that doesn't read back, is a warning.
  A variant with `hc` only for errors drops the read-back conclusion below.
- **`Files.True W cfg fs`** says that every file scans, and every *claim* it
  makes is true of `W`. The claims are read off the lossless scan:

| Item in the file | Its claim |
|---|---|
| block or `\leaninline` on key `k`, in view `v` (as `itemView` computes it, with `notation=` and the theorem options), with body `r` | there are `S` and `r'` such that: `W.stmt k = some S`; `W.trusted k`; `W.render v S = some r'`; `normalize r = normalize (shape (fill (slots r) (renderItem cfg labels syn r')))`, where `renderItem` applies the alias's template, label and meta source exactly as `plan` does; and, if the item is live (typeset), `W.Reads r' S` |
| `\leanref` on `k` | `W.stmt k` is some statement (the key is declared). The link text makes no claim about the statement |
| `\leancheck[stmt=h]{k₁,…,kₙ}` | each `kᵢ` is declared and trusted, and `h` is the first 12 hex digits of the statement hash (for one key), or of the hash of the keys' hashes joined by commas (for several), as `checkHashes` computes |
| `\leancheck{k₁,…}` without `stmt=` | each `kᵢ` is declared and trusted |
| `\lean{k}` in an environment with `\leanok` (blueprint) | `k` is declared and trusted |
| `\lean{k}` without `\leanok`, `\leanindex`, `\leanhypref`, text | no claim |

Its corollaries are the model's, now about files:

- **The typeset mathematics is true:** the live claims of the first row are
  what a reader sees, and each shows a proved statement, rendered, reading
  back as it.
- **Attested prose faces its statement:** if the world's hash is injective
  *on 12-digit prefixes* among the statements in question, a `\leancheck`
  that checks clean names the statement the prose was checked against.
- **Prose and rules show their statements:** Theorems 6.3–6.5, with the
  anatomy assumptions.

Three features of this statement are forced by the code, and the paper
should say so.

- **Normalisation.** The code compares bodies up to line endings, trailing
  whitespace and blank lines at the ends, so the claim is equality *after*
  `normalize`. That this doesn't change what TeX typesets joins the trusted
  base.
- **Read-back only for live items.** `audit` checks `problems` only for
  items TeX typesets. An item in an `\iffalse` branch is regenerated and
  checked for staleness, but not read back.
- **Twelve digits.** `\leancheck` records 48 bits of the hash. The
  collision assumption for attested prose is therefore about 48-bit
  prefixes, not SHA-256. That is weak enough for an adversary to forge, but
  adequate against accident. Recording the full hash, or more digits, would
  strengthen the theorem's assumption at no cost to the proof.

### What stays unproved

- **The shell, kept small and reviewed:**
  - argument parsing;
  - reading files and following `\input` through `Doc.loadIO`, which calls
    the verified `Doc.load` with an IO reader;
  - atomic writes, all or nothing per run;
  - printing diagnostics and exit codes.
  The theorems quantify over the files read, so the shell is trusted only
  to pass them through, which is checkable by reading about 200 lines.
- **The configuration and bundle parsers** (`Toml`, `Bundle.parse`). The
  theorems quantify over every configuration and bundle, so these parsers
  are trusted only to read what the author or the extractor wrote. A
  round-trip theorem for the bundle's JSON is a later, separate piece of
  work; today it's a golden test.
- **The compiler and runtime:** that compiled code computes what its
  definitions say.
- **TeX:** that the scanner's reading of comments, `\verb`, verbatim
  environments and conditionals agrees with TeX's, given no `\catcode`
  tricks, and that normalisation doesn't change the typeset result.
  Proofs make the scanner the *specification* of reading a paper. They can't
  make it agree with TeX.
- **The extractor and the notation,** as in §18.5. Proving the extractor's
  rendering is a separate project, tracked in #76.

### Coding rules for `Splice.Core`, enforced by the lint

- **Style:** no `partial`, `while`, `repeat`, `unsafe`, `implemented_by`,
  `extern` or `!` indexing; recursion is structural, or well-founded on
  length; `Id.run`/`let mut` only where a lemma covers the loop.
- **Proofs:** no `sorry`. A lint step checks `#print axioms` of each paper
  theorem against `propext`, `Quot.sound` and `Classical.choice`.
- **Dependencies:** core only, as now, with no Mathlib or Batteries (DESIGN
  §4). A small `Splice.Core.Lemmas` holds the `List` and `String` lemmas the
  proofs need.

### Where the code and proofs live

- **The `splice` package gains a library, `SpliceProofs`,** holding the
  laws, the refinement and Theorem 1. It isn't a default target, so building
  the binary doesn't build proofs, but CI builds it on every commit, with
  warnings as errors. It adds no Lake dependencies.
- **`about/lean` requires the splice package by path,** which is allowed
  because it isn't shipped. Its copies of `SpliceModel` and
  `Imprimatur/Bundle.lean` go away, so the paper's theorems are the
  constants in `SpliceProofs`. `Stlc` stays, as the example.

## Migration plan

Each phase ends with the full test suite green, with goldens unchanged unless
a phase says otherwise. Each phase can be merged on its own.

| Phase | Work | Exit criterion |
|---|---|---|
| 0 | **Freeze behaviour.** A differential harness that runs old and new functions side by side on the property generator and on a corpus: every `test/tex` case, every example, the about paper, and the spike papers. It also times them, and runs a 1 MB document (see Performance). | Done: `SpliceTest.Diff` and `SpliceTest.Reference` run in `lake test`, with the timing gate (`splice/diff/scan-speed-*`, `splice/diff/scan-linear`) on the about paper repeated to 0.7 and 1.4 MB. |
| 1 | **One model.** Move `SpliceModel` into `splice/`, as a library that isn't a default target; the splicer's bundle copy takes the module name `Imprimatur.Bundle`; `about/lean` requires the splice package. The paper is unchanged. | Done: the paper builds byte for byte from the moved constants. |
| 2 | **Text kernel.** `toLf`, `normalize`, `withEol`, `dominantEol` on `List Char`, structural, with lemmas: `normalize` is idempotent; `normalize ∘ toLf = normalize`; `withEol` then `toLf` is `toLf`. | Done: `Splice.Core.Text`, with tail-recursive versions run by `@[csimp]`; proved `toLf` idempotent, and `toLf ∘ withCrlf = id` on text without `\r`. The `normalize` lemmas wait until a proof needs them. Old and new agree on the corpus and on 20,000 generated texts. |
| 3 | **Lossless scanner.** `Chunk`, `scan` and `print`, with the lossless, compositional and complete theorems. Positions come from chunk lengths. | Done: `Splice.Core.Scan.scan`, total and tail-recursive, with `print_scan` (lossless) proved; `scanSrcWith` runs it. It agrees with the old scanner (items, every position, inputs, labels, switches, errors) on the corpus and on 20,000 generated documents, noise and truncated files, at about 1.5× the old scanner's time, linearly. The compositional, stable and complete theorems are stated where phase 5 needs them. The old helpers stay for `Slots`, `Apply` and `Strip` until their phases. |
| 4 | **Bodies and slots.** `parseBody` (both slot forms, `outer`) and `Body.print`, lossless; `mergeBody` via the model's `fill`; `sum` and `dflt` on bodies; `dflt` in the model. | Done: `Splice.Core.Slots` cuts a region into parts (`printParts_parts`, lossless) and numbers repeated ids into the model's `Body`; `findSlots` is the core's; an ordinary merge is the model's `fill` (`mergeBody`), and `mergeBody_keeps` is slot preservation for it. The model's `SlotId` became (id, occurrence), because the code has always matched repeated ids by occurrence, and the model's lookup by id alone would have lost authors' text. Agrees with the old code on the corpus and generated regions. `sum` and `dflt` on bodies, and `dflt` in the model, move to phase 5, with the plan that uses them. |
| 5 | **Plan on chunks.** `planItem`, `planFile` and `applyFiles`; option edits on `OptsSyn`; `applyEdits` removed from the core. The stability lemma. | Done, with one change of approach. `plan` is `planItem`, `planFile` and folds; each changed item is rewritten within its own characters, and a file is its chunks printed again. Instead of a proved stability lemma, `plan` checks its own output before anything is written: it must scan again to the chunks built (`unstable-output`), and planning again on it must find nothing to do (`not-fixed-point`). Proved, of the code (`SpliceModel.Splicer`): text outside items never changes and items keep their place (`planOnce_text`, `planOnce_items`); idempotence and the fixed point (`plan_fixed_point`). Not yet proved: that within an item only the region and the options change (the edits `planItem` makes lie in those spans). The check found a real bug: a rendering holding `\begin` of an alias was written, and every later scan of the file failed. Goldens unchanged, plus `unstable-output`. |
| 6 | **Check.** `checkFiles` (audit, stale, sorting; macro warnings unchanged), and the refinement of `check`. | Theorem 1 proved for `checkFiles`. |
| 7 | **Paper and docs.** The paper's theorems name `SpliceProofs` constants; §9 and DESIGN §18 are rewritten (the trusted base loses "the splicer's parsing"); the lint rules above are on. | `imprimatur check` on the about paper is clean; lint passes. |
| 8 | **Later.** A JSON round trip for the bundle; `accept`, `strip` and `requests` (now outside the theorems) on chunks; `migrate-slots`. | — |

Phase 3 is the largest: it is a rewrite of 600 lines of imperative scanner,
with proofs. Phases 4–6 are mostly reorganisation around the model's existing
proofs.

## Performance

Today `check` on the about paper (85 KB of TeX, a 117 KB bundle) takes
about 0.18 s and 74 MB, most of it start-up and JSON. The extractor, run by
`imprimatur build`, takes seconds to minutes. So the splicer's speed matters
only if it changes complexity.

- **Constant factor.** A `Char` in an `Array` is an unboxed scalar; a
  `List Char` allocates a cell per character, about 3–4 words, and walking
  it chases pointers. Expect scanning and memory to be about 2–5× today's,
  with no change in complexity.
- **Rules that keep it linear.** These are enforced by review and by the
  timing gate below.
  - **No left-nested appends.** Output is built with accumulators, or in
    reverse and reversed once; never as `acc ++ piece` in a loop, which is
    quadratic on lists.
  - **Tail recursion on long lists.** A function that recurses once per
    character without a tail call uses a stack frame per character, about
    300,000 for a 300 KB file, and can overflow the stack. That is a crash,
    not just slowness. Every recursion over a file's characters is
    tail-recursive, with an accumulator. Its proof goes through a lemma
    equating it with the simple, non-tail-recursive definition, which is the
    one the theorems use.
  - **Convert once.** `String.toList` and `String.ofList` run once per file
    and once per output, never per item.
  - **No new quadratic work.** Matching slots by id and numbering repeated
    ids are O(n²) per block today, and stay so. A notation table with
    hundreds of slots is where that would show. A map by id, if needed, is a
    separate change.
- **The timing gate.** Phase 0's harness also times the old and new code on
  the largest corpus paper and on a generated document of twice its size.
  CI fails if the new code is more than 5× slower than the old, or if
  doubling the input more than about doubles its time. The same harness
  runs a 1 MB generated document, to catch stack overflow.

## Risks

- **Scanner fidelity.** A rewrite can change behaviour in corners such as
  nested groups in options, `\verb` at the end of a line, or conditionals
  across files. The differential harness and the goldens are the guard, and
  the old scanner is deleted only when they agree.
- **Proof upkeep across Lean releases.** Core's `List` and `String` lemmas
  change names between versions. Keeping our own small lemma file, and
  avoiding broad `simp` sets in the long proofs, limits the churn to one
  place.
- **Performance.** See Performance above: a constant factor if the rules
  hold, enforced by a timing gate.
- **Scope creep in the model.** The model must stay readable for the paper.
  Concrete detail (raw options, positions, line endings) lives in L1 with its
  own lemmas, and reaches the model only through `abs`.

## Decisions needed

1. **Representation in the core:** `List Char` (recommended) or `String`
   with positions. `String` would be faster and nearer today's code, but its
   position lemmas in core are thin.
2. **Where proofs live:** a `SpliceProofs` library in the splice package,
   built in CI but not by default (recommended), or a separate package that
   requires the splicer.
3. **Scope of the first milestone:** `apply` and `check`, including
   positional slots, comment blocks and several files (recommended);
   `migrate-slots`, `accept`, `strip` and `requests` follow in phase 8.
4. **Normalisation in Theorem 1:** state equality after normalisation
   (recommended, and what the code does), or make `apply` write bodies
   byte for byte and drop normalisation from `check`. The second is
   stronger but would make CRLF and trailing-space edits from Overleaf look
   stale.
