# Testing imprimatur

*For contributors. This file describes the test layers, says how to run
them, and keeps the traceability matrix.*

## Test architecture

### Layers

| Layer | What it covers | How it runs | Speed |
|---|---|---|---|
| **Unit** | pure functions: the TeX scanner and parser, balanced-brace extraction, checksum normalisation, slot extraction and merging, escaping, the `Doc` emitter (precedence, widths, flattening), canonical serialisation for hashing, TOML config, JSON reading and writing of the bundle | `lake test` in each package | seconds |
| **Property** | invariants over generated inputs (Properties, below) | same, using a small seeded generator | seconds |
| **Golden: extractor** | every view of every declaration in the fixture projects (Fixtures, below) | `lake test` in `extract/`, once per toolchain | about a minute per toolchain |
| **Golden: splicer** | pairs of TeX files before and after `apply`, `check` reports, `strip` output | `lake test` in `splice/` | seconds |
| **Trust (negative)** | each trust failure ([CONTRIBUTING.md](../CONTRIBUTING.md), principle 5) on purpose-built fixtures | runs with the extractor golden tests | about a minute |
| **End-to-end** | the `imprimatur build` command line on the example projects in all three modes, then `latexmk` with pdflatex and lualatex: no LaTeX errors, and `pdftotext` output matches golden text | `scripts/e2e.sh`, in CI | a few minutes |
| **Cross-toolchain** | the same fixture gives byte-identical bundles, apart from the `producer` field, and identical `stmtHash` values, on every supported toolchain | CI matrix job comparing bundles | a few minutes |

### Fixtures

The fixtures are small Lean projects under `test/fixtures/`, with **no
Mathlib**, so CI can build them on every toolchain in seconds. Each targets
part of the design:

| Fixture | Contents | Covers |
|---|---|---|
| `Basic` | theorems with implicit, instance and explicit binders; definitions; a structure; a docstring on every kind | the `lean`, `meta`, `math` and `prose` views; keys; entries |
| `Semantics` | a small STLC with an inductive typing relation and a small-step relation; value predicates; well-formedness side conditions; docstring labels `/-- T-App: … -/` | the `rules` and `grammar` views, rule labels, premise conventions, `include`/`exclude`, slots |
| `Notation` | constants used in every kind of notation rule: infix, nested pattern, `hide`, `variant`, `flatten`, `width`, `prec` | the notation language (D§7.5) |
| `Patterns` | definitions by cases, nested cases that reuse a name, a case on a disjoint union, a dependent `if`, list literals | `latex_style pattern_matching` and `lists`, binder names in cases and equations (D§7.5) |
| `Trust` | `sorry` directly in a proof, and three levels deep in the cone; a custom `axiom`; `partial` and `unsafe` definitions; a theorem whose hypothesis definition exists in two versions (`Weak := True`, `Strong := …`), switched by a build option | D§7.7, and the drift tests of D§10.3 |
| `ModuleSys` | files with `module` headers, private proofs, and `import` with and without `all` | the `private`-level import (D§4, constraint 7) on the toolchains that have the module system |
| `Categories` | two notation modules over one small language: `Strict`, with `latex_style categories := strict`, and `Clash`, which gives two types one letter | strict metavariables and their errors (D§7.5, D§18.3, condition 5) |
| `Manifests` | a comparator-style `ChallengeX.lean` plus a JSON manifest; a mini blueprint `.tex` using `\lean{}` and `\leanok` | D§10.5, D§9.3 |

The TeX fixtures live under `test/tex/`. Each is a small document exercising
one splicer behaviour:
- blocks inside macro arguments, nested `\input`, and `\include`;
- commented-out blocks, and `verbatim` blocks containing fake markers;
- CRLF line endings;
- Unicode;
- hand-edited blocks, and edited slots;
- slots declared by position, as an earlier tool used them.

### Properties

The splicer is where a bug corrupts authors' files, so it gets the most
property tests. A small seeded generator (Tooling, below) produces TeX documents with
random prose, braces, comments, `verbatim`, blocks and slots, and random
bundles.

| Property | Statement |
|---|---|
| **Locality** | `apply` never changes a byte outside a block's generated region and its `sum=` and `dflt=` options. This is checked by masking the blocks and comparing. |
| **Idempotence** | `apply(apply(d, b), b) = apply(d, b)`. |
| **Fixed point** | `check(apply(d, b), b)` reports nothing stale. |
| **Slot preservation** | for every slot id present both before and after, the slot's text after `apply` equals its text before. |
| **Edit detection** | for any single-character edit inside a generated region, outside slots, `check` reports a hand edit; inside a slot, it doesn't. |
| **Normalisation** | converting a document to CRLF, or adding trailing whitespace, doesn't change any checksum's verdict. |
| **Strip** | after `strip`, the output contains no imprimatur markers, and contains every generated region verbatim. |
| **Scanner robustness** | on any input, including truncated files, unbalanced braces and markers inside `verbatim`, `scan` either succeeds or reports an error with a position. It never crashes, and never writes a file. |
| **Hash invariance** | in the extractor, renaming bound variables or universe parameters doesn't change `stmtHash`; changing a hypothesis does. |

### Differential tests

While the splicer is rewritten as a verified core (docs/verified-splicer.md),
each rewritten function is run beside the code it replaces, kept verbatim in
`splice/test/SpliceTest/Reference.lean`, and the two must agree: on
generated input (`splice/diff/text`), and on every `.tex` file of the test
cases and the examples (`splice/diff/text-corpus`). A
function's reference copy goes when its phase is complete. The scanner is
compared on whole scan results, for typeset and untypeset files, with and
without switches (`splice/diff/scan*`), and timed against the reference on
the built semantics example repeated to 0.8 and 1.6 MB: at most five times slower, and
no worse than linear (`splice/diff/scan-speed-*`, `splice/diff/scan-linear`).
The timing gate caught a block reader that measured the rest of the file
for every block, which made scanning quadratic.

### Tooling

- **Our own small test harness** in a test-only package: `check`,
  `checkEq`, golden comparison with `UPDATE_GOLDEN`, and a seeded generator
  that reproduces failures from a printed seed.
  - The test harness of an earlier tool is the model.
  - Not **Plausible** (the Lean property-testing library): decided at M0, so
    that test packages need nothing that might not support every toolchain
    in the range.
- **Golden files** are stored next to their tests. Updating them requires
  `UPDATE_GOLDEN=1` and shows up as a reviewable diff.
- **`scripts/test-all.sh`** runs every layer that CI runs, so a contributor
  can reproduce CI locally with a single command.

### Continuous integration (GitHub Actions)

| Job | Matrix | Contents |
|---|---|---|
| `splice` | one toolchain | build with warnings as errors; unit, property and golden tests |
| `extract` | v4.28.0-rc1, v4.31.0, v4.34.1 (the three motivating projects), plus the latest stable | build the fixtures; unit, golden and trust tests |
| `cross-toolchain` | needs `extract` | compare bundles and `stmtHash` values across the matrix |
| `e2e` | one toolchain, with TeX Live (`pdflatex` and `lualatex`) | `scripts/e2e.sh` on `examples/` in all three modes |
| `lint` | — | markdown links, JSON schema validation of golden bundles, the traceability matrix has no orphan entries |

**Everything is in this repository.** Every test runs from this repository
alone, so anyone can contribute without access to the papers imprimatur is
used for. The fixtures and examples stand in for them, with no Mathlib. Projects that use imprimatur check their own papers
with it, in their own repositories.

## Running the tests

| What | Command | Where |
|---|---|---|
| everything CI runs | `scripts/test-all.sh` | repository root |
| the test harness's own tests | `lake test` | `testkit/` |
| extractor tests (build the fixtures first) | `lake test` | `extract/test/` |
| one part of the extractor's fixture tests (`drift`, `index`, `categories`, `challenges`, or a fixture such as `Semantics`) | `lake test -- --part NAME` | `extract/test/` |
| end-to-end examples (needs TeX Live) | `scripts/e2e.sh` | repository root |
| splicer tests | `lake test` | `splice/test/` |
| the extractor on another toolchain | `scripts/test-all.sh --toolchain v4.31.0` | repository root |
| lint (links, schema, this matrix) | `scripts/lint.sh` | repository root |

The extractor's fixture tests each import a Lean environment, and in one
process those add up to more memory than a laptop has. So `lake test` in
`extract/test/` runs each part of them in a process of its own, and adds up
the results; peak memory is about 3.5 GB.

Each test package is a separate Lake package that requires the package it
tests and `testkit/`. The shipped packages therefore never depend on test
code ([CONTRIBUTING.md](../CONTRIBUTING.md), principle 6). A test package has no `lean-toolchain` of its own; `elan`
finds the one in the package it tests.

**Environment variables.**

- `UPDATE_GOLDEN=1` rewrites golden files instead of comparing them. Review
  the resulting diff line by line before committing it.
- `IMPRIMATUR_CASES=n` sets the number of cases per property (default 100;
  M1's gate is 10,000).
- `IMPRIMATUR_SEED=s` fixes the base seed. A failing property prints the
  seed and case count that reproduce it.
- `IMPRIMATUR_MAX_SIZE=n` bounds the size of generated values (default 30).

**Builds** use `lake build --wfail` in CI and in `scripts/test-all.sh`. The
lakefiles don't make warnings errors, so that a user on a newer toolchain
isn't broken by a new deprecation warning.

## Test names

Every check has a name of the form `package/area/what`, for example
`splice/prop/idempotence`. The matrix below refers to tests by these names,
and `scripts/check-traceability.py` checks that every name in it appears as a
string literal in a test source. Checks done by scripts are named
`lint/…` (in `scripts/`) or `e2e/…` (in `scripts/e2e.sh`).

**Golden bundles of the extractor.** `extract/test/golden/<fixture>.bundle.json`
holds the bundle of each fixture under `test/fixtures/`, with the toolchain in
`producer.lean` masked as `v4.x`. The same golden files must hold on every
toolchain in the CI matrix.

**Golden tests of the splicer.** Each directory under `test/tex/` is a case:
a document, its configuration and bundles, and a `steps` file of commands.
The test runs the steps and compares a transcript with
`splice/test/golden/<case>.txt` (see `splice/test/SpliceTest/Golden.lean`).

## Traceability matrix

Lean has no coverage tool, so this matrix stands in for coverage ([CONTRIBUTING.md](../CONTRIBUTING.md), principle 1).
There is one row per requirement, and every numbered section of
[DESIGN.md](../DESIGN.md) has at least one row. **Tests** lists test names,
or `—` if there are none yet. **When** is the milestone that brings the tests
(DESIGN §17), or `n/a` for sections that describe no behaviour.

`scripts/check-traceability.py` (run by `scripts/lint.sh` and the `lint` CI
job) fails if a section of DESIGN.md has no row, a row names a section that
doesn't exist, or a row names a test that doesn't exist.

| Section | Requirement | Tests | When |
|---|---|---|---|
| D§1 | goals and non-goals | — | n/a |
| D§2 | motivating projects | — | n/a |
| D§3 | prior art | — | n/a |
| D§4 | (1) the extractor builds and runs on every supported toolchain | `extract/version/lean`, `extract/golden/Basic` | M0 |
| D§4 | (2) the splicer imports nothing from Lean but `Lean.Data.Json` | `lint/splice-imports` | M1 |
| D§4 | (3) a notation rule naming a missing constant fails at build time (checked when the `Notation` fixture builds; the messages are tested by hand) | `extract/golden/Notation` | M4 |
| D§4 | (4) every declaration has a default rendering (the `lean` view) | `extract/golden/Basic` | M2 |
| D§4 | (5) external mode changes nothing in the host project | `e2e/external`, `e2e/semantics` | M3 |
| D§4 | (6) shipped packages have no Lake dependencies | `lint/no-deps` | M0 (lint) |
| D§4 | (7) environments are imported at `private` level | `extract/modules/private-sorry-seen`, `extract/modules/sorry-through-import-all`, `extract/golden/ModuleSys` | M2 |
| D§5 | extractor and splicer communicate only through the bundle | `splice/version/schema`, `extract/version/schema` | M1 |
| D§5 | `imprimatur build` runs scan, export, apply; `check` passes after it | `e2e/minimal`, `e2e/sidecar` | M2 |
| D§5 | `--timing` logs the splicer's and the extractor's phases, entries, views and formulas, and the summary names the slowest | `splice/timing/summary-phases`, `splice/timing/summary-slowest-formula`, `e2e/external` | M6 |
| D§6.1 | `imprimatur.toml` is parsed; unknown keys and bad values are reported | `splice/toml/parses`, `splice/toml/duplicate-key`, `splice/toml/error-line`, `splice/config/parses`, `splice/config/unknown-key`, `splice/config/alias-needs-view`, `splice/config/url-needs-template`, `splice/golden/config-errors` | M1 |
| D§6.2 | the notation module is elaborated and its names resolved, in-project and as a file in external mode | `extract/golden/Notation`, `e2e/minimal`, `e2e/external` | M4 |
| D§6.3 | sidecar and in-project modes | `e2e/minimal`, `e2e/sidecar` | M2 |
| D§6.3 | external mode, with `imprimatur toolchain install` | `e2e/external` | M3 |
| D§7.1 | `Doc` emitter: escaping, parenthesisation, line breaking | `extract/doc/escape-specials`, `extract/doc/width-symbols`, `extract/doc/width-wrappers`, `extract/doc/width-spacing`, `extract/doc/width-scripts`, `extract/doc/width-given`, `extract/doc/no-parens-left-assoc`, `extract/doc/parens-right`, `extract/doc/parens-tighter`, `extract/doc/no-parens-looser`, `extract/doc/width-counts-parens`, `extract/doc/fits-unbroken`, `extract/doc/breaks-outermost`, `extract/doc/breaks-deeper-when-needed`, `extract/doc/break-after-control-space` | M4 |
| D§7.2 | notation matches `Expr`; unmatched subterms are rendered as functions, or delaborated | `extract/golden/Notation`, `extract/notation/no-render-errors` | M4 |
| D§7.3 | `lean` view, with semantic token macros | `extract/tokens/line`, `extract/tokens/subscripts-and-primes`, `extract/names/strip`, `extract/golden/Basic` | M2 |
| D§7.3 | `meta` view; the splicer fills its source location per profile | `extract/markdown/code`, `extract/markdown/maths`, `extract/markdown/unbalanced-maths`, `extract/golden/Basic`, `splice/golden/meta-source` | M2 |
| D§7.3 | `prose` labels only hypotheses the paper refers to (`\leanhypref`) | `extract/prose/hyp-referred-labelled`, `extract/prose/hyp-unreferred-unlabelled`, `splice/golden/hyprefs` | M5 |
| D§7.3 | `math` and `prose` views | `extract/golden/Notation`, `e2e/minimal`, `e2e/fixture-views` | M4 |
| D§7.3 | the views that index the document (`conventions`, `vocabulary`, `provenance`) see every other block, list the library's notation, or the project's with `scope`, and give results their kind and page | `extract/index/no-warnings`, `extract/index/conventions-shown`, `extract/index/conventions-order`, `extract/index/provenance-theorem`, `extract/index/vocabulary-library-only`, `extract/index/vocabulary-project`, `extract/index/golden` | M6 |
| D§7.3 | `clauses` and `grammar|display`: definitions as `lhs ≜ rhs` rows and types as grammar rows, for a declaration or a `latex_display`, with descriptions as slots and every formula read back | `extract/display/clauses`, `extract/display/clauses-one-definition`, `extract/display/grammar`, `extract/display/title-names-declaration`, `extract/display/validated` | M6 |
| D§7.5 | `latex_style categories := strict`: a variable of a category's type is written with its letter and its own subscripts and primes; variables that then print alike, and a letter for two types, are errors | `extract/names/decorations`, `extract/categories/strict-renames`, `extract/categories/strict-clean`, `extract/categories/strict-print-alike`, `extract/categories/unique-letter` | M6 |
| D§18.4 | the one reading of a formula is the one the renderer expected, with `⁇` for forms it does not say how to read; a reading that differs is a misread | `extract/validate/matches`, `extract/validate/reading-left`, `extract/validate/misread-caught` | M6 |
| D§18.4 | a constant applied only to implicit arguments reads back as itself, not as a misread | `extract/validate/implicit-only-application` | M6 |
| D§7.3 | `rules` and `grammar` views | `extract/golden/Semantics`, `e2e/fixture-views`, `e2e/semantics` | M5 |
| D§7.3 | custom views through `@[latex_view]`, with the document inventory | `extract/golden/Semantics` (`fixture.rulelist`) | M5 |
| D§7.4 | rule label precedence; `latex_rules` templates, anchors, `sep`, `doc_labels`; groups across inductives | `extract/golden/Semantics` | M5 |
| D§7.5 | notation rules: patterns, templates, `prec`, `width`, `hide`, `variant`, `flatten`, typed patterns, lookup order, metavariables | `extract/golden/Notation`, `extract/doc/template-prime`, `extract/doc/template-longest`, `extract/doc/template-unknown`, `extract/doc/metavar-subscript`, `extract/doc/metavar-digits`, `extract/doc/metavar-prime`, `extract/doc/metavar-long`, `extract/doc/metavar-renamed`, `splice/golden/notation-config` | M4 |
| D§7.5 | packs: every rule has a golden use, and the output typesets with both engines | `extract/notation/every-pack-rule-used`, `e2e/fixture-views` | M4 |
| D§7.5 | the bundle records the macros each rendering uses | `extract/golden/Notation` | M4 |
| D§7.5 | binder patterns, partial applications, `flatten` with `sep`, `assoc`, `latex_style`, `latex_entry`, Greek letters, several notation files | `extract/golden/Notation` (`math:binders`), `extract/golden/Semantics` | M5 |
| D§7.5 | `break`: a long rendering breaks the line before a rule's operator | `extract/notation/break-before-operator` | M6 |
| D§18.2 | the splicer's laws and Theorem 1, proved for a model of the splicer (`splice/SpliceModel`, built with the splicer); the paper presenting them is built and checked in its own repository | `lint/verified` | M5 |
| D§18.4 | translation validation: tokens, productions of rules, readings counted up to two, sorts and type variables, coercions, chains, the built-in forms | `extract/validate/tokens`, `extract/validate/tokens-code`, `extract/validate/production`, `extract/validate/production-atomic`, `extract/validate/production-coercion`, `extract/validate/ambiguous`, `extract/validate/no-reading-without-parens`, `extract/validate/one-reading-with-parens`, `extract/validate/assoc-left`, `extract/validate/assoc-none`, `extract/validate/sorts`, `extract/validate/coercion-one-reading`, `extract/validate/flatten`, `extract/validate/builtin-implies`, `extract/validate/builtin-forall`, `extract/validate/tyvar-ill-sorted`, `extract/validate/tyvar-unknown`, `extract/validate/tyvar-binds`, `extract/validate/sort-arrow`, `extract/validate/sort-arrow-differs`, `extract/validate/sort-args-differ`, `extract/validate/sort-args-open`, `extract/validate/coercion-sorts`, `extract/validate/coercion-sorts-needed`, `extract/validate/application-curried`, `extract/validate/synonym`, `extract/validate/unmodelled` | M5 |
| D§18.4 | chains of hidden coercions: the renderer hides a coercion only where the reader's chain rule allows it, so the reader reads what it prints; the counterexample of docs/coercion-chains.md prints apart | `extract/chain/pun-printed-apart`, `extract/prop/chain-rule-reads-renderings` | M6 |
| D§7.6 | a premise a metavariable convention hides is still said: the prose view binds the variable in the predicate, and the table of conventions lists the convention with where the predicate is shown | `extract/index/convention-binds`, `extract/index/convention-row`, `extract/index/convention-shown`, `extract/index/golden` | M6 |
| D§18.4 | an application has the function's codomain for its sort, and a function of a named type or of unknown sort still applies | `extract/validate/application-typed`, `extract/validate/application-named`, `extract/validate/application-unknown`, `extract/validate/application-ill-typed` | M6 |
| D§18.4 | list literals, and types such as `[n]` not read as lists; `Sort*`; a constant applied is one reading | `extract/validate/list-literal`, `extract/validate/list-or-type`, `extract/validate/type-not-list`, `extract/validate/sort-star-type`, `extract/validate/sort-star-not-value`, `extract/validate/app-constant` | M5 |
| D§18.3 | side condition 5: a variable that prints as another type's category letter is reported | `extract/golden/Semantics` (`Stlc.size_pos`) | M5 |
| D§18.4 | the bundle records each view's problems; `check` warns at typeset blocks only, for the view they show | `extract/golden/Notation`, `extract/golden/Semantics`, `splice/golden/validation` | M5 |
| D§18.4 | a template that drops a pattern variable is a warning | the `#guard_msgs` test in `extract/test/ExtractTest/Validate.lean` | M5 |
| D§7.5 | `latex_style pattern_matching` and `lists`; case patterns and λ binders renamed when in scope; unused binders `_`; proof λs hidden; constructors shown in patterns; equation binders named by category or parameter, authors' names kept | `extract/golden/Patterns`, `extract/golden/Semantics`, `e2e/semantics` | M5 |
| D§7.6 | premise conventions | `extract/golden/Semantics`, `e2e/fixture-views` | M5 |
| D§7.7 | axioms and `sorry` | `extract/trust/direct-sorry`, `extract/trust/custom-axiom`, `extract/trust/classical-axioms`, `extract/trust/sorry-in-proof-chain`, `extract/trust/sorry-in-statement`, `extract/trust/custom-axiom-trust`, `extract/modules/private-sorry-seen` | M2 |
| D§7.7 | dependency cone up to `trusted_prefixes`, with reasons | `extract/trust/cone-sorry`, `extract/trust/cone-partial`, `extract/trust/cone-clean`, `splice/golden/cone` | M3 |
| D§7.7 | the axioms of an inductive type include those its constructors' types depend on (a cycle), and a cone's nodes and the axioms are the same whichever entry asks first | `extract/trust/cycle-axioms`, `extract/trust/axioms-order`, `extract/golden/Basic` | M6 |
| D§7.7 | `stmtHash`: insensitive to binder and universe names, sensitive to meaning, stable across toolchains | `extract/prop/hash-binder-names`, `extract/prop/hash-universe-names`, `extract/prop/hash-sees-constants`, `extract/prop/hash-ignores-mdata`, `extract/hash/sorry-tag-ignored`, `extract/hash/binder-kind-matters`, `extract/trust/same-hash-renamed-binder`, `extract/trust/same-hash-renamed-universes`, `extract/trust/weakened-hypothesis-drifts`, `extract/golden/Trust` | M3 |
| D§7.7 | `sigHash` change alone is a warning | `extract/trust/weakened-hypothesis-same-signature`, `extract/trust/different-sig-renamed`, `splice/golden/drift` | M3 |
| D§8 | bundles are deterministic: sorted keys, no timestamps; the same on every toolchain | `extract/json/sorted`, `extract/golden/Basic`, `extract/golden/ModuleSys`, `extract/golden/Trust` | M2 |
| D§8 | bundles contain no absolute paths, user names, URLs or commit hashes | `extract/golden/Basic`, `splice/bundle/absolute-path` | M2 |
| D§8 | bundles are read and checked against the rules of `schema/bundle.schema.json`; golden bundles validate against the schema | `splice/bundle/parses`, `splice/bundle/schema-version`, `splice/bundle/absolute-path`, `splice/bundle/missing-views`, `splice/golden/bundle-errors`, `lint/bundle-schema` | M1 |
| D§8 | a view that fails to render is recorded in `errors`, and is an error only if requested | `extract/golden/Basic`, `splice/golden/failures` | M2 |
| D§8 | the bundle is a Lean type, of which the file is the JSON: an extractor's bundle survives parse and render byte for byte; both packages hold the same copy of the module | `splice/bundle/round-trip`, `lint/bundle-copies` | M6 |
| D§9.1 | `leanblock`, `\leaninline`, `\leanref`, `\leancheck`, `\leanindex` are recognised | `splice/scan/forms`, `splice/scan/options`, `splice/scan/check-keys`, `splice/golden/basic` | M1 |
| D§9.1 | block options: `include`/`exclude` and the theorem modifiers (`show`/`hide` are not implemented) | `extract/golden/Semantics`, `splice/golden/basic` | M5 |
| D§9.2 | alias options `label`, `repeat_suffix`, `template`, `comment` | `splice/golden/aliases` | M5 |
| D§10.1 | definitions of imprimatur's macros are not uses | `splice/golden/definitions` | M5 |
| D§10.1 | conditionals: blocks in branches that are off (`\iffalse`, `\newif` switches) are maintained but not typeset; the document inventory | `splice/golden/conditionals`, `splice/golden/aliases` | M5 |
| D§9.2 | aliases map existing environments onto `leanblock` | `splice/config/alias-slots`, `splice/golden/basic`, `splice/golden/positional-slots` | M1 |
| D§9.3 | blueprint `\lean{…}` read as check-only references; `\leanok` cross-checked | `splice/golden/blueprint` | M3 |
| D§9.3 | `--blueprint-compat` writes `\lean{…}` | — | M6 |
| D§9.4 | a document compiles with `imprimatur.sty` (pdflatex and lualatex) and shows the spliced content | `e2e/minimal`, `e2e/sidecar` | M2 |
| D§9.5 | slots keep their text by id; slot edits are not hand edits | `e2e/semantics`, `splice/slots/merge`, `splice/checksum/ignores-slot-text`, `splice/prop/slot-preservation`, `splice/prop/edit-detection`, `splice/golden/slots`, `splice/golden/unicode` | M1 |
| D§9.5 | orphaned slots are dropped with their text printed; `--rename-slot` | `splice/slots/orphans`, `splice/slots/rename`, `splice/golden/slots` | M1 |
| D§9.5 | slots still holding the defaults recorded in `dflt=` take new defaults; edited ones keep their text, and a changed default is reported once | `splice/golden/slot-defaults`, `splice/golden/slots`, `splice/prop/slot-preservation` | M6 |
| D§9.5 | slots declared by position; `migrate-slots` | `splice/slots/found`, `splice/slots/outer`, `splice/golden/positional-slots`, `splice/golden/migrate-slots` | M1 |
| D§10.1 | `scan` follows `\input`, `\include`, `\subfile`, skips comments, `\verb` and `verbatim`; malformed markup is an error with a position | `splice/scan/inputs`, `splice/scan/comment-skipped`, `splice/scan/verb-skipped`, `splice/scan/verbatim-skipped`, `splice/scan/unclosed-block`, `splice/prop/scanner-robustness`, `splice/prop/scanner-truncated`, `splice/golden/basic`, `splice/golden/comments-verbatim`, `splice/golden/macro-args`, `splice/golden/parse-errors`, `splice/golden/outside` | M1 |
| D§10.2 | `apply` refuses output that doesn't scan back to what it built, or that applying again would change | `splice/golden/unstable-output` | M6 |
| D§10.2 | `apply` is idempotent, changes nothing outside regions, `sum=` and `dflt=`, and touches only changed files | `splice/prop/idempotence`, `splice/prop/locality`, `splice/prop/fixed-point`, `splice/golden/basic` | M1 |
| D§10.2 | checksums normalise line endings and trailing whitespace | `splice/prop/normalisation`, `splice/normalize/crlf-and-trailing`, `splice/golden/crlf` | M1 |
| D§10.2 | hand edits are refused without `--force`; nothing is written when there is an error | `splice/prop/edit-detection`, `splice/golden/hand-edit` | M1 |
| D§10.2 | missing keys are errors; `--keep-stale` | `splice/golden/failures` | M1 |
| D§10.2 | writes keep line endings and encoding | `splice/golden/crlf`, `splice/golden/unicode` | M1 |
| D§10.3 | `check` reports stale blocks, with `--diff` | `splice/diff/lines`, `splice/golden/slots`, `splice/golden/positional-slots` | M1 |
| D§10.3 | `check` reports broken references | `splice/golden/failures` | M1 |
| D§10.3 | `check` reports untrusted results (splicer side; the extractor fills in the data in M2) | `splice/golden/failures` | M1 |
| D§10.3 | `check` reports drift; `accept` records the new hash | `splice/golden/drift` | M3 |
| D§10.3 | `check` warns of undefined macros and orphaned slots | `splice/macros/defined`, `splice/macros/loaded`, `splice/golden/macros`, `splice/golden/slots` | M6 |
| D§10.3 | `check` exit codes: non-zero on anything but warnings | `splice/golden/failures`, `splice/golden/config-errors`, `splice/golden/slots` | M1 |
| D§10.4 | `strip` removes markers and keeps generated content | `splice/slots/unwrap`, `splice/prop/strip`, `splice/golden/strip` | M1 |
| D§10.5 | comparator manifests, including `@challenge` entries | `splice/golden/manifests`, `extract/manifests/challenge-keys`, `extract/manifests/challenge-statement-matches`, `extract/manifests/unknown-challenge`, `extract/golden/Manifests` | M3 |
| D§11 | profiles `relative` (default), `url`, `none` for `\leanref` and the `meta` view | `splice/tex-escape`, `splice/config/url-needs-template`, `splice/golden/refs`, `splice/golden/meta-source` | M1 |
| D§11 | `check --anonymous` | — | M6 |
| D§12 | `show` prints one key's renderings and problems, fails on a missing key, and writes nothing | `e2e/show` | M6 |
| D§12 | every command in the table exists and prints usage | — | M6 |
| D§13 | the supported toolchain range is documented and enforced | — | M6 |
| D§13 | the same fixture gives the same bundle on every toolchain, apart from `producer` | `extract/golden/Basic`, `extract/golden/ModuleSys`, `extract/golden/Trust` | M2 |
| D§13 | the same declaration has the same `stmtHash` on every toolchain | `extract/golden/Trust`, `extract/golden/Basic`, `extract/golden/Manifests` | M3 |
| D§13 | the splicer accepts the current and previous bundle schema | `splice/version/schema`, `splice/bundle/schema-version` | M1 |
| D§14 | testing (this file) | — | n/a |
| D§15 | repository layout | — | n/a |
| D§16 | adoption in the motivating projects; each is checked in its own repository, so that imprimatur's tests need nothing outside this one | — | n/a |
| D§17 | roadmap | — | n/a |
| D§18.1 | what a document claims | — | n/a |
| D§18.3 | correctness: faithful rendering (Theorem 2) | — | n/a |
| D§18.5 | the trusted base | — | n/a |
| D§19 | open questions | — | n/a |
| D§A | claims still to check | — | n/a |

The test harness has its own checks (`testkit/harness/counts`,
`testkit/gen/splitmix-pinned` and so on), which aren't listed here because
they test the tests.
