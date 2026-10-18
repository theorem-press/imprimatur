# imprimatur — build and test plan

*Companion to [DESIGN.md](DESIGN.md), and written for the people building
imprimatur. DESIGN.md says what to build; this file says in what order, and
how we will know each part is right. Section references like "D§10.2" point
into DESIGN.md.*

## 1. Principles

1. **Every requirement has a test, and every test names its requirement.**
   `docs/TESTING.md` keeps a traceability matrix from each design section
   (D§…) to the tests that cover it. Lean has no coverage tool, so this
   matrix stands in for coverage. A pull request that changes behaviour
   updates the matrix.
2. **Tackle the risks first.** The design rests on three assumptions that
   could fail, and each gets a short spike (§3) before code is built on it:
   - external mode works;
   - statement hashes can be made stable across toolchains;
   - imprimatur can match the output of llmbda's existing tool.
3. **Test-first for the splicer and the trust checks.** These are the parts
   whose bugs do harm. A bug in the splicer corrupts authors' files. A bug in
   the trust checks lets an unchecked claim through. Their tests are written
   before their code.
4. **Golden files for rendering.** We can't specify rendered LaTeX exactly in
   advance. So views are pinned by golden output: reviewed once, then
   changed only deliberately (`UPDATE_GOLDEN=1`, with the diff reviewed in
   the pull request).
5. **Failure modes are features.** Every error and warning the design
   promises (hand edit, orphaned slot, drift, `sorry` deep in a dependency
   cone, disallowed axiom, missing key, anonymity leak) has a fixture that
   triggers it and a test that the message and exit code are right.
6. **No dependencies in shipped code** (D§4, constraint 6). Test code may
   have dependencies, but only in separate test packages that users never
   build.

## 2. Test architecture

### 2.1 Layers

| Layer | What it covers | How it runs | Speed |
|---|---|---|---|
| **Unit** | pure functions: the TeX scanner and parser, balanced-brace extraction, checksum normalisation, slot extraction and merging, escaping, the `Doc` emitter (precedence, widths, flattening), canonical serialisation for hashing, TOML config, JSON reading and writing of the bundle | `lake test` in each package | seconds |
| **Property** | invariants over generated inputs (§2.3) | same, using a small seeded generator | seconds |
| **Golden: extractor** | every view of every declaration in the fixture projects (§2.2) | `lake test` in `extract/`, once per toolchain | about a minute per toolchain |
| **Golden: splicer** | pairs of TeX files before and after `apply`, `check` reports, `strip` output | `lake test` in `splice/` | seconds |
| **Trust (negative)** | each trust failure (§1, principle 5) on purpose-built fixtures | runs with the extractor golden tests | about a minute |
| **End-to-end** | the `imprimatur build` command line on the example projects in all three modes, then `latexmk` with pdflatex and lualatex: no LaTeX errors, and `pdftotext` output matches golden text | `scripts/e2e.sh`, in CI | a few minutes |
| **Cross-toolchain** | the same fixture gives byte-identical bundles, apart from the `producer` field, and identical `stmtHash` values, on every supported toolchain | CI matrix job comparing bundles | a few minutes |
| **Real-world integration** | llmbda (parity, §4 M5), PLanet and the math catalogue, all Mathlib-based | `scripts/integration.sh`, run locally and before releases, not in CI (§2.5) | tens of minutes |

### 2.2 Fixture Lean projects

The fixtures are small Lean projects under `test/fixtures/`, with **no
Mathlib**, so CI can build them on every toolchain in seconds. Each targets
part of the design:

| Fixture | Contents | Covers |
|---|---|---|
| `Basic` | theorems with implicit, instance and explicit binders; definitions; a structure; a docstring on every kind | the `lean`, `meta`, `math` and `prose` views; keys; entries |
| `Semantics` | a small STLC with an inductive typing relation and a small-step relation; value predicates; well-formedness side conditions; docstring labels `/-- T-App: … -/` | the `rules` and `grammar` views, rule labels, premise conventions, `include`/`exclude`, slots |
| `Notation` | constants used in every kind of notation rule: infix, nested pattern, `hide`, `variant`, `flatten`, `width`, `prec` | the notation language (D§7.5) |
| `Trust` | `sorry` directly in a proof, and three levels deep in the cone; a custom `axiom`; `partial` and `unsafe` definitions; a theorem whose hypothesis definition exists in two versions (`Weak := True`, `Strong := …`), switched by a build option | D§7.7, and the drift tests of D§10.3 |
| `ModuleSys` | files with `module` headers, private proofs, and `import` with and without `all` | the `private`-level import (D§4, constraint 7) on the toolchains that have the module system |
| `Manifests` | a comparator-style `ChallengeX.lean` plus a JSON manifest; a mini blueprint `.tex` using `\lean{}` and `\leanok` | D§10.5, D§9.3 |

The TeX fixtures live under `test/tex/`. Each is a small document exercising
one splicer behaviour:
- blocks inside macro arguments, nested `\input`, and `\include`;
- commented-out blocks, and `verbatim` blocks containing fake markers;
- CRLF line endings;
- Unicode;
- hand-edited blocks, and edited slots;
- slots declared by position, as llmbda uses them.

### 2.3 Properties

The splicer is where a bug corrupts authors' files, so it gets the most
property tests. A small seeded generator (§2.4) produces TeX documents with
random prose, braces, comments, `verbatim`, blocks and slots, and random
bundles.

| Property | Statement |
|---|---|
| **Locality** | `apply` never changes a byte outside a block's generated region and its `sum=` option. This is checked by masking the blocks and comparing. |
| **Idempotence** | `apply(apply(d, b), b) = apply(d, b)`. |
| **Fixed point** | `check(apply(d, b), b)` reports nothing stale. |
| **Slot preservation** | for every slot id present both before and after, the slot's text after `apply` equals its text before. |
| **Edit detection** | for any single-character edit inside a generated region, outside slots, `check` reports a hand edit; inside a slot, it doesn't. |
| **Normalisation** | converting a document to CRLF, or adding trailing whitespace, doesn't change any checksum's verdict. |
| **Strip** | after `strip`, the output contains no imprimatur markers, and contains every generated region verbatim. |
| **Scanner robustness** | on any input, including truncated files, unbalanced braces and markers inside `verbatim`, `scan` either succeeds or reports an error with a position. It never crashes, and never writes a file. |
| **Hash invariance** | in the extractor, renaming bound variables or universe parameters doesn't change `stmtHash`; changing a hypothesis does. |

### 2.4 Test tooling

- **Our own small test harness** in a test-only package: `check`,
  `checkEq`, golden comparison with `UPDATE_GOLDEN`, and a seeded generator
  that reproduces failures from a printed seed.
  - The llmbda `RunLatex/Test.lean` harness is the model.
  - We will look at **Plausible** (the Lean property-testing library) for
    the test package only. We adopt it only if it has no Mathlib dependency
    and supports every toolchain in the range.
- **Golden files** are stored next to their tests. Updating them requires
  `UPDATE_GOLDEN=1` and shows up as a reviewable diff.
- **`scripts/test-all.sh`** runs every layer that CI runs, so a contributor
  can reproduce CI locally with a single command.

### 2.5 Continuous integration (GitHub Actions)

| Job | Matrix | Contents |
|---|---|---|
| `splice` | one toolchain | build with warnings as errors; unit, property and golden tests |
| `extract` | v4.28.0-rc1, v4.31.0, v4.34.1 (the three motivating projects), plus the latest stable | build the fixtures; unit, golden and trust tests |
| `cross-toolchain` | needs `extract` | compare bundles and `stmtHash` values across the matrix |
| `e2e` | one toolchain, with TeX Live (`pdflatex` and `lualatex`) | `scripts/e2e.sh` on `examples/` in all three modes |
| `lint` | — | markdown links, JSON schema validation of golden bundles, the traceability matrix has no orphan entries |

**Not in CI:** Mathlib-based integration. A Mathlib cache costs about 5 GB
per toolchain, and private repositories on the free plan get 2,000 Actions
minutes a month. `scripts/integration.sh` runs it locally against the real
projects. It is required before every release, and its report is attached to
the release.

**Branch rules:** `main` is protected; every change arrives as a pull
request with green CI; releases are tags following semantic versioning, with
`CHANGELOG.md` entries.

## 3. Spikes (do first, keep short, throw the code away)

Each spike ends with a short written result in `docs/spikes/`, and if
needed a change to DESIGN.md.

| # | Question | Done when | If it fails |
|---|---|---|---|
| S1 | **External mode.** Can a prebuilt extractor combine its own `.olean` files with a host's `lake env` search path, elaborate a notation file in-process with the frontend, and then import the host modules at `private` level? This must work on v4.28.0-rc1, v4.31.0 and v4.34.1 | a 100-line program does all of this against PLanet's project on all three toolchains | sidecar mode becomes the default; D§6.3 is updated |
| S2 | **Stable hashing.** Does a canonical serialisation of `Expr`, with binder names dropped and universe parameters renamed, give the same hash for the same declaration on all three toolchains, and do the dependency-cone walk and `collectAxioms` behave the same way? | the same hashes for the `Trust` fixture on three toolchains | the hash is defined per toolchain, and `check` reports "toolchain changed, run `accept`" instead of drift |
| S3 | **Parity baseline.** How much of llmbda's current output can a generic `rules` view reproduce? | a list of llmbda's rendering special cases, each marked as generic, notation, convention or custom view | the scope of the custom views for M5 is planned from this list |

S1 and S2 run in the first week, since external mode and hashing shape
milestones M2 and M3.

**Results.**
- S3 (2026-10-17) classified llmbda's 254 rendering special cases: about
  half were notation, a fifth custom views, and the rest generic or
  conventions. Its report, which quotes llmbda's code, is kept in llmbda.
  It set M5's scope: binder patterns, `latex_style`, `latex_entry`, label
  styles, alias templates and labels, and comment-delimited blocks.
- S1 succeeded on all three projects:
  [docs/spikes/S1-external-mode.md](docs/spikes/S1-external-mode.md).
- S2 succeeded once definitions are hashed by their equation lemmas, not their
  bodies: [docs/spikes/S2-stable-hashing.md](docs/spikes/S2-stable-hashing.md).
- DESIGN.md revision 3 takes in both results. S3 is still to do, before M5 is
  planned.

## 4. Milestones

Each milestone ends with green CI, an updated traceability matrix, and a
tag. "Tests first" means the listed tests are merged, failing, before the
code that makes them pass.

### M0 — Foundations (no release)

*Status: done on branch `m0-foundations` (2026-10-17), apart from green CI on
GitHub, which needs the branch pushed. §7's decisions were taken at their
defaults:*
- *our own generator, not Plausible;*
- *the toolchains v4.28.0-rc1, v4.31.0 and v4.34.1, plus v4.35.0, the latest
  stable;*
- *the repository stays private until v0.5.0.*

- Repository layout as in D§15: two Lake packages, `test/` and `scripts/`,
  Apache headers, `CONTRIBUTING.md`, templates for pull requests and issues.
- Build settings: `autoImplicit false`, all linters on, warnings as errors.
- The test harness and generator (§2.4), and golden-file support.
- The CI skeleton with all jobs; jobs that have nothing to test yet pass
  trivially.
- `docs/TESTING.md` with an empty traceability matrix listing every D§
  section.
- Spikes S1 and S2.

### M1 — The splicer (v0.1.0-alpha)

The splicer is pure text with no Lean internals, so it can be built
completely, test-first, before the extractor exists. Its input is
hand-written golden bundles.

- **Tests first:** every property in §2.3 except hash invariance; the TeX
  fixtures of §2.2; golden `check` reports for each failure mode.
- **Code:**
  - the TeX scanner, following `\input`, `\include` and `\subfile`, and
    skipping comments and `verbatim`;
  - block, inline and reference forms;
  - aliases;
  - slots, in both forms;
  - checksums with normalisation;
  - `scan`, `apply`, `check` (with `--diff`), `strip`, `migrate-slots`;
  - bundle reading, validated against `schema/bundle.schema.json`;
  - `imprimatur.toml`.
- **Done when:** all property tests pass with 10,000 generated cases per
  property, and llmbda's current `paper.tex` goes through `scan` and `strip`
  without changing a byte outside its blocks.

### M2 — The extractor, first views (v0.1.0)

- **Tests first:** golden bundles for `Basic`, covering the `lean` and
  `meta` views; trust fixtures for direct `sorry` and custom axioms; the
  `ModuleSys` fixture; the cross-toolchain job.
- **Code:**
  - environment loading through `Compat/`, at `private` level;
  - the `lean` view, with semantic macros, through the delaborator and
    `open_scoped`;
  - the `meta` view;
  - `collectAxioms` and `sorry` detection;
  - writing the bundle;
  - `imprimatur-export`, and the `imprimatur` wrapper in sidecar and
    in-project modes;
  - profiles, with `relative` as the default;
  - `imprimatur.sty`, with the token macros.
- **Done when:** the `e2e` job builds `examples/minimal` into a PDF in both
  modes. Also, `scripts/integration.sh` runs the `lean` view over PLanet's
  `Planet.Paper.*` and over the theorem in the math repository's
  `Separation.lean`, with outputs reviewed by hand.

### M3 — Trust and manifests (v0.2.0)

- **Tests first:** the whole `Trust` fixture, including `Weak`/`Strong` drift
  and `sorry` three levels down; hash-invariance properties; the
  `Manifests` fixture; `\leancheck` and `accept` round trips.
- **Code:**
  - the dependency cone with `trusted_prefixes`;
  - `stmtHash` and `sigHash`;
  - `\leancheck` and `accept`;
  - comparator and blueprint manifests, and `@challenge` entries;
  - external mode, if spike S1 succeeded.
- **Done when:**
  - `check` gives the right verdict on every `Trust` case on every
    toolchain;
  - the math repository's comparator manifests import cleanly in the
    integration run;
  - a deliberately weakened copy of a PLanet theorem is caught as drift.

### M4 — Notation and typeset maths (v0.3.0)

- **Tests first:** the `Notation` fixture with golden output for every
  feature of a notation rule; unit tests of the `Doc` emitter (precedence
  tables, widths, line breaks, flattening, escaping of every TeX special
  character).
- **Code:**
  - the `Doc` IR and emitter;
  - the `latex_notation` command and its environment extension;
  - pattern matching on `Expr` with the delaborator fallback;
  - `variant`, `flatten`, `width`, `hide`, `prec`;
  - the `math` and `prose` views;
  - notation packs (`core`, `logic`, `sets`, `order`), each tested against
    the fixtures.
- **Done when:** the partition-principle theorem renders in the `prose` view
  to the agreed target text (D§3; reviewed by hand in the integration run),
  and every pack rule has at least one golden use.

### M5 — Rules, grammars, and the llmbda migration (v0.4.0)

*Status: done on branch `m5-rules` (2026-10-18). The parity gate passes
byte for byte. llmbda's notation module and custom views live in llmbda
(`imprimatur/`, on llmbda's `imprimatur` branch), whose three documents are
now built with imprimatur in external mode; llmbda's old exporter, and the
gate with it, are deleted there. PLanet's rules
are generated (`integration/planet-rules`), with Lift hand-written. `show=`
and `hide=` are not implemented, and `migrate-slots` was not needed.*

- **Tests first:** `Semantics` fixture golden files for `rules` and
  `grammar`; premise conventions; `include` and `exclude`; label precedence;
  slots in grammars; the **parity harness**.
- **Code:**
  - the `rules` and `grammar` views;
  - `latex_metavar_convention` and `latex_hide_premise`;
  - theorem modifiers (`rule`, `def`, `forall`, `names`);
  - custom views through `@[latex_view]`.
- **Migration:** llmbda's notation module and custom views, built from spike
  S3's list.
- **Parity gate:** a script in llmbda builds `oopsla2027/paper.tex`
  with the old `run_latex` and with imprimatur from the same commit. It
  passes only if every difference is a `sum=` addition. Only then is the old
  code deleted from llmbda.
- **Done when:** the parity gate passes, and PLanet's rule figure is
  generated, with Lift still hand-written.

### M6 — Index, lint, anonymity, release (v0.5.0)

- **Tests first:** a golden `\leanindex` output; lint fixtures; anonymity
  fixtures (an absolute path, a user name or a URL planted in each output
  channel must be caught).
- **Code:** `\leanindex`, `lint`, `check --anonymous`, undefined-macro
  warnings, `--blueprint-compat`, release binaries for Linux, macOS and
  Windows, the toolchain range documented and enforced.
- **Done when:** PLanet builds with the `submission` profile and passes both
  `check --anonymous` and its own `check-anonymity.sh`. A release candidate
  is used for a week on a real paper before v0.5.0 is tagged.

## 5. Definition of done (every pull request)

- **Tests:** they come first, or alongside the code with the reason stated
  in the pull request. Every new error or warning has a test that triggers
  it.
- **Traceability:** the matrix in `docs/TESTING.md` is updated, and DESIGN.md
  is updated if behaviour differs from it.
- **Golden files:** changes are reviewed line by line in the pull request,
  with no blind `UPDATE_GOLDEN`.
- **CI:** green on every toolchain in the matrix.
- **Changelog:** a `CHANGELOG.md` entry for anything a user would notice.

## 6. Risks

| Risk | Likelihood | Mitigation |
|---|---|---|
| External mode is impossible on some toolchains | medium | spike S1 first; sidecar mode is a complete fallback |
| Lean internals change between toolchains (delaborator, `importModules`, frontend) | high, over time | everything version-specific lives in `Compat/`; CI covers the matrix; tags per toolchain if needed (D§13) |
| Golden files get approved without being read | medium | the definition of done; golden diffs kept small by giving each fixture one concern |
| llmbda parity takes longer than planned because of its special cases | medium | spike S3 measures it before M5 is planned |
| Mathlib integration is too heavy for CI and this machine (35 GB free disk) | high | Mathlib stays out of CI; integration runs locally, one toolchain at a time, reusing each project's existing `.lake` |
| The private repository runs out of Actions minutes | low to medium | the extractor matrix runs on pull requests, and the full matrix nightly; or make the repository public before v0.5 |

## 7. Decisions needed before M0

1. **When to make the repository public.** This affects CI minutes and
   whether others can contribute. The suggestion is at v0.5.0.
2. **Test-only dependencies.** Is Plausible acceptable in the test package
   (§2.4), or do we write our own small generator? Our own generator is the
   default.
3. **Supported toolchains for v0.1.** The suggestion is exactly the three
   used by the motivating projects, plus the latest stable release.
