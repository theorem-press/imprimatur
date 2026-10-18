# Testing imprimatur

*For contributors. [PLAN.md](../PLAN.md) §2 describes the test layers; this
file says how to run them and keeps the traceability matrix.*

## Running the tests

| What | Command | Where |
|---|---|---|
| everything CI runs | `scripts/test-all.sh` | repository root |
| integration with the real projects (not in CI) | `scripts/integration.sh` | repository root |
| the test harness's own tests | `lake test` | `testkit/` |
| extractor tests (build the fixtures first) | `lake test` | `extract/test/` |
| end-to-end examples (needs TeX Live) | `scripts/e2e.sh` | repository root |
| splicer tests | `lake test` | `splice/test/` |
| the extractor on another toolchain | `scripts/test-all.sh --toolchain v4.31.0` | repository root |
| lint (links, schema, this matrix) | `scripts/lint.sh` | repository root |

Each test package is a separate Lake package that requires the package it
tests and `testkit/`. The shipped packages therefore never depend on test
code (PLAN §1.6). A test package has no `lean-toolchain` of its own; `elan`
finds the one in the package it tests.

**Environment variables.**

- `UPDATE_GOLDEN=1` rewrites golden files instead of comparing them. Review
  the resulting diff line by line before committing it (PLAN §5).
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
`lint/…` (in `scripts/`), `integration/…` (in `scripts/integration.sh`) or
`e2e/…` (in `scripts/e2e.sh`).

**Golden bundles of the extractor.** `extract/test/golden/<fixture>.bundle.json`
holds the bundle of each fixture under `test/fixtures/`, with the toolchain in
`producer.lean` masked as `v4.x`. The same golden files must hold on every
toolchain in the CI matrix.

**Golden tests of the splicer.** Each directory under `test/tex/` is a case:
a document, its configuration and bundles, and a `steps` file of commands.
The test runs the steps and compares a transcript with
`splice/test/golden/<case>.txt` (see `splice/test/SpliceTest/Golden.lean`).

## Traceability matrix

Lean has no coverage tool, so this matrix stands in for coverage (PLAN §1.1).
There is one row per requirement, and every numbered section of
[DESIGN.md](../DESIGN.md) has at least one row. **Tests** lists test names,
or `—` if there are none yet. **When** is the milestone that brings the tests
(PLAN §4), or `n/a` for sections that describe no behaviour.

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
| D§4 | (4) every declaration has a default rendering (the `lean` view) | `extract/golden/Basic`, `integration/projb-lean-view`, `integration/math-lean-view` | M2 |
| D§4 | (5) external mode changes nothing in the host project | `e2e/external` | M3 |
| D§4 | (6) shipped packages have no Lake dependencies | `lint/no-deps` | M0 (lint) |
| D§4 | (7) environments are imported at `private` level | `extract/modules/private-sorry-seen`, `extract/modules/sorry-through-import-all`, `extract/golden/ModuleSys` | M2 |
| D§5 | extractor and splicer communicate only through the bundle | `splice/version/schema`, `extract/version/schema` | M1 |
| D§5 | `imprimatur build` runs scan, export, apply; `check` passes after it | `e2e/minimal`, `e2e/sidecar` | M2 |
| D§6.1 | `imprimatur.toml` is parsed; unknown keys and bad values are reported | `splice/toml/parses`, `splice/toml/duplicate-key`, `splice/toml/error-line`, `splice/config/parses`, `splice/config/unknown-key`, `splice/config/alias-needs-view`, `splice/config/url-needs-template`, `splice/golden/config-errors` | M1 |
| D§6.2 | the notation module is elaborated and its names resolved, in-project and as a file in external mode | `extract/golden/Notation`, `e2e/minimal`, `e2e/external` | M4 |
| D§6.3 | sidecar and in-project modes | `e2e/minimal`, `e2e/sidecar` | M2 |
| D§6.3 | external mode, with `imprimatur toolchain install` | `e2e/external`, `integration/math-manifests`, `integration/projb-drift` | M3 |
| D§7.1 | `Doc` emitter: escaping, parenthesisation, line breaking | `extract/doc/escape-specials`, `extract/doc/width-symbols`, `extract/doc/width-wrappers`, `extract/doc/width-spacing`, `extract/doc/width-scripts`, `extract/doc/width-given`, `extract/doc/no-parens-left-assoc`, `extract/doc/parens-right`, `extract/doc/parens-tighter`, `extract/doc/no-parens-looser`, `extract/doc/width-counts-parens`, `extract/doc/fits-unbroken`, `extract/doc/breaks-outermost`, `extract/doc/breaks-deeper-when-needed` | M4 |
| D§7.2 | notation matches `Expr`; unmatched subterms are rendered as functions, or delaborated | `extract/golden/Notation`, `extract/notation/no-render-errors` | M4 |
| D§7.3 | `lean` view, with semantic token macros | `extract/tokens/line`, `extract/tokens/subscripts-and-primes`, `extract/names/strip`, `extract/golden/Basic`, `integration/projb-lean-view` | M2 |
| D§7.3 | `meta` view; the splicer fills its source location per profile | `extract/markdown/code`, `extract/markdown/maths`, `extract/markdown/unbalanced-maths`, `extract/golden/Basic`, `splice/golden/meta-source` | M2 |
| D§7.3 | `math` and `prose` views | `extract/golden/Notation`, `e2e/minimal`, `e2e/fixture-views`, `integration/math-prose` | M4 |
| D§7.3 | `rules` and `grammar` views | `extract/golden/Semantics`, `e2e/fixture-views`, `integration/projb-rules`, project-a's parity gate | M5 |
| D§7.3 | custom views through `@[latex_view]`, with the document inventory | `extract/golden/Semantics` (`fixture.rulelist`), project-a's parity gate (four custom views) | M5 |
| D§7.4 | rule label precedence; `latex_rules` templates, anchors, `sep`, `doc_labels`; groups across inductives | `extract/golden/Semantics`, project-a's parity gate | M5 |
| D§7.5 | notation rules: patterns, templates, `prec`, `width`, `hide`, `variant`, `flatten`, typed patterns, lookup order, metavariables | `extract/golden/Notation`, `extract/doc/template-prime`, `extract/doc/template-longest`, `extract/doc/template-unknown`, `extract/doc/metavar-subscript`, `extract/doc/metavar-digits`, `extract/doc/metavar-prime`, `extract/doc/metavar-long`, `extract/doc/metavar-renamed`, `splice/golden/notation-config` | M4 |
| D§7.5 | packs: every rule has a golden use, and the output typesets with both engines | `extract/notation/every-pack-rule-used`, `e2e/fixture-views` | M4 |
| D§7.5 | the bundle records the macros each rendering uses | `extract/golden/Notation` | M4 |
| D§7.5 | binder patterns, partial applications, `flatten` with `sep`, `assoc`, `latex_style`, `latex_entry`, Greek letters, several notation files | `extract/golden/Notation` (`math:binders`), `extract/golden/Semantics`, project-a's parity gate | M5 |
| D§7.6 | premise conventions | `extract/golden/Semantics`, `e2e/fixture-views` | M5 |
| D§7.7 | axioms and `sorry` | `extract/trust/direct-sorry`, `extract/trust/custom-axiom`, `extract/trust/classical-axioms`, `extract/trust/sorry-in-proof-chain`, `extract/trust/sorry-in-statement`, `extract/trust/custom-axiom-trust`, `extract/modules/private-sorry-seen` | M2 |
| D§7.7 | dependency cone up to `trusted_prefixes`, with reasons | `extract/trust/cone-sorry`, `extract/trust/cone-partial`, `extract/trust/cone-clean`, `splice/golden/cone` | M3 |
| D§7.7 | `stmtHash`: insensitive to binder and universe names, sensitive to meaning, stable across toolchains | `extract/prop/hash-binder-names`, `extract/prop/hash-universe-names`, `extract/prop/hash-sees-constants`, `extract/prop/hash-ignores-mdata`, `extract/hash/sorry-tag-ignored`, `extract/hash/binder-kind-matters`, `extract/trust/same-hash-renamed-binder`, `extract/trust/same-hash-renamed-universes`, `extract/trust/weakened-hypothesis-drifts`, `extract/golden/Trust` | M3 |
| D§7.7 | `sigHash` change alone is a warning | `extract/trust/weakened-hypothesis-same-signature`, `extract/trust/different-sig-renamed`, `splice/golden/drift` | M3 |
| D§8 | bundles are deterministic: sorted keys, no timestamps; the same on every toolchain | `extract/json/sorted`, `extract/golden/Basic`, `extract/golden/ModuleSys`, `extract/golden/Trust` | M2 |
| D§8 | bundles contain no absolute paths, user names, URLs or commit hashes | `extract/golden/Basic`, `splice/bundle/absolute-path` | M2 |
| D§8 | bundles are read and checked against the rules of `schema/bundle.schema.json`; golden bundles validate against the schema | `splice/bundle/parses`, `splice/bundle/schema-version`, `splice/bundle/absolute-path`, `splice/bundle/missing-views`, `splice/golden/bundle-errors`, `lint/bundle-schema` | M1 |
| D§8 | a view that fails to render is recorded in `errors`, and is an error only if requested | `extract/golden/Basic`, `splice/golden/failures` | M2 |
| D§9.1 | `leanblock`, `\leaninline`, `\leanref`, `\leancheck`, `\leanindex` are recognised | `splice/scan/forms`, `splice/scan/options`, `splice/scan/check-keys`, `splice/golden/basic` | M1 |
| D§9.1 | block options: `include`/`exclude` and the theorem modifiers (`show`/`hide` are not implemented) | `extract/golden/Semantics`, `splice/golden/basic` | M5 |
| D§9.2 | alias options `label`, `repeat_suffix`, `template`, `comment` | `splice/golden/aliases`, project-a's parity gate | M5 |
| D§10.1 | conditionals: blocks in branches that are off (`\iffalse`, `\newif` switches) are maintained but not typeset; the document inventory | `splice/golden/conditionals`, `splice/golden/aliases`, project-a's parity gate | M5 |
| D§9.2 | aliases map existing environments onto `leanblock` | `splice/config/alias-slots`, `splice/golden/basic`, `splice/golden/positional-slots` | M1 |
| D§9.3 | blueprint `\lean{…}` read as check-only references; `\leanok` cross-checked | `splice/golden/blueprint` | M3 |
| D§9.3 | `--blueprint-compat` writes `\lean{…}` | — | M6 |
| D§9.4 | a document compiles with `imprimatur.sty` (pdflatex and lualatex) and shows the spliced content | `e2e/minimal`, `e2e/sidecar` | M2 |
| D§9.5 | slots keep their text by id; slot edits are not hand edits | `splice/slots/merge`, `splice/checksum/ignores-slot-text`, `splice/prop/slot-preservation`, `splice/prop/edit-detection`, `splice/golden/slots`, `splice/golden/unicode` | M1 |
| D§9.5 | orphaned slots are dropped with their text printed; `--rename-slot` | `splice/slots/orphans`, `splice/slots/rename`, `splice/golden/slots` | M1 |
| D§9.5 | slots declared by position; `migrate-slots` | `splice/slots/found`, `splice/slots/outer`, `splice/golden/positional-slots`, `splice/golden/migrate-slots` | M1 |
| D§10.1 | `scan` follows `\input`, `\include`, `\subfile`, skips comments, `\verb` and `verbatim`; malformed markup is an error with a position | `splice/scan/inputs`, `splice/scan/comment-skipped`, `splice/scan/verb-skipped`, `splice/scan/verbatim-skipped`, `splice/scan/unclosed-block`, `splice/prop/scanner-robustness`, `splice/prop/scanner-truncated`, `splice/golden/basic`, `splice/golden/comments-verbatim`, `splice/golden/macro-args`, `splice/golden/parse-errors`, `splice/golden/outside` | M1 |
| D§10.2 | `apply` is idempotent, changes nothing outside regions and `sum=`, and touches only changed files | `splice/prop/idempotence`, `splice/prop/locality`, `splice/prop/fixed-point`, `splice/golden/basic` | M1 |
| D§10.2 | checksums normalise line endings and trailing whitespace | `splice/prop/normalisation`, `splice/normalize/crlf-and-trailing`, `splice/golden/crlf` | M1 |
| D§10.2 | hand edits are refused without `--force`; nothing is written when there is an error | `splice/prop/edit-detection`, `splice/golden/hand-edit` | M1 |
| D§10.2 | missing keys are errors; `--keep-stale` | `splice/golden/failures` | M1 |
| D§10.2 | writes keep line endings and encoding | `splice/golden/crlf`, `splice/golden/unicode` | M1 |
| D§10.3 | `check` reports stale blocks, with `--diff` | `splice/diff/lines`, `splice/golden/slots`, `splice/golden/positional-slots` | M1 |
| D§10.3 | `check` reports broken references | `splice/golden/failures` | M1 |
| D§10.3 | `check` reports untrusted results (splicer side; the extractor fills in the data in M2) | `splice/golden/failures` | M1 |
| D§10.3 | `check` reports drift; `accept` records the new hash | `splice/golden/drift`, `integration/projb-drift` | M3 |
| D§10.3 | `check` warns of undefined macros and orphaned slots | — | M6 |
| D§10.3 | `check` exit codes: non-zero on anything but warnings | `splice/golden/failures`, `splice/golden/config-errors`, `splice/golden/slots` | M1 |
| D§10.4 | `strip` removes markers and keeps generated content | `splice/slots/unwrap`, `splice/prop/strip`, `splice/golden/strip` | M1 |
| D§10.5 | comparator manifests, including `@challenge` entries | `splice/golden/manifests`, `extract/manifests/challenge-keys`, `extract/manifests/challenge-statement-matches`, `extract/manifests/unknown-challenge`, `extract/golden/Manifests` | M3 |
| D§11 | profiles `relative` (default), `url`, `none` for `\leanref` and the `meta` view | `splice/tex-escape`, `splice/config/url-needs-template`, `splice/golden/refs`, `splice/golden/meta-source` | M1 |
| D§11 | `check --anonymous` | — | M6 |
| D§12 | every command in the table exists and prints usage | — | M6 |
| D§13 | the supported toolchain range is documented and enforced | — | M6 |
| D§13 | the same fixture gives the same bundle on every toolchain, apart from `producer` | `extract/golden/Basic`, `extract/golden/ModuleSys`, `extract/golden/Trust` | M2 |
| D§13 | the same declaration has the same `stmtHash` on every toolchain | `extract/golden/Trust`, `extract/golden/Basic`, `extract/golden/Manifests` | M3 |
| D§13 | the splicer accepts the current and previous bundle schema | `splice/version/schema`, `splice/bundle/schema-version` | M1 |
| D§14 | testing (this file) | — | n/a |
| D§15 | repository layout | — | n/a |
| D§16 | project-a's `paper.tex` goes through `scan` and `strip` with every byte outside its blocks kept | `integration/project-a-scan-strip` | M1 |
| D§16 | project-a parity gate | `imprimatur/parity.sh` in project-a, passed for each of its three documents, then retired with the old exporter (project-a commit `0114fd4`) | M5 |
| D§16 | project B rules figure | `integration/projb-rules` | M5 |
| D§16 | project B `check --anonymous` | — | M6 |
| D§16 | math catalogue comparator manifests import cleanly | `integration/math-manifests` | M3 |
| D§17 | roadmap | — | n/a |
| D§18 | open questions | — | n/a |
| D§A | claims still to check | — | n/a |

The test harness has its own checks (`testkit/harness/counts`,
`testkit/gen/splitmix-pinned` and so on), which aren't listed here because
they test the tests.
