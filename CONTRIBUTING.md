# Contributing to imprimatur

*For people changing imprimatur's code. [DESIGN.md](DESIGN.md) says what to
build, [docs/TESTING.md](docs/TESTING.md) how each part is tested, and the
[issues](https://github.com/theorem-press/imprimatur/issues) what is still to
do: labelled `functionality`, `paper` or `outreach`, with release scope in
milestones.*

## Principles

1. **Every requirement has a test, and every test names its requirement.**
   `docs/TESTING.md` keeps a traceability matrix from each design section
   (D§…) to the tests that cover it. Lean has no coverage tool, so this
   matrix stands in for coverage. A pull request that changes behaviour
   updates the matrix.
2. **Tackle the risks first.** An assumption the design rests on, which
   could fail, gets a short spike before code is built on it, with a written
   result in `docs/spikes/`. External mode (S1) and stable hashing (S2) were
   settled this way; S3, which classified project A's 254 rendering special
   cases and set M5's scope, keeps its report in project A.
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

## Layout

| Directory | What it is |
|---|---|
| `extract/` | Lake package `imprimatur`: the extractor and the `imprimatur-export` executable. Lean core only, no Lake dependencies |
| `splice/` | Lake package `imprimatur-splice`: the splicer. Text only, no Lean internals, no Lake dependencies |
| `testkit/` | test-only package: harness, golden files, seeded generator |
| `extract/test/`, `splice/test/` | test packages; each requires its parent and `testkit/` |
| `test/` | fixtures shared by the tests: Lean projects, TeX documents, bundles |
| `schema/` | the bundle's JSON schema |
| `scripts/` | `test-all.sh`, `lint.sh`, `e2e.sh` and the lint checks |
| `docs/` | documentation; `docs/spikes/` holds spike write-ups |

## Before you open a pull request

`scripts/test-all.sh` must pass; it runs every layer CI runs. The definition
of done:

- **Tests** come first, or with the code, with the reason stated in the pull
  request. Every new error or warning has a test that triggers it.
- **Traceability.** Update the matrix in `docs/TESTING.md`. If behaviour
  differs from DESIGN.md, update DESIGN.md too.
- **Golden files.** Review every changed line. Never commit the output of
  `UPDATE_GOLDEN=1` unread.
- **CI** is green on every toolchain in the matrix.
- **Changelog.** Add a `CHANGELOG.md` entry for anything a user would notice.

## Conventions

- Every source file starts with the Apache-2.0 header used in the existing
  files.
- `autoImplicit` is off and every linter is on. CI builds with
  `lake build --wfail`.
- Every public declaration has a docstring.
- Test names have the form `package/area/what` and are unique; the
  traceability matrix refers to them.
- Code that differs between Lean versions lives in `extract/Imprimatur/Compat/`
  and nowhere else (DESIGN §13).
- The extractor must build on every toolchain in the matrix. Avoid APIs that
  were added, renamed or deprecated inside that range. For example,
  `String.mk` and `String.trim` are deprecated from v4.28; use
  `String.ofList` and `String.trimAscii`. Check an API in each toolchain's
  sources (`~/.elan/toolchains/*/src/lean`) before relying on it.

## Branches and releases

`main` is protected. Every change arrives as a pull request with green CI.
Releases are tags following semantic versioning, each with a `CHANGELOG.md`
entry.
