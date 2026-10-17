# Contributing to imprimatur

*For people changing imprimatur's code. [DESIGN.md](DESIGN.md) says what to
build, [PLAN.md](PLAN.md) the order and how each part is tested, and
[docs/TESTING.md](docs/TESTING.md) how to run the tests.*

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
of done is PLAN §5:

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
  `String.mk` is deprecated in v4.35 and `String.ofList` doesn't exist in
  v4.28, so `testkit` builds strings with `String.push`.

## Branches and releases

`main` is protected. Every change arrives as a pull request with green CI.
Releases are tags following semantic versioning, each with a `CHANGELOG.md`
entry.
