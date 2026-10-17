# Changelog

All notable changes to imprimatur are recorded here. Versions follow
[semantic versioning](https://semver.org/).

## Unreleased

- Repository layout, build settings, test harness and CI skeleton (PLAN M0).
- `imprimatur-splice`, the splicer (PLAN M1): `scan`, `apply`, `check` (with
  `--diff`), `strip` and `migrate-slots`. It supports blocks, aliases,
  `\leaninline`, `\leanref`, `\leancheck`, slots in both forms, checksums
  that ignore line endings and trailing whitespace, multi-file documents, and
  `imprimatur.toml`. See [docs/blocks.md](docs/blocks.md).
- `imprimatur-export`, the extractor (PLAN M2). It renders the `lean` view
  (the signature, with semantic token macros) and the `meta` view (source
  location, axioms, `sorry` status, docstring). It imports at the `private`
  level, so a `sorry` hidden in a `module` file's private proof is found.
  Bundles are byte-identical across toolchains v4.28.0-rc1 to v4.35.0. See
  [docs/views.md](docs/views.md).
- `imprimatur build` and `imprimatur check` run the whole flow in in-project
  and sidecar modes. `tex/imprimatur.sty` typesets the result with pdfLaTeX
  or LuaLaTeX. `examples/minimal` and `examples/sidecar` show both modes.
