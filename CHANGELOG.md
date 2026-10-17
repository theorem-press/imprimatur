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
