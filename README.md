# imprimatur

*Imprimatur* ("let it be printed") keeps the LaTeX of a paper in step with a
Lean 4 development.

- **Generated content.** Authors mark places in ordinary `.tex` files where a
  Lean declaration should appear: a theorem statement, a definition, a set of
  inference rules or a grammar. imprimatur renders that content from the
  compiled Lean environment and splices it in place.
- **Checked prose.** Hand-written theorem prose can be tied to the Lean
  results it describes. The build then fails if a result disappears, depends
  on `sorry` or a disallowed axiom, or changes its statement after an author
  last checked the prose against it.

The `.tex` files stay ordinary LaTeX, so they compile on Overleaf and arXiv
with no preprocessor. The host Lean project doesn't need to change.

## Status

Early development. The splicer, `imprimatur-splice`, works from
hand-written bundles; see [docs/blocks.md](docs/blocks.md). The extractor,
which produces bundles from Lean, comes next. [PLAN.md](PLAN.md) gives the build order, and
[CONTRIBUTING.md](CONTRIBUTING.md) explains how to work on the code. See
[DESIGN.md](DESIGN.md) for:

- the architecture: a Lean-side extractor and a text-only splicer, connected
  by a versioned JSON bundle;
- the notation language;
- the trust checks;
- a survey of prior art;
- the roadmap.

## License

Apache-2.0. See [LICENSE](LICENSE).
