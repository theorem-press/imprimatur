# About imprimatur

`imprimatur-paper.tex` is a short paper about imprimatur, built with
imprimatur. Its theorems are DESIGN §18.2's: the splicer's laws (locality,
idempotence, the fixed point, slot preservation) and Theorem 1, what a
successful `imprimatur check` guarantees. They are proved in `lean/`, a
model of the splicer in which a document is already parsed into pieces.

The model is built on the bundle's type, `bundle/Bundle.lean`, of which the
JSON that passes from the extractor to the splicer is the file; `lean/` holds
a copy of it, under the extractor's module name, which the lint keeps equal
to the source.

Every definition and theorem displayed in the paper is generated from
`lean/`; every hand-written claim about it carries a `\leancheck`. The
notation is in `notation/SpliceTeX.lean`, read in external mode.

It also states Theorem 2, that rendering is faithful, as what translation
validation checks for each formula (DESIGN §18.3–§18.4), and what is left
to the trusted base. The notation uses `latex_style categories := strict`,
and Appendix A, the metavariables and the notation, is generated.

To rebuild and check it:

```
(cd lean && lake build)
imprimatur toolchain install v4.35.0   # once
imprimatur build
imprimatur check                       # 0 stale, 0 errors, 0 warnings
latexmk -pdf imprimatur-paper.tex
```

CI does the same (`e2e/about` in `scripts/e2e.sh`), and fails if the
committed paper is not what `imprimatur build` makes, or if `check` reports
anything, including a formula that does not read back faithfully.
