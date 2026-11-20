# What the archive claims

A note of two pages that states the five theorems the Lean archive released by
Levent Alpöge on 2026-11-20 claims to prove, the Riemann Hypothesis and the
Generalized Riemann Hypothesis for Dirichlet L-functions, in the words of their
Lean statements ([paper.tex](paper.tex), the result in
[expected/paper.tex](expected/paper.tex)). It is imprimatur's first example
on a Mathlib host, and its first on statements whose proofs are not in the
development (#137).

The host, [host/](host/), is Mathlib plus one file,
[Riemann/Statements.lean](host/Riemann/Statements.lean), that states the five
theorems with Mathlib's definitions only and `sorry` for every proof: it says
what is claimed and proves nothing. The archive itself is not here. Lean's
Comparator checks that the archive proves exactly such statements;
imprimatur checks that the note says exactly what the statements say. Neither
reads the proofs.

What the note shows:

- a theorem whose statement is a named proposition, Mathlib's
  `RiemannHypothesis`, rendered with the definition unfolded (`[unfold]`);
- an instance binder, `[NeZero N]`, stated as a hypothesis because the
  notation module writes it;
- statements whose proofs are `sorry` on purpose, marked `[claim]`, so that
  `check` warns of the `sorry` instead of failing, and the provenance table
  says **sorry** on every row;
- an index of the notation, each entry with the Mathlib constant it stands
  for.

To build it, with imprimatur installed as in
[Try it in two minutes](../../README.md#try-it-in-two-minutes):

```sh
cd examples/riemann
(cd host && lake exe cache get && lake build)
imprimatur build
imprimatur check
latexmk -pdf paper.tex
```

The host pins Lean `v4.34.1` and the Mathlib commit the extractor was tried
on; the archive itself is on `v4.33.1` and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, where the five definitions are
the same. Loading Mathlib takes the extractor about 7 GB of memory. The
end-to-end tests skip this example unless `E2E_MATHLIB=1` is set
([steps](steps)), since Mathlib's cache is several gigabytes.
