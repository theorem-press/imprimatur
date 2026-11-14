# A small calculus, generated from Lean

A short paper on a simply typed λ-calculus with names, in external mode: the
Lean project in `host/` is read as it is, and the notation is a file outside
it.

- [paper.tex](paper.tex): the paper as its author writes it, with empty
  blocks. [expected/paper.tex](expected/paper.tex) is the result of
  `imprimatur build`.
- [host/Stlc/Lang.lean](host/Stlc/Lang.lean): terms, types, typing and
  reduction, with swapping and α-equivalence after Pitts;
  [host/Stlc/Safety.lean](host/Stlc/Safety.lean): substitution, preservation
  and progress, proved; [host/Stlc/Examples.lean](host/Stlc/Examples.lean):
  the paper's examples, theorems about particular terms over four fixed
  names, two or three for each section.
- [notation/StlcTeX.lean](notation/StlcTeX.lean): how the paper writes each
  Lean constant (`latex_notation`), its metavariables (`latex_category`),
  and the titles it uses as keys (`latex_entry`).
- [imprimatur.toml](imprimatur.toml): the configuration, including the
  paper's own environments (`leangrammar`, `leanrules`, `leantheorem`).

The paper shows each kind of generated block: a grammar whose descriptions
are the authors' (slots), inference rules, definitions by their equations,
theorems and examples as sentences, and hand-written statements checked
against Lean with `\leancheck`. It ends with a generated index of its
notation. The examples' names are set in typewriter ($\mathtt{x}$) to tell
them from the metavariables ($x$): written alike, reading back finds every
rule that mentions $x$ ambiguous, and `imprimatur check` says so.

To build it, see [the examples](../README.md).
