# Examples

Four small papers built with imprimatur. Each is a directory with a Lean
project, an `imprimatur.toml`, and a `paper.tex` whose blocks are empty until
`imprimatur build` fills them in. `expected/paper.tex` in each is the result,
as the end-to-end tests check it.

| Example | Mode | What it shows |
|---|---|---|
| [minimal](minimal/paper.tex) | in-project: the Lean project requires imprimatur ([result](minimal/expected/paper.tex)) | the smallest setup: declarations in each view (`lean`, `meta`, `math`, `prose`), with a one-rule notation module inside the project |
| [sidecar](sidecar/paper.tex) | sidecar: a separate Lake package beside the host reads it ([result](sidecar/expected/paper.tex)) | a theorem as Lean prints it, with its source, axioms and `sorry` status, without touching the host's lakefile |
| [external](external/paper.tex) | external: the host is read as it is, with a notation file outside it ([result](external/expected/paper.tex)) | a formula typeset from a notation file outside the host, which is read unchanged |
| [semantics](semantics/) | external | a short paper on a typed λ-calculus: a generated grammar and rules, theorems as sentences, hand-written prose checked with `\leancheck` |

To build one (see [Getting started](../README.md#getting-started) for
installing imprimatur):

```sh
cd examples/semantics
(cd host && lake build)                  # the Lean project, built by its owners
imprimatur toolchain install v4.35.0     # external mode: once per Lean version
imprimatur build                         # fill in the blocks
imprimatur check
latexmk -pdf paper.tex
```

The modes are explained in [docs/blocks.md](../docs/blocks.md).
