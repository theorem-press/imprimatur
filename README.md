# imprimatur

*Imprimatur* ("let it be printed") keeps the LaTeX of a paper in step with a
Lean 4 development.

- **Generated content.** Authors mark places in ordinary `.tex` files where a
  Lean declaration should appear: a theorem statement, a definition, a set of
  inference rules or a grammar. imprimatur renders that content from the
  compiled Lean environment, in the paper's own notation, and splices it in
  place.
- **Checked prose.** Hand-written theorem prose can be tied to the Lean
  results it describes. The build then fails if a result disappears, depends
  on `sorry` or a disallowed axiom, or changes its statement after an author
  last checked the prose against it.
- **Faithful notation.** Every formula imprimatur typesets is read back, in
  the grammar of the paper's notation, and must mean the Lean statement it
  came from: one reading, and the right one.

The `.tex` files stay ordinary LaTeX, so they compile on Overleaf and arXiv
with no preprocessor. The host Lean project doesn't need to change.

## What it looks like

In Lean, from [examples/semantics](examples/semantics/README.md):

```lean
theorem preservation {e e' : Tm} (hs : Step e e') :
    ∀ {Γ : Ctx} {t : Ty}, HasType Γ e t → HasType Γ e' t
```

In the paper, the author writes an empty block that names the theorem:

```latex
\begin{leantheorem}{Stlc.preservation}{Preservation}
\end{leantheorem}
```

The first argument is the **key**, the Lean name of the declaration to show;
the second is the theorem's title. `leantheorem` is an environment the
paper's `imprimatur.toml` declares, as a sentence (the `prose` view) wrapped
in `theorem`:

```toml
[aliases]
leantheorem = { view = "prose", wrap = "theorem", label = "thm:{key}" }
```

`imprimatur build` looks up `Stlc.preservation`, renders it with the
notation the paper declares for `Step`, `HasType` and the rest, and fills in
the block:

```latex
\begin{leantheorem}[sum=jU5x8J0Hfl]{Stlc.preservation}{Preservation}
\label{thm:Stlc.preservation}
\LeanProse{Let $e, e' \in \mathit{Term}$, $\Gamma \in \mathit{Context}$ and
$\tau \in \mathit{Type}$. Assume $e \longrightarrow e'$ and
$\Gamma \vdash e : \tau$. Then $\Gamma \vdash e' : \tau$.}
\end{leantheorem}
```

which typesets as a theorem: *Let e, e′ ∈ Term, Γ ∈ Context and τ ∈ Type.
Assume e ⟶ e′ and Γ ⊢ e : τ. Then Γ ⊢ e′ : τ.* The `sum=` checksum records
what was generated. If the Lean theorem changes, `imprimatur check` reports
the block as stale; if someone edits it by hand, as edited; if the theorem
comes to depend on `sorry`, as untrusted.

A key can also be a title the paper uses, mapped to the Lean name in the
notation module (`latex_entry "Preservation" => Stlc.preservation`), as
[examples/semantics](examples/semantics/paper.tex) does.

### What the block rests on

Between the Lean development and the paper there is one file, the *bundle*,
which `imprimatur build` writes and the splicer reads. Its entry for the
theorem above is, abridged:

```json
"Stlc.preservation": {
  "kind": "theorem",
  "stmtHash": "a89b1dbd…",
  "sigHash":  "dd711a64…",
  "views": { "prose": "\\LeanProse{Let $e, e' \\in \\mathit{Term}$ …}", "math": "…" },
  "sorry": false, "axioms": [], "cone": { "size": 16, "untrusted": [] }
}
```

It says nothing about the *proof* of preservation, and cannot: the splicer
never sees Lean. It carries two images of the *statement*, a hash that
names its meaning and TeX that shows it, and a verdict on the proof. That
is the whole interface, and it is a Lean type, `Bundle (Image TeX) Verdict`
in [bundle/Bundle.lean](bundle/Bundle.lean), of which the file is the JSON.

The type comes with its meaning. A bundle is *true* of a development when
every claim it makes holds of the statement it is about: the hash is that
statement's, each view is that statement rendered, and a view with no
recorded problems reads back as it. A bundle may say less than Lean knows,
a view it could not render, a hash it could not compute, never something
false; where it is silent, `check` reports the silence.

That is enough for one theorem, proved in Lean for a model of the splicer
([about/](about/)):

> **If `imprimatur check` reports nothing, and the bundle is true, then the
> paper is true:** every displayed formula is a statement Lean proved,
> rendered by the paper's notation, and reads back as that statement; and
> every `\leancheck` names, by its hash, a statement Lean proved.

The theorem's hypothesis is the trust boundary, stated once: the extractor
is honest about the development, and SHA-256 does not collide. Everything
after that, generation, hand edits, staleness, slot text, drift, is covered
by the proof.

## What it does

- **Views:** a declaration as Lean prints it (`lean`), as a formula
  (`math`, or its defining equations with `def`), as a sentence (`prose`),
  as inference rules (`rules`), as a BNF grammar (`grammar`), or its source,
  axioms and `sorry` status (`meta`). Indexes of the paper's metavariables,
  its notation and its results are views too. See
  [docs/views.md](docs/views.md).
- **Notation** is declared in Lean, with `latex_notation`, `latex_category`
  and `latex_style`, and shared packs for logic, sets and order. See
  [docs/notation.md](docs/notation.md).
- **Trust checks:** results that disappear, depend on `sorry` or a
  disallowed axiom, or whose statement changed since `\leancheck` recorded
  it. Comparator manifests and leanblueprint's `\lean{…}` are read too. See
  [docs/trust.md](docs/trust.md).
- **Translation validation:** each formula is parsed back in the notation's
  grammar, and one that is ambiguous, cannot be read back, or reads as
  something other than its statement is reported where it is. The parser is
  proved sound and complete, so a formula that passes has no reading in the
  grammar but its statement's (docs/verified-validator.md). With
  `latex_style categories := strict`, a variable is always written with its
  type's letter, so a reader can tell its type.
- **Three modes:** inside the Lean project, as a sidecar package, or
  external, which leaves the host project untouched. See
  [docs/blocks.md](docs/blocks.md).

## Getting started

You need [elan](https://github.com/leanprover/elan), a TeX distribution with
`latexmk`, and a built Lean project.

```sh
git clone https://github.com/theorem-press/imprimatur.git
cd imprimatur/splice && lake build
export PATH="$PWD/.lake/build/bin:$PATH"
```

Then, in a paper's directory with an `imprimatur.toml`
([docs/blocks.md](docs/blocks.md) explains it):

```sh
imprimatur toolchain install v4.31.0   # external mode: once per Lean version
imprimatur build                       # render and splice the blocks
imprimatur check                       # what is stale, untrusted or unfaithful
latexmk -pdf paper.tex
```

[examples/](examples/README.md) has four working papers: one for each mode, and a
longer one on a λ-calculus.

## Status

Usable now from source: build it from `main`, as in Getting started above.
It works on Lean v4.28.0-rc1 to v4.35.0, and builds the papers of two
programming-language projects, whose grammars, rules and results are
generated, and a paper about imprimatur itself ([about/](about/)), whose
theorems about the splicer, and about the extractor's layouts, are proved
in Lean.

There is no tagged release yet, so pin a commit if you depend on it. The
first release, v0.5.0, adds an index of every result a paper cites,
`check --anonymous` for double-blind submission, `init`, and release
binaries: see the
[v0.5.0 milestone](https://github.com/theorem-press/imprimatur/milestone/1).
Other planned work is in the
[issues](https://github.com/theorem-press/imprimatur/issues).

## More

- [DESIGN.md](DESIGN.md): the architecture (a Lean-side extractor and a
  text-only splicer, connected by a versioned JSON bundle), the notation
  language, the trust checks, prior art, and what correctness means (§18).
- [CHANGELOG.md](CHANGELOG.md): what has changed.
- [CONTRIBUTING.md](CONTRIBUTING.md) and [docs/TESTING.md](docs/TESTING.md):
  working on the code.

## License

Apache-2.0. See [LICENSE](LICENSE).
