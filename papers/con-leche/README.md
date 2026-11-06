# con-leche's README, as a paper

An experiment: the README of [con-leche](https://github.com/leanprover/con-leche),
Lean's verified external checker, turned into a paper whose Lean statements
imprimatur generates. The prose is the README's at commit 7cb7a45
(2026-11-05), unchanged; its three Markdown code blocks (the main corollary,
the main theorem and the lifted corollary) are generated blocks, and a
generated block follows each mention of a declaration the README only links
to. Every block is the `lean` view: the signature as Lean prints it, from the
built development, in external mode, so con-leche's repository does not
change. `[trust] checker = "con-leche"` has con-leche check its own
development.

## Building

```sh
git clone https://github.com/leanprover/con-leche ../../../con-leche   # beside imprimatur
(cd ../../../con-leche && lake build ConLeche.MainTheorem ConLeche.Verify.Frontend.Prepare \
   ConLeche.Model.StreamConsts ConLeche.Frontend.Olean.View con-leche)   # about 10 minutes
imprimatur toolchain install v4.35.0
imprimatur build        # the extractor, about 20 s; con-leche's own check besides, the first time
imprimatur check
latexmk -pdf main.tex
```

## What the README names, and what the paper shows

| README | Key | Note |
|---|---|---|
| `sorryAx` | `sorryAx` | Lean's axiom (`Init/Prelude.lean`) |
| the main corollary (code block) | `ConLeche.no_False_declaration` | |
| the meaning of `False` | `ConLeche.falseBasis` | the pinned block the link points at |
| the main theorem (code block) | `ConLeche.model_exists` | |
| `Model V env` | `ConLeche.Model` | |
| `Denotes` | `ConLeche.Denotes` | |
| `checkDecls` | `ConLeche.Cached.checkDecls` | |
| `preparePrelude`, `preparePrelude_perm` | `ConLeche.Frontend.preparePrelude`, `…_perm` | |
| `checkDecls_consts` | `ConLeche.Cached.checkDecls_consts` | |
| `runArgs`, `CheckerIO`, `parMapExcept`, `liftIO` | `ConLeche.Driver.runArgs`, `ConLeche.CheckerIO`, `….parMapExcept`, `….liftIO` | |
| `ModelIO`, `checkDeclsIO` | `ConLeche.ModelIO`, `ConLeche.Driver.checkDeclsIO` | |
| the lifted corollary (code block) | `ConLeche.main_no_False` | |
| `main`, the linearity protection | `main`, `enableAbortOnNonlinear` | module `Main`, con-leche's executable |
| `[SetTheory V]` | `ConLeche.SetTheory` | |
| `carneiro_implies_conleche` | — | in `bridge/lean4lean-model`, a separate package on Mathlib; not imported |
| the `.olean` corollary (code block) | `ConLeche.main_oleans_no_False` | |
| `decodeModuleSpec` | `ConLeche.Frontend.Olean.decodeModuleSpec` | |
| `withPtrAddr` | `withPtrAddr` | Lean's (`Init/Util.lean`) |

Not shown: `--jobs` and `--trusted` (command-line options, not
declarations), `Lean.Expr`, `And`, `Nat`, `Nat.add`, `ZFSet`,
`withExclusive` (Lean's and Mathlib's types and functions the prose mentions
in passing).

## What `check` says

con-leche accepts its own development: `leanexport` and `con-leche
--verified` on the five modules' closure took 320 s alongside the extractor
(on a machine also running imprimatur's test suites; peak RSS 1.37 GiB),
and the verdict is then kept, so a later `build` or `check` reads it back
in 1.5 s. The extractor itself takes about 25 s, most of it the dependency
cone of `checkDecls`.

Besides that, `imprimatur check` reports three `untrusted` errors, all
expected:

- `sorryAx depends on sorry`: the block shows the `sorry` axiom itself;
- `ConLeche.Cached.checkDecls` and `checkDecls_consts` have
  `ConLeche.Expr.hasStrLitGo (partial)` in their dependency cone: the
  checker's fold calls a `partial` traversal, which Lean compiles to an
  opaque constant. con-leche's proof is about `checkDecls` as Lean's kernel
  sees it, so this is sound; imprimatur's cone check reports every `partial`
  by policy (docs/trust.md).

imprimatur has no way to cite a declaration as the subject of discussion
rather than as a result the paper relies on; the README does both with the
same backticks. That is a gap the experiment shows.
