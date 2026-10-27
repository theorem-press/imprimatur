# imprimatur — design

*Status: the design as built through M5 (§17), with M6's parts marked
"(M6)" where they are described. Revision 2 (2026-10-17) took in a survey of
prior art (§3), and revision 3 (2026-10-17) spikes S1 (external mode) and S2
(stable hashing), under [docs/spikes/](docs/spikes/). Later sections record
what each milestone found, and §18 states what correctness means.*

*Name: an imprimatur ("let it be printed") is the approval a work receives
before publication. The tool's core job is to let only checked statements into
print. Earlier drafts used the name "leantex", which belongs to an existing
project.*

imprimatur keeps the LaTeX of a paper in step with a Lean development. Authors
mark places in their `.tex` sources where a Lean declaration should appear —
a theorem statement, a definition, a set of inference rules, a grammar — and
imprimatur regenerates that LaTeX from the compiled Lean environment. It can also
check, without generating anything, that hand-written statements still refer
to Lean results that exist, are free of `sorry`, and have not changed since an
author last checked the prose against them.

---

## 1. Goals and non-goals

**Goals**

- Render Lean declarations as LaTeX in several styles, from verbatim Lean
  signatures (zero configuration) to typeset mathematics using the paper's own
  macros.
- Splice the output into existing `.tex` files idempotently, without
  clobbering hand edits. The `.tex` files stay ordinary LaTeX that compiles on
  Overleaf and arXiv with no preprocessor and no `--shell-escape`.
- Work for any Lean 4 project, including Mathlib-based ones, without editing
  the project's proof sources and, where needed, without editing its lakefile.
- Tie hand-written prose to the Lean results it describes, and fail the build
  when those results change, disappear or depend on `sorry`.
- Support anonymous submission: nothing generated may identify the authors.

**Non-goals**

- Running code blocks or capturing program output (a separate concern, which
  one motivating project handles with a tool of its own).
- Producing whole documents (as doc-gen4, Verso or Isabelle's document
  preparation do). imprimatur fills holes in documents that humans write in
  ordinary LaTeX.
- Planning a formalisation or drawing dependency graphs (leanblueprint and
  LeanArchitect do this; §3).
- Typesetting proofs.

## 2. Motivating projects

The design was checked against three projects with different needs.

Two of them are programming-language papers under anonymous review, so
they are called project A and project B here.

| | project A (a PL paper) | math catalogue | project B (a PL paper) |
|---|---|---|---|
| Lean toolchain | v4.28.0-rc1 | v4.34.1 (uses the module system) | v4.31.0 |
| Depends on Mathlib | yes | yes, plus about 15 other libraries | yes |
| TeX layout | one large `paper.tex` | one large `overview.tex` | about 20 files joined with `\input` |
| What it needs | inference rules, grammars, theorems and definitions as typeset maths; a provenance index | the statements of the main theorems inside catalogue entries | rules generated from an inductive derivation relation; hand-written theorem prose checked against a Lean file of restated results; an appendix index |
| Existing metadata | hard-coded export lists | `formalization.yaml`, plus a comparator manifest per result in `ComparatorChallenges/*.json` | a Lean file restates every numbered result |
| Constraints | already has a hard-wired version of this tool to replace | proof sources must not be edited | anonymous submission; the Lean project is shipped as the supplement and must not change |

Project A's existing implementation (Lean exporters for rules, grammars,
conventions and translations, and the splicing half of a build tool, about
4,000 lines) is the starting point. Its rendering ideas carry over. Its hard-wired parts do not: rule symbols are chosen by
string-matching name prefixes, exported declarations are hard-coded lists,
the imported modules are fixed in `Main.lean`, and the splicer knows the
paper's environments by name.

## 3. Prior art and positioning

A survey of related tools (Gemini Deep Research, October 2026; the claims
still to be checked are listed in Appendix A) found no tool that combines all
of imprimatur's parts. The pieces exist separately, and imprimatur borrows from
each:

| Tool | What it does | What imprimatur takes from it | Where imprimatur differs |
|---|---|---|---|
| **leanblueprint** + **checkdecls** (Massot) | `\lean{…}` and `\leanok` macros in blueprint LaTeX; `checkdecls` checks that the named declarations exist | the macro ergonomics already familiar to the Lean community; imprimatur reads `\lean{…}` as a check-only reference (§9.3) | also checks `sorry`, axioms and statement drift; renders content |
| **LeanArchitect** (Zhu, ITP 2026) | `@[blueprint]` attributes; infers dependencies and `sorry` status; writes fragments that `\inputleannode` pulls in | auditing a declaration's dependency cone | the LaTeX statement is written by hand in a docstring and can drift; imprimatur renders from the Lean term, and changes no Lean source |
| **comparator** (leanprover), **AxiomSweep** (ArkLib) | check that a solution proves a pinned challenge statement using permitted axioms only | the trust checks: permitted axioms, and auditing the declarations used in the statement (§7.7); comparator manifests as a source of entries (§10.5) | links the check to the prose that describes the result |
| **plectis** (Cook, 2026) | a registry of public claims, each recording its approved wording and supporting Lean theorems | a human-reviewed commitment to a statement hash (`\leancheck`, `imprimatur accept`) | the commitment lives in the paper itself, not in a separate registry |
| **Isabelle** antiquotations | `@{thm}`, `@{term}` with print modes (`source`, `rule`, `names_short`, `no_vars`) | the vocabulary for view options (§9.1) | the paper is ordinary `.tex`, not generated from `.thy` files |
| **HOL4** LaTeX munger | `\HOLthm[options]{Thy.name}` in `.htex`, expanded into `.tex`; override maps from tokens to LaTeX | display widths in notation rules; theorem modifiers such as `rule`, `def` and `nosp` | edits the file in place instead of generating a separate `.tex` |
| **Agda** `--latex` | semantic macros (`\AgdaFunction`, `\AgdaBound`, …) defined in `agda.sty` | semantic macros in the `lean` view (§7.3) | content is picked by declaration name, so the paper's order is free of the source order |
| **Ott**, **Lem** | one spec produces grammars and `\inferrule`s in LaTeX, plus prover definitions | splitting each constructor into an inference rule; hiding value predicates through metavariable conventions; grouping productions (§7.4–7.5) | works backwards from Lean definitions that already exist, rather than from a separate spec |
| **PLT Redex**, **K** | typeset grammars and judgment forms from executable semantics; K uses `[latex(…)]` attributes with `#1` placeholders | rendering a chosen subset of rules per block; positional placeholders | |
| **sTeX** / MMT | semantic LaTeX macros tied to formal symbols, with several notations per symbol | named notation variants; flattening chains of associative operators | authors don't write semantic macros. The sTeX authors report this burden as the main reason it saw little uptake outside their group |
| **Cog** (Batchelder) | splices generated text in place between markers; base64 checksums against hand edits; `--check` and `--diff` for CI; `-d` strips markers | the splicer's state machine and command-line conventions (§10) | understands TeX environments and follows `\input` |
| **doc-gen4**, **Verso**, **LeanInk**, **Alectryon** | HTML documentation and literate documents, generated from Lean | how to load an environment (doc-gen4); `--lake`-style operation from outside a project (LeanInk); a JSON layer between prover and renderer (Alectryon) | output is spliced into LaTeX that people write; output contains no repository URLs |

**Conclusion.** Build imprimatur as a new tool, and make it able to coexist with
the blueprint ecosystem.

- **Blueprint documents.** imprimatur reads `\lean{…}` in blueprint documents as
  check-only references (§9.3), so a blueprint project gains stricter checks
  than `checkdecls` without changing its documents.
- **Comparator manifests.** imprimatur can import comparator manifests (§10.5),
  so projects already audited by comparator get entries automatically.

## 4. Constraints that shape the design

1. **The extractor must match the host's Lean version exactly.** It loads the
   host's `.olean` files with `importModules`, and Lake compiles a dependency
   with the host's toolchain. The three projects above use three toolchains.
2. **The splicer doesn't need Lean at all.** It only edits text, so tying it
   to a toolchain is unnecessary.
3. **Declaration names must be checked.** A notation rule that names a
   renamed constant must fail loudly at build time. With project A's string
   prefixes, a rename silently falls back to the default rendering.
4. **Hand-writing renderers per constant doesn't scale for Mathlib-heavy
   projects.** A useful default rendering must exist for every declaration.
5. **Some host projects can't be touched.** These include supplementary
   artifacts and repositories owned by other people.
6. **No extra pins on dependencies.** A tool that brings its own versions of
   `batteries` or `Cli` into a Mathlib project can shift Mathlib's pins and
   force Mathlib to rebuild from source; the survey cites this happening with
   LeanArchitect. The extractor therefore depends on Lean core only and has no
   Lake dependencies at all.
7. **The module system hides proof bodies at lower levels.** Since Lean 4.2x,
   `.olean` data comes in levels (`exported` < `server` < `private`). Checks
   for axioms and `sorry` need the proof bodies, which are only in `private`.
   In v4.34.1, `importModules` takes a `level` argument whose default is
   `.private` (verified in `Lean/Environment.lean`). The extractor always
   passes it explicitly, through `Compat.lean` (§13).

## 5. Architecture

```
                 ┌──────────────── host Lean environment ────────────────┐
 paper/*.tex ──▶ │ scan ──▶ requests.json ──▶ imprimatur-export ──▶ bundle  │ ──▶ apply ──▶ paper/*.tex
   (splicer)     │                            (extractor, runs            │    (splicer)
                 │                             with host toolchain)       │
                 └────────────────────────────────────────────────────────┘
```

There are two Lake packages in one repository, and they communicate only
through a versioned JSON **bundle**. This is the same separation Alectryon
makes between prover drivers and rendering.

- **`imprimatur` (the extractor)** is a Lean library and the `imprimatur-export`
  executable. It depends on Lean core only (constraint 6). It must compile
  under every supported toolchain.
- **`imprimatur-splice` (the splicer)** is a Lean executable with no dependence
  on Lean internals, built with its own pinned toolchain and also shipped as
  prebuilt release binaries. It scans TeX for requests, applies bundles,
  checks documents and strips markers.

Because the bundle is a public contract (§8), other producers could later
feed the same splicer, such as an Isabelle or Rocq exporter, or a script.

A wrapper command `imprimatur` runs the whole flow:

- `imprimatur build` runs scan, then export, then apply.
- `imprimatur check` runs the same steps without writing, and exits non-zero if
  anything is out of date or fails a trust check.

## 6. Configuration

There are two kinds of configuration, and they are kept separate on purpose.

- **Anything that names a Lean declaration is written in Lean.** This covers
  notation, entries, groups, premise conventions and custom views. It lives
  in a *notation module* that Lean elaborates, so every name is resolved and
  checked.
- **Project wiring is written in TOML.** This covers paths, profiles, tag
  aliases, manifests, scoped namespaces and modules to import. It lives in
  `imprimatur.toml` next to the main `.tex` file.

### 6.1 `imprimatur.toml`

```toml
schema = 1
main = "paper.tex"                        # entry point; \input/\include are followed
lean_project = "lean"
mode = "external"                         # external | sidecar | in-project (§6.3)
imports = ["MyPaper.Results"]             # modules to read declarations from
notation = ["tex/PaperTeX.lean"]          # notation modules
strip_namespaces = ["MyPaper", "MyPaper.Results"]
open_scoped = []                          # e.g. ["Topology", "BigOperators"], for the lean view
notation_packs = ["core", "logic"]        # §7.5
verbatim_envs = []                        # extra environments the scanner skips (§10.1)
known_macros = []                         # macros packages define, e.g. ["toprule"] (§10.3)
validate = true                           # read rendered formulas back (§18.4)
default_profile = "submission"

[profile.submission]
source_links = "relative"                 # MyPaper/Results.lean:122 (§11)

[profile.camera-ready]
source_links = "url"
url_template = "https://github.com/ORG/REPO/blob/{commit}/{path}#L{line}"

[aliases]                                 # existing environment names → generic block
leantheorem = { view = "math",  wrap = "theorem" }
leanlemma   = { view = "math",  wrap = "lemma" }
leandef     = { view = "math",  wrap = "definition" }
leanrules   = { view = "rules" }
leangrammar = { view = "grammar" }

[trust]
allowed_axioms   = ["propext", "Classical.choice", "Quot.sound"]
trusted_prefixes = ["Mathlib", "Std", "Batteries", "Lean", "Init"]   # module prefixes (§7.7)

[manifests]                               # §10.5
comparator = []                           # e.g. ["ComparatorChallenges/*.json"]
blueprint  = false                        # read \lean{…} as check-only references
```

### 6.2 Notation module

This is an ordinary Lean file, and the only file that imports `imprimatur`
(more examples in §7.5):

```lean
import Stlc
import Imprimatur

open Stlc

latex_notation HasType Γ e t      => r"#Γ \vdash #e : #t"   prec := 50
latex_notation Step e e'          => r"#e \longrightarrow #e'" prec := 50
latex_notation Tm.lam x t e       => r"\lambda #x{:}#t.\, #e" prec := 10
latex_notation Ty.arrow a b       => r"#a \to #b"   prec := 25  assoc := right  width := 3

latex_group "Typing rules" := [HasType.var, HasType.lam, HasType.app, HasType.unit]

latex_entry "Preservation" => Stlc.preservation  options := "forall"
latex_style names := raw
```

Its commands (M5): `latex_notation`, `latex_metavar`, `latex_style` (§7.5);
`latex_entry`, a key of the document that is a title rather than a name, with
block options that apply to all its views (§9.1); `latex_group`,
`latex_rules`, `latex_rule_label` (§7.4); `latex_metavar_convention`,
`latex_hide_premise` (§7.6); `latex_category` (§7.3); and `@[latex_view]`.
In external mode the module may be several files, elaborated in turn in one
environment, so a large one can keep its tables apart.

The notation module is not itself a `module` file, so that elaborating it
sees `private` data (constraint 7).

**Naming convention.**

- **Lean commands** are prefixed `latex_` (`latex_notation`,
  `latex_entry`, `@[latex_view]`, …) because they describe output rather than
  the tool. They are visible only in the notation module, which is the only
  file that imports `Imprimatur`, so they cannot clash with the host project.
- **TeX markup** keeps the `lean` prefix (`leanblock`, `\leanref`,
  `\leancheck`, `\leanindex`) because it marks Lean content in the paper.
- **The tool itself** is named `imprimatur` in packages, commands and files
  (`imprimatur.toml`, `imprimatur.sty`, `imprimatur-bundle/1`).

### 6.3 How a project uses imprimatur

There are three modes. All of them end with the extractor running against an
environment that contains the host's modules and the notation module.

**A. External runner (recommended default).**

- `imprimatur toolchain install v4.31.0` builds the extractor and the `Imprimatur`
  library once per toolchain into a user cache. The toolchain is read from
  the host's `lean-toolchain`.
- At run time, imprimatur takes the host's search path from `lake env` in the
  host project, adds its own cached `Imprimatur` `.olean` files, and elaborates
  the notation module in-process with Lean's frontend. The resulting
  environment already contains the requested modules at `private` level, so
  nothing is imported a second time. Spike S1
  ([docs/spikes/S1-external-mode.md](docs/spikes/S1-external-mode.md))
  showed this working on all three motivating projects. For a Mathlib-based
  host it needs about 7 GB of memory.
- The host's lakefile, manifest and sources are untouched, and there is no
  extra checkout of Mathlib. This is LeanInk's `--lake` pattern.
- It suits all three motivating projects, and is the only mode the math
  catalogue needs.
- **The cache (M3).** The extractor's cache is `IMPRIMATUR_CACHE`, or
  `~/.cache/imprimatur`, with one directory per toolchain. External mode
  never builds the host; the host's owners build it.

**B. Sidecar package.** A small Lake package next to the host requires the
host by path, plus `imprimatur`:

```toml
# tex-lean/lakefile.toml
name = "paper-tex"
[[require]]
name = "my-paper"
path = "../lean"
[[require]]
name = "imprimatur"
git = "https://github.com/theorem-press/imprimatur"
rev = "v0.3.0"
subDir = "extract"
[[lean_lib]]
name = "PaperTeX"
```

- `imprimatur init --sidecar` (M6, #31) will create it, copy the host's
  toolchain, and pin shared dependencies to the host's manifest. Until then
  it is written by hand, as in `examples/sidecar`.
- It costs one extra checkout of the dependencies; for Mathlib, use
  `lake exe cache get`.
- Use it when the notation module needs Lake features: it spans several
  files, or it defines custom views that must be compiled.

**C. Inside the project.** The host adds `require imprimatur … subDir =
"extract"` and a library for the notation module.

- Because imprimatur has no dependencies, this cannot disturb Mathlib's pins
  (constraint 6).
- It is the simplest mode when you own the project and its lakefile is not
  an artifact in its own right. Project A was planned this way, but uses
  external mode (§16).

## 7. The extractor (`imprimatur`)

### 7.1 Pipeline

```
Name ─▶ ConstantInfo ─▶ view renderer ─▶ Doc ─▶ LaTeX emitter ─▶ string
                          ▲      │ (unmatched subterm)
     notation registry ───┘      └──▶ delaborator ─▶ Syntax ─▶ token macros
```

`Doc` is a small intermediate tree. It has:

- text and macro nodes;
- infix, prefix and postfix operators with precedence and associativity;
- flattened n-ary operator chains;
- applications;
- binder telescopes;
- inference-rule nodes;
- grammar productions;
- line-break hints with display widths.

Escaping, parenthesisation and line breaking happen once, in the emitter.

### 7.2 Notation matches `Expr`, and the delaborator renders what is left

The survey recommends delaborating first and pattern-matching on the
resulting `Syntax`, to avoid exposing instance arguments
(`@HAdd.hAdd ℕ ℕ ℕ inst a b`). imprimatur takes a hybrid approach.

- **Notation rules match on `Expr`, not `Syntax`.** Rules name constants,
  which Lean checks (constraint 3). Matching on `Expr` doesn't depend on which
  namespaces are open, on pretty-printer options, or on surface syntax that
  differs between toolchains. Instance and implicit arguments are hidden by
  binder info, and the notation packs (§7.5) cover the arithmetic, order,
  set, logic and coercion constants that would otherwise leak through.
- **Unmatched subterms go to Lean's delaborator.** A subterm that no rule
  matches is delaborated with the configured `open_scoped` namespaces active.
  The resulting tokens are emitted with the semantic macros of §7.3. Every
  declaration therefore renders legibly with no configuration, and notation
  improves the rendering bit by bit.

### 7.3 Views

| View | Output | Configuration needed |
|---|---|---|
| `lean` | the declaration's signature, pretty-printed by Lean (delaborator and `ppSignature`, with `open_scoped` active). Tokens are wrapped in semantic macros (`\LeanKeyword`, `\LeanConst`, `\LeanBound`, `\LeanSort`, …, in the manner of `agda.sty`) defined in `imprimatur.sty`. There are no verbatim environments, so the output works inside macro arguments | none |
| `meta` | source location (§11), axioms used, `sorry` status, docstring | none |
| `math` | the statement as a formula (§7.2) | notation |
| `prose` | "Let …. Assume …, (h₂) …. Then …": explicit Prop binders become hypotheses, labelled with their names where the paper refers to them (`\leanhypref{key}{h}`, M5), and the conclusion is split at `∧` | notation |
| `rules` | each constructor of an inductive predicate becomes a mathpartir `\inferrule`; premises are its Prop-typed binders, in order, after premise conventions are applied (§7.6) | notation, groups |
| `grammar` | inductive types become BNF alternatives, and structures become field lists. Constructors can be grouped into productions on one line or on separate lines, with a comment column (as in Ott). Each comment is an author-owned slot (§9.5), and the constructor's docstring supplies its default text | notation, groups |

**How the `lean` and `meta` views are made (M2).**

- **`lean`.** Lean's `ppSignature` prints the signature. The printed text is
  then split into tokens, and each identifier is classified: a bound
  variable (from the type's binders), a constant (by name resolution, with
  `strip_namespaces` open), a keyword or a sort. Working on the text keeps the
  output identical across toolchains. The fixtures' bundles are
  byte-identical from v4.28 to v4.35.
- **`meta`.** The extractor writes `\leanmetasource{}` for the source
  location, and the splicer fills it according to the active profile (§11).
- **Requests.** The extractor reads its settings (`imports`, `open_scoped`,
  `strip_namespaces`) from `requests.json`, which `scan` writes, so it needs
  no TOML parser.

**Projects can add their own views.** A project registers
`@[latex_view "name"] def myView : ViewFn` in its notation module. The
extractor discovers it through the attribute and runs it with `evalConst`, in
the renderer's monad, with the key, the declaration (if any) and the block's
options. It also sees the document's inventory (§10.1): the blocks, with the
labels the splicer gives them, and the paper's `\label`s, in document order.
A grammar whose forms are hand-written TeX is a custom view rather than the
generic `grammar` view, as are project A's theorem prose and provenance
index (§16).

### 7.4 Rule labels

The label of a `rules` entry is chosen in this order:

1. an explicit `latex_rule_label HasType.app "T-App"`;
2. otherwise, a docstring that starts `Label: …` or `Label.` supplies
   `Label`, following the `/-- T-App: … -/` convention of the motivating
   projects;
3. otherwise, the constructor name, prettified (`i_nest` becomes `I-Nest`).

`latex_rules I` sets, per inductive, the template the label goes in, the
macro that anchors each rule (`\rulelabel{Key}{label}%`), the text between
the words of a name (`sep := " "` gives `Scalar Lit`), and whether docstrings
supply labels (`doc_labels := false` when they are prose such as
`Variables: …`). A `latex_group` may mix constructors of several inductives;
each takes its own inductive's style.

### 7.5 Notation rules

```lean
latex_notation SetRealization.Realize U φ ρ    => r"#U \models #φ"     hide ρ := Fin.elim0
latex_notation ¬ SetRealization.Realize U φ ρ  => r"#U \not\models #φ" hide ρ := Fin.elim0
latex_notation partitionPrinciple              => r"\mathsf{PP}"       width := 2
latex_notation Fintype.card C                  => r"|#C|"              prec := max
latex_notation (variant := "named") Tm.app e₁ e₂ => r"\mathsf{app}(#e₁, #e₂)"
latex_notation Label.lub a b                   => r"\lub{#a, #b}"      flatten
```

- **Pattern.** The left-hand side is a pattern whose head is a constant, with
  nested patterns allowed. Pattern variables bind explicit arguments.
  Implicit and instance arguments are hidden unless the pattern names them,
  in `@` form. For example, `@LE.le (Set _) _ a b` matches `≤` only on sets.
  - **As implemented (M4).** The pattern is elaborated as an ordinary term.
    Each identifier that names no constant is bound as a pattern variable of
    unknown type, so notation such as `=` and `¬` works in patterns.
  - **`hide x := v`.** `v` is itself a pattern, so `Fin.elim0` matches
    whatever its implicit arguments are.
  - **Binders (M5).** A pattern may bind a variable: `fun x => e`, `∀ x, p`,
    `p → q`, and a constant applied to a `fun` (`∃ x, p`, `∑' x, f`,
    `{x | p}`). Matching opens the binder, so the variable renders as its
    bound name and the body in scope. `∀ x, p` matches a quantifier whose
    body mentions `x`, `p → q` an implication or function type; both
    override the built-in forms. A constant applied to fewer arguments than
    it takes matches that partial application.
- **Template.** `#x` inserts the rendering of a pattern variable, as with
  K's positional placeholders and Ott's homomorphisms.
- **`prec`** sets the precedence of the result when nested. A variable inside
  braces, or in an atomic template, needs no parentheses. A variable at the
  top level needs the rule's precedence, with operators associating to the
  left. Pack rules also set their associativity.
- **`width`** is the rendered width in characters, which the line breaker
  uses instead of the length of the LaTeX source. Without it, long macro
  names cause premature line breaks; this is a lesson from HOL4's munger.
- **`hide x := v`** applies the rule only when `x` is definitionally equal to
  `v`, and leaves `x` out of the output; **`when x := v`** applies it only
  when `x` matches the pattern `v`, and shows `x` (M5).
- **`variant`** names an alternative notation for the same constant. A block
  selects it with `notation=named`, after sTeX's multiple notations per
  symbol.
- **`flatten`** applies to associative operators: a nested chain renders as
  one n-ary call (`\lub{a, b, c}`, or `a + b + c` for infix operators),
  after sTeX's `seq`. On a binder rule it folds a chain of binders into one
  list of variables (`\exists\, a,\, b,\; p`), separated by **`sep`**.
- **`assoc`** is `left` (the default), `right`, or `none`, which
  parenthesises both operands at the rule's own precedence, as one motivating
  paper does for `∧` next to `∨`.
- **`latex_style`** fixes conventions of the renderer for the whole paper
  (the table is in [docs/notation.md](docs/notation.md)):
  - `names := raw` writes binder names as they are (they are TeX: `l_c`),
    rather than escaped and in `\mathit`;
  - `applied_variables := call` or `subscript` writes an applied variable as
    `f(a)(b)` or `f_{a, b}`;
  - `pattern_matching := cases` writes a `match` as
    `\mathsf{case}\ d\ \mathsf{of}\ p \Rightarrow e \mid \dots`;
  - `lists := literal` writes a list literal as `[a, b]`.

  Greek binder names are always macros (`\varepsilon`).
- **Binder names.** A binder Lean named that nothing uses is written `_`; a
  λ that binds a proof is not shown, since proofs are not (`if h : c then a
  else b` is `if c then a else b`). The variables of a case's patterns, and
  λ binders, are renamed when their names are already in scope. In an
  equation lemma, binders with Lean's generic names (`a`, `x✝`) are named
  after their types' categories (`latex_category`), or after the
  definition's own parameters; names the author wrote are kept.
- **Patterns.** In a pattern (a case's, or an argument on the left of an
  equation), a rule that writes a constructor as its bare argument
  (`Sum.inl a => "#a"`) gives way to one that shows the constructor, if the
  module has one, since the constructor is what the pattern tests.
- **Order of lookup.**
  1. The project's rules. The most specific pattern wins, and declaration
     order breaks ties.
  2. Notation packs shipped with imprimatur (`core`, `logic`, `sets`,
     `order`; a `mathlib-common` pack is not yet written, #36). A pack is
     selected in `imprimatur.toml`, and its rules are stored as names, so
     imprimatur still doesn't depend on Mathlib.
  3. The delaborator fallback (§7.2).
- **Metavariables.** A trailing digit or a Unicode subscript becomes a LaTeX
  subscript. `latex_metavar` renames a binder, for example rendering
  `spec` as `L`.
- **Macros come from the paper.** The bundle records the macros each
  rendering uses (§8), so the splicer warns about macros that are not
  defined anywhere in the document (§10.3).

### 7.6 Premise conventions (for `rules` and `prose`)

A mechanised rule carries premises that a paper leaves implicit. Two
declarations hide them:

```lean
-- Ott-style value convention: hide `IsValue v` premises and render v as the metavariable \val.
latex_metavar_convention Expr.IsValue v => r"\val"
-- ORBI-style well-formedness: hide premises matching a pattern.
latex_hide_premise Ctx.WF _
latex_hide_premise (_ : Fintype _)
```

Instance binders are always hidden. Block options `show=` and `hide=`, to
override these choices per block, are designed but not implemented (#35).

### 7.7 Trust metadata

For every entry, the extractor imports the environment at `private` level
(constraint 7) and computes the following.

- **Axioms** used by the declaration, via `collectAxioms`.
- **`sorry`**: whether it depends on `sorryAx`.
- **The statement's dependency cone**, following comparator. This is every
  constant appearing in the declaration's type, followed transitively through
  definitions until it reaches a constant declared in a module whose name
  starts with an entry of `trusted_prefixes`.
  - The test is on modules, not namespaces. Core constants such as `Nat.add`
    are declared in `Init.Prelude` but in no `Init` namespace.
  - Recursive definitions (structural or well-founded) are followed through
    their equation lemmas (`Meta.getEqnsFor?`), not their compiled bodies,
    which differ between toolchains. Other definitions are followed through
    their bodies, which are what the author wrote. Matchers and auxiliary
    recursors count by their type only.
  - M3 revised spike S2 here: generating equation lemmas for every
    definition exhausted memory on a definition in the math catalogue, and
    equations are only needed for recursion.
  - For a theorem or an axiom, the walk starts from the type: the proof
    doesn't count. For anything else, such as a definition or an inductive
    type, the declaration is in its own cone, because its meaning includes
    its definition. M3 found that without this, two definitions with the
    same type had the same hash.
  - `partial` means the kernel sees an `opaque` constant with an
    `_unsafe_rec` implementation. Structural and well-founded recursion also
    generate `_unsafe_rec` helpers, but stay definitions, so they don't count.
  - Each constant in the cone is itself checked for `sorry`, for disallowed
    axioms, and for `unsafe` or `partial`. The bundle records each untrusted
    member with its reasons (`sorry`, `axiom`, `partial`, `unsafe`), and the
    splicer accepts the axioms that `allowed_axioms` (or a manifest's
    `permitted_axioms`) lists.
  - Without this, someone could change a definition used in the hypotheses
    to `True`, and the theorem would become trivial while its own statement
    looked unchanged.
- **`stmtHash`** is a SHA-256 hash of a canonical serialisation of the
  declaration's type, together with each definition in its cone. A recursive
  definition is represented by its type and the statements of its equation
  lemmas; any other definition by its type and body.
  - Compiled recursion is not used, because its elaborated form changes
    between toolchains. For example, structural recursion compiles
    differently in v4.28 and v4.31. Equation lemmas were byte-identical from
    v4.28 to v4.35 in spike S2
    ([docs/spikes/S2-stable-hashing.md](docs/spikes/S2-stable-hashing.md)).
  - The serialisation is a Merkle hash: each subterm is written in terms of
    its children, and replaced by its own SHA-256 once longer than 64
    characters. It is memoised on shared subterms, so its cost is linear in
    the term as Lean stores it. The math catalogue has a definition of 3,813
    shared nodes, which is more than 10^8 nodes as a tree.
  - Binder names are dropped and universe parameters are renamed to
    canonical names.
  - Every `sorryAx` application is serialised as one fixed token, because an
    elaborated `sorry` carries a tag that encodes where it was written.
  - The environment is imported with `loadExts := true`. Without it,
    equation lemmas can't be generated for imported definitions.
  - imprimatur writes its own serialisation and does not use Lean's
    `Expr.hash`, so the hash stays the same across toolchain upgrades.
  - The hash changes when the statement, or anything in the project that the
    statement depends on, changes in meaning. It does not change when a proof
    changes.
- **`sigHash`** is a hash of the `lean` view's text. A change in `sigHash`
  alone (a binder renamed, notation changed) produces a warning, not an error.
- **`\leancheck` records 12 hexadecimal digits of each:** `stmt=` and `sig=`.
  With several keys, they are digits of the hash of the keys' hashes joined
  by commas. `imprimatur accept KEY…` (or `--all`) writes them. The
  details for authors are in [docs/trust.md](docs/trust.md).

## 8. The bundle (`imprimatur-bundle/1`)

The bundle is a Lean type, `Bundle (Image TeX) Verdict` in
`bundle/Bundle.lean`, and the file is its JSON: the extractor writes it
with `Bundle.render` and the splicer reads it with `Bundle.parse`, and an
extractor's bundle survives the round trip byte for byte. The module is
copied into both packages (constraint 6 forbids a shared dependency) and
into the paper's model, under the module name the extractor gives it;
`lint/bundle-copies` keeps the copies equal. An entry is `Entry σ π`, what a
key names, its statement as `σ` and the verdict on its proof as `π`; the
file is at the statement's images (`Image`: the hashes and the views) and
the verdict (`Verdict`: axioms, `sorry`, the cone), and the model of the
splicer (§18.2) at bodies with their slots parsed and a bit. The module also
says what makes a bundle true of an environment (`World`, `Image.Of`,
`Bundle.True`), which is Theorem 1's hypothesis. A group's entry (a
`latex_group` or `latex_display`) states what its members state: its hash
and cone are theirs, united.

```json
{
  "schema": "imprimatur-bundle/1",
  "producer": { "tool": "imprimatur-export", "version": "0.3.0",
                "lean": "v4.31.0", "project": "my-paper" },
  "entries": {
    "MyPaper.Results.theorem1_main": {
      "kind": "theorem",
      "decl": "MyPaper.Results.theorem1_main",
      "source": { "path": "MyPaper/Results.lean", "line": 122 },
      "doc": "**Theorem 1 (1).** If `main(x)` is derivable, ...",
      "axioms": ["propext", "Classical.choice", "Quot.sound"],
      "sorry": false,
      "cone": { "size": 14, "untrusted": [] },
      "stmtHash": "b41c…",
      "sigHash": "07ae…",
      "macros": ["\\judge"],
      "views": { "lean": "…", "math": "…", "prose": "…", "meta": "…" }
    }
  }
}
```

- **Determinism.** Keys are sorted, and output contains no timestamps.
- **Paths.** `source.path` is relative to the Lean project root. Absolute
  paths, user names, repository URLs and commit hashes never appear. Profiles
  add URLs at splice time (§11).
- **Slots.** A view's text marks its slots as
  `\leanslot{id}{default text}`. The splicer parses these when it applies the
  bundle (§9.5), so no separate slot list is needed.
- **Schema evolution.** Changes within a major version only add fields. A
  view that fails to render is recorded under `errors.<view>`, and is an
  error only if a block asks for that view.

## 9. TeX syntax

### 9.1 Generic forms

```latex
\begin{leanblock}[view=math, wrap=theorem, sum=Rwh4n2CfQD]{MyPaper.Results.theorem1_main}{Soundness}
…generated…
\end{leanblock}

\leaninline[sum=…]{SetFormula.choice}{…generated…}    % inline; regenerates arg 2
\leanref{MyPaper.Results.theorem1_main}{…generated…}     % source location, per profile (§11)
\leancheck[stmt=b41c]{MyPaper.Results.theorem1_main, MyPaper.Results.theorem1_inter}
\leanindex                                            % table of every key used in the document (M6, #25)
```

The options of `leanblock`:

- **`view`**, **`wrap`** (an environment to put the content in, such as
  `theorem`) and **`label`**;
- **`sum`**, the checksum of the generated content (§10.2);
- **`notation`**, which selects a notation variant (§7.5);
- **`include`** and **`exclude`**, which select constructors for a `rules` or
  `grammar` view, as PLT Redex does. With them, one inductive can be
  presented a few rules at a time across sections;
- **`show`** and **`hide`**, which would override premise conventions
  (§7.6; not implemented, #35);
- **theorem modifiers**, after Isabelle's print modes and HOL4's `\HOLthm`
  options:
  - `rule` renders `A → B → C` as an inference rule;
  - `def` renders a definition's equation lemmas as an aligned block;
  - `forall` shows the outer quantifiers, which are hidden by default;
  - `names=short|full` sets how much of each name's namespace is shown.

`\leanref`, `\leancheck` and `\leanindex`:

- **`\leanref`** is expanded by the splicer according to the active profile
  (§11). Like `\leaninline`, it has a second argument that the splicer
  fills; authors write `\leanref{key}{}`. It carries no checksum and is always
  regenerated.
- **`\leancheck`** generates nothing. It ties hand-written prose to Lean
  (§10.3). This is plectis's idea of a reviewed claim, kept inline in the
  paper.
- **`\leanindex`** (M6, #25) will replace project A's provenance table, which
  is a custom view for now, and list every result in project B's Lean
  appendix. The
  scanner already recognises it. The `provenance` view (docs/views.md) is its table, as a block; the
  `conventions` and `vocabulary` views index the document's metavariables and
  its library notation in the same way.

### 9.2 Aliases

The `[aliases]` table maps existing environment names (`leantheorem`,
`leanrules`, …) onto `leanblock`, so projects keep their current markup.

An alias can also shape its blocks' content (M5), so that markup the old
tool generated keeps being generated:

- **`label = "thm:{key}"`** writes a `\label` from the key, and
  **`repeat_suffix = "-appendix"`** distinguishes a key stated again
  (`-appendix`, `-appendix2`, …), counted per alias;
- **`template`** is the content, over `{content}`, `{label}`, `{key}` and
  `{title}`: `"\\label{{label}}\n\\({content}\\)"`;
- **`comment = true`** makes the alias a region delimited by comments,
  `%NAME{key}{title}` … `%ENDNAME`, for a row of a tabbing display where an
  environment would disturb TeX.

### 9.3 Blueprint compatibility

- **Reading blueprints.** With `manifests.blueprint = true`, the scanner
  reads leanblueprint's `\lean{a, b}` as check-only references, the same as
  `\leancheck` without a recorded hash. `\leanok` is cross-checked: a node
  marked `\leanok` whose declarations depend on `sorry` is an error.
- **Writing blueprint markers (M6, #30).** `imprimatur build --blueprint-compat`
  will also write `\lean{…}` inside generated blocks, so a paper can feed a
  blueprint dependency graph.

### 9.4 `imprimatur.sty`

This file ships in the repo. It defines the environments and macros above,
the semantic token macros of the `lean` view, and the `meta` badges.
`\leanblockalias{NAME}{WRAP}` defines an alias environment. A table of
`\newunicodechar` mappings covers the symbols Lean prints, so pdfLaTeX needs
no special fonts (see [docs/views.md](docs/views.md)). A
document still compiles without imprimatur installed; it shows the content last
spliced in.

### 9.5 Author-owned slots

Some parts of a generated block belong to the authors, not to Lean. Examples
are the description column of a grammar, a gloss beside an inference rule,
and the description column of `\leanindex`. A view marks such a part as a
**slot**. imprimatur regenerates everything around a slot and never
overwrites the text inside it.

```latex
\begin{leanblock}[view=grammar, sum=…]{Core values}{Values}
\entry{v ::= \lambda x.\,e}{\leanslot{Expr.lam}{a function}}
\entry{\mid c}{\leanslot{Expr.scalar}{a scalar constant; edited by hand}}
\end{leanblock}
```

- **Identity.** A slot has a stable id chosen by the view, usually the name
  of the declaration or constructor it describes. Text is matched by id, not
  by position or by the surrounding formula. A slot's text therefore
  survives changes to the notation that would alter the formal part.
- **Default text.** For a new slot, the view supplies the default text, for
  example the constructor's docstring. A block with slots records a digest
  of its slots' default texts in `dflt=`. While the slots still match it,
  the authors haven't touched them, so a changed default replaces them.
  Once the authors edit a slot of the block, the text belongs to the
  authors: every slot of the block keeps its text, and a later change of
  default is reported (`slot-default`), listing the slots that differ from
  their new defaults. A digest per block, not per slot, keeps the markup
  unchanged, at the price of treating a block's slots together.
- **Checksums.** Slot contents are replaced by their ids before the block's
  checksum is computed (§10.2). Editing a slot is never a hand edit, and
  editing anything else in the block still is.
- **Orphans.** If a regenerated block no longer contains a slot (for example
  because a constructor was deleted or renamed), `apply` drops the slot and
  prints its id and text, so the prose isn't lost silently. `check` reports
  the orphan as a warning. `imprimatur build --rename-slot old=new` moves a
  slot's text when a renamed constructor should keep it.
- **`\leanslot{id}{text}`** is defined in `imprimatur.sty` to typeset just
  `text`.
- **Slots without the macro, for existing markup.** An alias can declare
  slots by position instead, so a paper whose markup predates imprimatur
  needs no edits:

  ```toml
  [aliases]
  leangrammar = { view = "grammar", slots = { macros = ["\\entry", "\\defentry", "\\Category"], arg = 2, id = "arg1" } }
  ```

  Here the second argument of each of these macros is a slot, identified by
  the text of its first argument. This is exactly what project A's old
  splicer did. Identifying a slot by formal text is
  weaker than by `\leanslot` id, because a change to the notation orphans
  the slot. `imprimatur migrate-slots` rewrites such blocks into the
  `\leanslot` form once a project is ready.

## 10. The splicer (`imprimatur-splice`)

The splicer's state machine and command-line conventions follow Cog, adapted
to TeX environments.

### 10.1 `scan`

- `scan` starts from `main` and follows `\input`, `\include` and `\subfile`.
  Commented-out lines are skipped. Branches of conditionals are all scanned,
  and their blocks maintained, but the scanner records which are typeset
  (M5): not those in a branch that is off (`\iffalse`, the `\else` of
  `\iftrue`, a switch declared with `\newif\ifNAME` and set with
  `\NAMEfalse`, as project A turns appendices off), nor those in a file reached
  only from one. Other conditionals count as on in both branches.
- It also collects keys from the manifests (§10.5).
- It writes every requested key and view to `requests.json`, with the
  document's inventory: the blocks, with the labels the splicer will give
  them and whether they are typeset, and the paper's typeset `\label`s, in
  document order, for views that index the paper.

### 10.2 `apply`

- **Idempotent.** Applying the same bundle twice changes nothing. Only blocks
  whose content changed are rewritten, and a file with no changes is not
  touched, so its timestamp stays the same and `latexmk` doesn't rebuild.
- **Protects hand edits** (Cog's `-c`).
  - Every generated block records a base64 checksum of its content in
    `sum=…`.
  - The checksum is computed after normalising line endings to `\n` and
    removing trailing whitespace. Otherwise, editing through the Overleaf git
    bridge or on Windows would look like a hand edit.
  - The checksum covers only the generated parts of the block. The contents
    of author-owned slots (§9.5) are left out, so editing them is not a hand
    edit.
  - If a block's content doesn't match its checksum, `apply` refuses to
    overwrite it unless given `--force <key>`.
  - Together with slots, this replaces project A's special-case rules for
    preserving last-good output and merging paper-side edits.
- **Keeps slot text.** When it regenerates a block, `apply` copies each
  slot's existing text into the new content, matched by slot id, unless
  the block's slots still hold the defaults recorded in `dflt=` (§9.5).
- **Missing keys.** A key with no entry in the bundle is an error.
  `--keep-stale` makes it a warning and leaves the old content.
- **Rewrites files in place.** Writes are atomic, and every file keeps its
  original line endings and encoding (UTF-8).
- **All or nothing.** If anything is an error, `apply` writes no file at all,
  so a run never leaves a document half updated.
- **Where content goes.** A block's content starts on the line after its
  header when the rest of the header line is blank or a comment, and ends at
  the start of the `\end` line. The details are in
  [docs/blocks.md](docs/blocks.md).

### 10.3 `check`

`check` runs `apply` in memory and reports, without writing:

- **stale** blocks, whose content differs from what the bundle would produce.
  `--diff` prints a unified diff, and `--check-fail-msg` sets the message
  shown in CI (both as in Cog);
- **broken** references in `leanblock`, `\leanref`, `\leancheck`, `\lean`
  and manifest keys, meaning the key doesn't exist;
- **untrusted** results: any key whose dependency cone (§7.7) contains
  `sorry`, a disallowed axiom, or an untrusted `unsafe` declaration;
- **drift**: a `\leancheck[stmt=…]` whose hash differs from `stmtHash`. The
  statement, or something in the project it depends on, has changed since a
  person last checked the prose against it. `imprimatur accept <key>` records
  the new hash after re-reading the prose. A change in `sigHash` alone is a
  warning;
- **undefined macros**: macros used by generated content that nothing
  defines: not a file of the document, a package of the paper's own (a
  `.sty` or `.cls` beside the main file, and the local files it loads), the
  standard set (TeX's primitives, the LaTeX kernel and article class,
  amsmath, amssymb, mathpartir, and imprimatur.sty with the packages it
  loads; `scripts/gen-std-macros.py` lists them), or `known_macros`. A
  warning, once per macro, at its first use;
- **orphaned slots**, as `apply` reports them: slot text whose slot no
  longer exists in the regenerated block (§9.5). Also only a warning;
- **unfaithful renderings**: formulas that do not read back as what they
  render (§18.4). Also only a warning.

`check` exits non-zero on anything except warnings, so it can gate CI and a
pre-submission checklist.

### 10.4 `strip`

`imprimatur strip` (Cog's `-d`) writes a copy of the document with the imprimatur
markers removed, leaving the generated content as plain LaTeX. Use it for
arXiv, or for a journal's production system, when the `leanblock`
environment names shouldn't appear. `imprimatur.sty` makes stripping optional,
not required.

### 10.5 Manifests

Existing metadata can supply entries, so they don't have to be repeated in
TeX or Lean:

- **Comparator manifests** (`ComparatorChallenges/*.json`). Each
  `theorem_names` entry becomes a check-only key, and its `permitted_axioms`
  replace `allowed_axioms` for that key. The manifests' solution modules are
  added to the extractor's imports. Each manifest's
  `challenge_module` statement is also offered as an entry with the suffix
  `@challenge`. It is a restatement that uses only Mathlib and has been
  audited by comparator, and is often the best thing to render in a
  catalogue. A challenge module declares the same names as its solution, so
  the extractor imports each challenge module in a separate environment,
  after the main one is done with.
- **Blueprint `\lean{…}`** (§9.3). Only nodes marked `\leanok` are checked
  for trust; a bare `\lean{…}` marks work in progress.

## 11. Source links and anonymity

The active profile (`--profile`, or `default_profile`, which is `relative`
when not set) controls how `\leanref` and the `meta` view refer to source
code.

- **`relative`** gives `MyPaper/Results.lean:122`, a path inside the
  supplementary artifact. Nothing in it identifies the authors. This is the
  default.
- **`url`** gives a permalink built from `url_template` and the commit hash.
  Use it for camera-ready versions and public catalogues. It must be chosen
  explicitly.
- **`none`** omits locations.

Separately from the profile:

- the bundle never contains absolute paths, user names, URLs or commit
  hashes (§8);
- `check --anonymous` (M6, #26) will scan everything generated for strings like
  `/home/`, `@` or `github.com`;
- external mode (§6.3 A) leaves no trace of imprimatur in the host project.

Unlike leanblueprint and doc-gen4, nothing in the output templates contains a
repository URL.

## 12. Commands

| Command | What it does |
|---|---|
| `imprimatur toolchain install <ver>` | build the extractor for a toolchain (external mode) |
| `imprimatur build [--profile p] [--commit sha] [--force key] [--keep-stale] [--rename-slot old=new]` | scan, then export, then apply |
| `imprimatur check [--profile p] [--diff] [--check-fail-msg m] [--keep-stale]` | the checks in §10.3 |
| `imprimatur accept <key>… \| --all` | record the current statement hash in `\leancheck` |
| `imprimatur show <key> [--view v]…` | print one key's renderings and their validation problems, writing nothing; for working on notation |
| `imprimatur strip -o dir` | write a copy with the markers removed |
| `imprimatur migrate-slots` | rewrite slots declared by position into `\leanslot` form (§9.5) |
| `imprimatur-splice scan\|apply\|check\|strip\|migrate-slots\|accept` | the splicer on its own |
| `imprimatur-export --requests r.json --out b.json` | the extractor on its own |

Planned for M6:

| Command | What it will do |
|---|---|
| `imprimatur init [--sidecar]` | create `imprimatur.toml`, and the sidecar package if asked (#31) |
| `imprimatur build --blueprint-compat` | also write `\lean{…}` (§9.3, #30) |
| `imprimatur check --anonymous` | the anonymity scan (§11, #26) |
| `imprimatur lint` | report binder names that differ from the paper's naming convention (generalised from project A's binder linter; #29) |

A typical `Makefile` addition:

```make
all: imprimatur
	latexmk -pdf $(PAPER)
imprimatur:
	imprimatur build
```

## 13. Toolchain compatibility and versioning

- **Supported range.** Each extractor release states the range of toolchains
  it supports (at the time of writing, v4.28.0-rc1 to v4.35.0). CI builds
  and runs the golden tests on v4.28.0-rc1, v4.31.0, v4.34.1 and v4.35.0.
  Enforcing the range is M6 (#33).
- **Where version differences live.** Differences between Lean versions are
  confined to `Imprimatur/Compat.lean`. They include:
  - the delaborator;
  - `importModules`, including whether it has a `level` argument and what
    its default is;
  - the frontend API used by external mode (for example, from v4.31
    `runFrontend` turns initializer execution off again, so a later
    `importModules (loadExts := true)` must turn it back on).

  If a version break can't be bridged there, that version gets its own
  release tag (`v0.3.0-lean4.28`).
- **Statement hashes** are independent of the toolchain by construction
  (§7.7). A golden test checks that the same declaration gets the same hash
  on every supported toolchain.
- **The splicer** pins its own toolchain and is released as binaries for
  Linux, macOS and Windows.
- **The bundle schema** is versioned on its own and only gains fields within
  a major version. The splicer accepts the current and the previous major
  version.

## 14. Testing

[docs/TESTING.md](docs/TESTING.md) describes the test layers: unit and property tests,
golden tests of the extractor (fixture projects, run on every toolchain in
the matrix) and of the splicer (TeX documents before and after `apply`),
negative trust tests, end-to-end builds of `examples/` with pdflatex and
lualatex. Every test runs from this repository alone, so contributing
needs no access to the papers imprimatur is used for.
[docs/TESTING.md](docs/TESTING.md) says how to run them, and keeps the
traceability matrix from each section here to its tests.

## 15. Repository layout

```
imprimatur/
  README.md  DESIGN.md  CHANGELOG.md  CONTRIBUTING.md  LICENSE
  extract/                        Lake package "imprimatur" (no dependencies)
    Imprimatur/Doc.lean           IR and LaTeX emitter (escaping, precedence, widths, flattening)
    Imprimatur/Render.lean        Expr → Doc; delaborator fallback; telescopes, metavariables, cases
    Imprimatur/Notation.lean      the registry and its environment extension
    Imprimatur/Commands.lean      latex_notation, latex_metavar, latex_style and the other commands
    Imprimatur/Packs.lean         the notation packs
    Imprimatur/Validate.lean      reading renderings back (§18.4)
    Imprimatur/Views/             Lean.lean Math.lean Rules.lean Grammar.lean
    Imprimatur/CustomViews.lean   @[latex_view]
    Imprimatur/Entry.lean         bundle entries, and the views run for each
    Imprimatur/Trust.lean         axioms, sorry, dependency cone, stmtHash, sigHash
    Imprimatur/Export.lean        Requests.lean  Bundle.lean  TeX.lean  Sha256.lean  Version.lean
    Imprimatur/Compat.lean        differences between toolchains
    Main.lean                     imprimatur-export (also the external-mode runner)
    test/                         unit tests and golden bundles of the fixtures
  splice/                         Lake package "imprimatur-splice"
    Splice/Text.lean  Splice/Sha256.lean  Splice/Toml.lean  Splice/Config.lean
    Imprimatur/Bundle.lean  Splice/Diag.lean  Splice/Scan.lean  Splice/Doc.lean
    Splice/Slots.lean  Splice/Apply.lean  Splice/Check.lean  Splice/Strip.lean
    Splice/Manifests.lean  Splice/Cli.lean  Splice/Wrapper.lean  Splice/Version.lean
    Main.lean  SpliceWrapper.lean imprimatur-splice, and the imprimatur wrapper
    SpliceModel/                  the model, its laws and Theorem 1 (§18.2)
    test/
  testkit/                        test-only package: harness, golden files, seeded generator
  test/                           fixtures/ (Lean projects), tex/ (documents), bundles/
  scripts/                        test-all.sh, lint.sh, e2e.sh, and the lint checks
  schema/bundle.schema.json
  tex/imprimatur.sty
  docs/                           blocks.md notation.md views.md trust.md TESTING.md spikes/
  examples/                       minimal/ sidecar/ external/ semantics/
  about/                          a paper about imprimatur, and lean/, its model of the splicer
  .github/workflows/              ci.yml (the toolchain matrix), pages.yml
```

## 16. Adoption in the three projects

**Project A** (external, §6.3 A; done in M5)

- **The parity gate.** Two of project A's papers were built with its old
  exporter and with imprimatur from the same commit of its Lean project, and
  the results differed only in the `sum=` options imprimatur adds. The gate
  passed byte for byte, after which project A deleted its old exporter and
  the gate with it.
- **What project A keeps.** The port lives in project A's own repository,
  shared by its documents: notation for every arm of the old renderer, the
  groups, labels and entries, and four custom views (theorem prose, `≜`
  definitions, the hand-written grammar tables, and the conventions,
  dispatch and provenance tables). Its binder linter and conventions table
  stay in its Lean sources, and a custom view splices the table from there.
- **Hand-written grammar descriptions are kept.** The `leangrammar` alias
  declares the description arguments of `\entry`, `\defentry` and
  `\Category` as slots identified by their first argument (§9.5), which
  reproduces what the old splicer did.
- **Its Lean version is supported.** It uses `v4.28.0-rc1`, a release
  candidate, which is in the supported range (§13).
- **What the gate found.** Two blocks the old tool had left frozen, because
  their theorems were not registered: one is now generated, the other (its
  theorem gone) became plain text. It also showed the old renderer's
  mistakes kept for parity, such as a dropped premise, each now one line to
  delete.
- **What came out of it.** Generic features: binder patterns,
  `latex_style`, `latex_entry`, `when` guards, decorated metavariables,
  alias labels and templates, comment-delimited blocks, the scanner's
  reading of `\newif` switches (so an index leaves out appendices switched
  off while their blocks are kept up to date), and the document inventory,
  which `\leanindex` (M6) will also use.

**Math catalogue** (external, §6.3 A)

- A notation file outside `lean/OAI/` covers `Realize`, `ZFRealization`,
  `partitionPrinciple`, `SetFormula.choice` and so on. Nothing in the Lean
  project changes.
- `[manifests] comparator = ["lean/ComparatorChallenges/*.json"]` turns
  every comparator manifest into a checked key with its permitted axioms.
- Result entry 244 in `overview.tex` gets a `leanblock[view=prose]` for
  `…TransitiveGround.exists_model_partitionPrinciple_without_choice@challenge`.
  That is the audited statement in `ComparatorChallenges/PartitionPrinciple`,
  which uses only Mathlib. The entry also gets a `\leanref` with the `url`
  profile.
- Other entries can use `view=lean` at once, with no notation work.
- `check` ensures that no catalogued result depends on `sorry`, and that the
  catalogue agrees with the comparator manifests.
- **Don't splice into a file that something else regenerates.**
  `overview.tex` appears to be machine-generated (372 identical
  `\resultentry` entries) and belongs to the upstream repository, which has
  no generator script. If upstream regenerates or replaces it, the spliced
  blocks are lost, and `check` reports them as missing.
  - Prefer a companion document that you own. It can `\input` the catalogue,
    or quote selected entries, and carry the `leanblock`s itself.
  - Splice into `overview.tex` itself only once it is known to be
    maintained by hand.
- **The general rule for every project:** imprimatur owns the content of its
  blocks, so the file containing them must be one that people edit, not one
  that another tool writes.

**Project B** (external, `submission` profile)

- **The paper's prose stays hand-written.** About sixty `\leancheck`s, in
  the section and appendix files, tie its theorems and propositions to a
  Lean file that restates them.
- **The rules figure.** The analysis rules are generated from the
  derivation relations, with labels from the constructor docstrings and the
  `Fintype` data hidden by premise conventions. One schematic rule of the
  paper, which stands for four constructors, stays hand-written (§19,
  question 3).
- **A standalone document** is generated from the development: every
  definition and result up to the main theorem, with the paper's core
  syntax as Lean inductive types, in the paper's display style. Only its
  headings, descriptions and connecting sentences are written by hand.
  Rendering all of the definitions found the case, list-literal and
  binder-name features of §7.5.
- **Still to do (M6):** its Lean appendix gains a `\leanindex` (#25), and
  `check --anonymous` runs alongside the project's own anonymity check
  (#26). The supplement is unaffected.

## 17. Roadmap

| Version | Scope | Status |
|---|---|---|
| 0.1 | Splicer: scan, apply, check, `--diff`, checksums with normalisation, author-owned slots (both forms), multi-file documents, aliases, strip. Bundle schema 1. Extractor (sidecar and in-project modes) with the `lean` view (semantic macros) and the `meta` view; axioms and `sorry`; profiles with `relative` as the default. **Useful for all three projects with no notation work.** | done, untagged |
| 0.2 | Dependency cones, `stmtHash`/`sigHash`, `\leancheck`, `imprimatur accept`. Comparator and blueprint manifests. External mode with `toolchain install`. | done, untagged |
| 0.3 | `Doc` IR, notation DSL (`width`, `variant`, `flatten`), delaborator fallback, `math` and `prose` views, notation packs. | done, untagged |
| 0.4 | `rules` and `grammar` views ported from project A, premise conventions, `include`/`exclude`, theorem modifiers, rule labels, custom views, `migrate-slots`. Migrate project A, gated by the parity test (§16). | done, untagged |
| 0.5 | `\leanindex` (the `provenance` table over every key the document cites), `check --anonymous`, undefined-macro warnings, `init`, `show`, release binaries, the toolchain range documented and enforced. `lint` and `--blueprint-compat` are later (#29, #30). | M6, not started: the [v0.5.0 milestone](https://github.com/theorem-press/imprimatur/milestone/1) |

The milestones M0 to M6, named in `CHANGELOG.md` and in comments in the
code, built these versions: M0 the foundations (layout, harness, CI, spikes
S1 and S2), M1 and M2 version 0.1 (the splicer, then the extractor), M3 0.2,
M4 0.3, M5 0.4, and M6 0.5. Each was merged as a pull request (M0 to M5 as
#2 to #7). Work since is tracked as issues.

The trust features moved earlier than in revision 1. They are where the
survey found the clearest gap, and they don't depend on the notation work.

## 18. Correctness

What does it mean for imprimatur to be correct? A paper is correct with
respect to its Lean development when what it shows is what Lean proved. This
section states that as two theorems, one about the splicer and one about the
notation, with the trusted base they rest on. Theorem 1 and the splicer's
laws are proved for a model of the splicer (`splice/SpliceModel`), and
then for the splicer's own code (docs/verified-splicer.md); §18.4 says how
the rest is checked.

### 18.1 What a document claims

A document `D` is read as a list of *claims*, each tied to a key `k`, which
names a constant of the Lean environment `E` with type `T_k`:

- **Generated claims.** A block or `\leaninline` of view `v` on `k` shows
  `render_N(v, T_k)`, where `N` is the notation module.
- **Attested claims.** A `\leancheck[stmt=h]{k}` attached to hand-written prose
  records that a person checked the prose against the statement whose hash is
  `h`. Prose has no formal meaning; it is only attested.

The meaning `⟦D⟧` is the set of propositions `T_k`, each asserted as proved.

### 18.2 Theorem 1: what `check` guarantees

**If `imprimatur check D` succeeds against `E`, then for every claim on `k`:**

1. `k` is a constant of `E`, proved with no `sorry` and with only the
   permitted axioms (§7.7);
2. for a generated claim, the text in the document is exactly
   `render_N(v, T_k)` for the current `E`;
3. for an attested claim, the statement hash of `T_k` is `h`: assuming no
   collision, the statement has not changed since the prose was checked.

It rests on the splicer's laws, which are statements about pure functions on
strings and so can be proved in Lean, where the splicer is written:

- **locality:** `apply` changes nothing outside generated regions and `sum=`;
- **idempotence:** `apply(apply(d, b), b) = apply(d, b)`;
- **fixed point:** `check(apply(d, b), b)` reports nothing stale;
- **slot preservation:** slot text survives regeneration.

They are proved in Lean for a model of the splicer, in which a document is
already parsed into pieces (`splice/SpliceModel`, presented in
`about/imprimatur-paper.tex`, a paper built and checked with imprimatur),
and for the splicer's own code, the functions the binary runs
(docs/verified-splicer.md): its scanner is lossless
(`Splice.Core.Scan.print_scan`); an ordinary slot merge is the model's
`fill` (`Splice.Core.Slots.mergeBody_keeps`); `apply` changes nothing
outside items, and within an item only its options and its region
(`SpliceModel.Splicer.planOnce_text`, `planOnce_local`) and reaches a fixed
point, which it checks of its own output before writing
(`SpliceModel.Splicer.plan_fixed_point`); and Theorem 1 holds of
`Splice.checkDoc`, which is what `check` reports
(`SpliceModel.Theorem1.checkDoc_block`, `checkDoc_ref`, `checkDoc_check`,
`checkDoc_stmt`, `checkDoc_leanok`).
They depend on Lean's standard axioms only (`lint/axioms`), and the verified
code may not use what a proof can't see into (`lint/verified`). The property
tests (docs/TESTING.md, Properties) and the differential tests remain.

### 18.3 Theorem 2: rendering is faithful

Theorem 1 says the text is the *rendering* of `T_k`. Theorem 2 says a reader
recovers `T_k` from it. This is Pollack's question of believing a
machine-checked proof (Pollack 1998), and Wiedijk's *Pollack-consistency*:
printing a term and parsing it back gives the same term (Wiedijk 2012).

The notation module `N` defines both directions. Printing is `render_N`.
Reading is a grammar `G_N`, many-sorted by Lean type: each `latex_notation`
rule is a mixfix production whose template tokens are terminals, whose holes
are nonterminals of their variables' sorts, and whose `prec` and `assoc` give
grouping (Danielsson and Norell's mixfix operators).

**For every expression `e` in the fragment of `N`, `G_N` parses
`render_N(e)` uniquely, and the parse is `e` up to `≈_N`.**

`≈_N` erases exactly what `N` declares invisible, and nothing else:

- implicit and instance arguments, and arguments a rule `hide`s;
- proofs, and a λ that binds one (the branches of a dependent `if`);
- premises a convention hides: `latex_hide_premise` premises are erased;
  `latex_metavar_convention P v` premises are restored from the reading
  "the metavariable stands for a `v` with `P v`";
- the names of hypotheses, and the choice of bound names (α-equivalence),
  including `_` for a variable nothing uses;
- the association of a `flatten` chain, which the rule declares associative;
- synonyms: a rule that writes a constant as what it equals, by definition
  or by a lemma (the `core` pack writes `Nat.succ n` as `n + 1`, as Lean
  does; a module may mark its own rules `synonym`);
- application, however it is written (`f\,a`, `f(a)`, `f_{a}`, and `⇑f a`
  through the coercion to a function), with `f(a)(b)` read as `f` applied
  to `a` and `b`.

The views extend it: the `prose` view's sentences have a fixed reading
(*Let x ∈ X. Assume P. Then Q.* is `∀ x : X, P → Q`); a `rules` figure reads
as the constructors it shows, so a figure without `include`/`exclude` *is*
the inductive definition; a `grammar` reads as the inductive type's
constructors; the `def` view reads as the equation lemmas.

**Side conditions on `N`,** checkable on `N` itself:

1. **distinct readings:** two rules whose templates coincide apply at
   different sorts (`(a\ b) \cdot e` for terms and for contexts);
2. **separated holes:** holes are separated by tokens or enclosed in braces;
   a template that is a bare hole (`Tm.var x => #x`) is a coercion between
   sorts; a chain of hidden coercions never stacks two with the same
   argument sort, and the renderer shows a coercion it may not hide there,
   so a cycle of them is harmless;
3. **consistent precedence:** the precedences and associativities make
   `G_N` unambiguous; this is where `(a b)·e₁ e₂` failed;
4. **injective names:** metavariable renamings (`latex_metavar`, including
   `decorated` ones) are injective on the names in a statement;
5. **categories keep their letters:** a grammar category's metavariable
   (`latex_category T => "e"`) stands for `T` wherever it appears, as in BNF,
   where `e ::= e₁\;e₂` says the arguments are expressions. A variable of
   another type must not print as it, with or without subscripts and primes.
   A letter may stand for several types, as a paper's programs and a
   development's representation of them, declared by one `latex_category`
   each; types are compared after unfolding reducible definitions.

**Source and glyphs.** The theorem is about TeX source. A reader sees
glyphs, and two tokens can print alike: `\;` (application) prints as space,
and in `examples/semantics` `\val` prints as `v`. A glyph-level reading needs
one more condition: macros that print alike are reserved for one sort (`v`
stands only for values). It is not checked yet (#43).

### 18.4 Checking it

The extractor is meta-programming and will not be verified. Instead:

- **the splicer's laws** and Theorem 1 are proved in Lean for a model of the
  splicer (`splice/SpliceModel`); the splicer's scanner and edits are property-tested;
- **Theorem 2 by translation validation** (`Imprimatur.Validate`), below;
- **the `Doc` emitter's parenthesisation**, a few dozen lines, is
  unit-tested (`extract/doc/*`), not proved. Its errors are caught formula
  by formula, as misreads (below).

The validator itself is proved (below, "The proved part"; #22): the parser
that reads formulas back is sound and complete, and the matching of
readings is structural. #50 is for a proof of the emitter.

**Translation validation.** The extractor reads back every formula a view
renders, as it renders it, and records what it finds in the bundle
(`validation`, per view). `imprimatur check` reports each problem in a
typeset block as a warning, `unfaithful-rendering`, where the block is.

- **The grammar** is `G_N` over TeX tokens: a production for each rule, with
  its holes at the precedences the emitter gives them; the built-in forms
  (`∀`, `∃`, `→`, `λ`, application, and, under the styles that write them,
  `f(a)` or `f_{a}`, `case`, and list literals); the emitter's parentheses;
  and the formula's own atoms (variables, literals, constants without
  notation, Lean's fallback text).
- **Sorts** are Lean types: a head constant with its type arguments
  (`Option(Label)`), `Prop`, a function sort `(A → B)`, a type parameter of
  the statement, or unknown. A named type found where a function is expected
  is accepted, since it may be one by definition (`Matrix R C α`). A hole of a
  type the pattern leaves open (`a ⊔ b` for any `a b : α`) is a type
  variable, bound by what fills the first such hole, so `a = b = c` does not
  read as comparing a proposition with a label. A rule elaborated with a
  defaulted universe applies at any sort, unless its head has no universe
  to default (`Fin n` is a type). A universe that may be `Prop` is `Sort*`:
  it takes a type or a proposition, but not a value of a datatype, so the
  type `[n]` is not read as a one-element list. A proposition is read where
  a type is expected, but not the other way round.
- **Readings** are trees named by the shapes of the rules' patterns, so
  rules for the same expressions (a variant's and a pack's) give the same
  reading. Coercions, chain association and synonyms are invisible (`≈_N`),
  and a constant applied is one reading however the rules write it.
  A coercion is read as a production that adds nothing to the reading, and
  gives it the coercion's sort, with its argument's bound (`inl x` for
  `x : A` is of sort `Sum(A, *)`); a reading can therefore be of several
  sorts, and a hole's binding chooses among them.
- **One reading** must be the original expression. As it renders, the
  renderer builds the reading it expects (`Render.Expect`): an atom reads as
  its TeX, a rule as its pattern's shape with its holes' readings, and an
  application, `∃`, `λ` or implication as the built-in form. A form it does
  not say how to read (`∀` with its binders, `match`, chains, folded
  binders, synonyms, Lean's fallback text) is `⁇`, which matches any
  subterm. A reading that does not match is a *misread*, reported with both:
  the emitter left out parentheses a reader needs, or the grammar does not
  mirror the renderer. **Two** is an ambiguity, reported with both readings.
  **None** means the grammar does not model what the renderer did, and the
  formula is *not validated*; that is a gap in the validator, or a rendering
  no reader could parse.
- **The proved part.** The chart parser that counts at most two readings
  is one total module, `Imprimatur.ReadBack`, proved sound and complete
  for any algebra of sorts (docs/verified-validator.md,
  docs/pollack-consistency.md): every reading it returns is a reading in
  the grammar (`SpliceModel.readBack_sound`), and every reading in the
  grammar is among those it returns unless it set a flag
  (`readBack_complete`). The flags: `over` (the budget or the fuel ran
  out), `pruned` (a third reading of a question, or a variant past the cap
  of 256, dropped), `cut` (a question asked again while being asked, which
  only a production whose body is a bare hole brings about), `lists` (a
  list of the grammar takes no token per element); each is reported as
  "not validated". A question is the sort, precedence, excluded
  production, the argument sorts of the coercions above it on its chain of
  coercions, and the span; a chain applies no coercion whose argument sort
  is on it already, and no cast below a cast, so chains are finite without
  a cut. The rule mentions the chain's coercions alone, never the sort
  asked for, so the renderer obeys it: where it would hide a coercion the
  rule does not allow, it shows it, as a constant applied
  (`\LeanMathConst{Option.some}\,x`). So the grammar holds every
  rendering, and the theorems are about the renderer's grammar, not a
  narrowing of it (docs/coercion-chains.md, route A). The matcher decides structural matching, so a validated formula
  (one reading, no flag, matching the expected reading) has in the grammar
  no reading but the expected one, wherever that is definite
  (`SpliceModel.pollack`); for the world as the validator sees it, whose
  `Reads` is that it accepts each formula printed of a statement, the two
  reading-back assumptions of a sound anatomy (§18.2's `Anatomy.Sound`)
  are theorems (`Validated.sound`), and so each formula of a block that
  checks clean reads only as the part it was printed from
  (`document_pollack`). Trusted still: where the expected reading has a
  `⁇`, that `Validate.ofRule` follows `Render.fillTemplate`; the
  precedence each hole needs is one function they share, `Doc.holeNeeds`
  in the module `Imprimatur.Layout`, so that part holds by construction.
  On
  project B's standalone document, 610 of the 662 formulas with one reading
  have an expected reading without `⁇`, 21 have one in part, and 31 have
  none (#41 would close the gap). Making the emitter drop the parentheses its holes need is caught
  as 6 misreads there (`(\lambda r\, q.\, …) = M` read as
  `\lambda r\, q.\, (… = M)`).
- **Side conditions** are found per formula: ambiguity (conditions 1–3),
  variables that print alike (4), and variables that print as another
  type's category letter (5). One is checked when the notation module is
  elaborated: a pattern variable that the template neither
  shows nor constrains (`hide`, `when`) is a warning, since two expressions
  that differ there render alike. `validate = false` in `imprimatur.toml`
  turns the reading back off. A setting that makes these problems errors
  is #40.

Reading back project A's main paper adds about a second to a 50-second
extraction. It reads every formula, and finds 70 ambiguities (about 200
before reading back was typed), all puns of its notation: two constants
written alike, and coercions both ways between two sorts of expression,
which side condition 2 excludes.

### 18.5 The trusted base

The Lean kernel and compiler; the extractor's reading of the environment,
which gathers what a view says (binders, `isProp`, notation matching,
`inferType`) and builds the reading it expects of a formula
(docs/verified-extractor.md and docs/verified-validator.md say what is
proved instead: the prose and rules layouts, the emitter's parentheses and
the holes' precedences are the shared module `Imprimatur.Layout`, the
parser that reads formulas back is the shared module `Imprimatur.ReadBack`,
and the paper's theorems are about them; that the grammar holds every
rendering, coercion chains included, holds by construction, the renderer
deciding with the parser's own functions, `Doc.holeNeeds` and
`Chain.allows`);
the splicer's shell, which reads files, the configuration and the
bundle and writes what `apply` returns; the scanner's reading of TeX, which
the theorems take as the specification of where markup is; collision
resistance of SHA-256; the notation module as the paper's dictionary (Lean
checks its names, not its choice of symbols); TeX, since the theorems stop
at TeX source; and, for attested claims, the person who checked the prose.

**References.** R. Pollack, "How to believe a machine-checked proof", in
*Twenty-Five Years of Constructive Type Theory*, OUP, 1998. F. Wiedijk,
"Pollack-inconsistency", *ENTCS* 285, 2012. N. A. Danielsson and U. Norell,
"Parsing mixfix operators", *IFL 2008*, LNCS 5836, 2011.

## 19. Open questions

1. **Name availability.** In October 2026, a GitHub search found no Lean or
   LaTeX project called "imprimatur", and the repository is now
   `theorem-press/imprimatur`. Before the first release, also check
   Reservoir, and any other registry the release binaries will be
   published to (#54).
2. **Toolchain support window.** How far back should support go? Each
   additional toolchain adds to the CI matrix and to `Compat.lean` (#33).
3. **Schematic rules.** One rule in project B, and the ⊕-merged rules elsewhere,
   are single paper rules that stand for several constructors. Should
   merging them be a built-in feature of the `rules` view, or stay a custom
   view? (#37)
4. **Where the `\leancheck` hash lives.** Inline as `[stmt=…]`, which
   coauthors can see, or in a lock file, which keeps the TeX tidier. The draft
   keeps it inline, as plectis keeps the reviewed wording next to the claim
   (#38).
5. **How far the dependency cone goes.** Following definition bodies until
   `trusted_prefixes` catches definitions that were weakened. It can also
   flag harmless refactors of definitions in the project. Should those
   refactors produce a separate, softer kind of drift? (#39)
**Resolved.**

- **Whether external mode works in practice.** Spike S1 showed it working
  on v4.28.0-rc1, v4.31.0 and v4.34.1 against the three motivating projects,
  and since M5 project A's three documents and project B are built in it.
  Custom views in the notation module work too: they are elaborated, not
  compiled, and run by `evalConst`.
- **Overleaf.** Splicing in place leaves ordinary `.tex` files, which
  Overleaf compiles as-is; CI runs `check`; and checksum normalisation
  (§10.2) handles the line endings introduced by the git bridge.

---

## Appendix A. Claims from the prior-art survey that still need checking

The survey was produced by an automated research tool. These claims affect
the design and should be checked against primary sources before the work
that depends on them. Those still to check are tracked in #48.

| Claim | Affects | Status |
|---|---|---|
| Since Lean 4.2x, `.olean` data has levels, and proof bodies are only in `private` | §4 (7), §7.7 | **Verified** for v4.28.0-rc1, v4.31.0, v4.34.1 and v4.35.0: `importModules (level := OLeanLevel.private)` in `Lean/Environment.lean`. Spike S1 read proof bodies from a `module` file of the math catalogue. The `ModuleSys` fixture shows the consequence (M2). Below `private`, a public theorem of a `module` file is imported as an axiom with no body. `collectAxioms` then reports the theorem itself as an axiom on v4.28, and `sorryAx` on v4.35. Only at `private` do both give the right answer |
| The math repository already uses comparator manifests with `theorem_names` and `permitted_axioms` | §10.5, §16 | **Verified** locally (`lean/ComparatorChallenges/PartitionPrinciple.json`) |
| Cog's `-c` checksum, `--check`, `--diff`, `--check-fail-msg` and `-d` behave as described | §10 | Check against the Cog 3.6 documentation |
| LeanArchitect's own pins caused a Mathlib rebuild (cameronfreer/infinitary-logic issue #26) | §4 (6) | Read the issue. The constraint stands on general grounds either way |
| `checkdecls` checks only that declarations exist | §3, §9.3 | Read the source |
| LeanArchitect detects `sorry` but doesn't check statement drift | §3 | Read the ITP 2026 paper (arXiv 2601.22554) |
| plectis and ArkLib's AxiomSweep exist and work as described | §3, §7.7 | Check the plectis paper and the ArkLib repository. These are borrowed ideas only, so nothing breaks if they are wrong |
| The HOL4 munger supports `\HOLthm` options `nosp`, `def`, `rule`, `nostile`, and display widths in override maps | §7.5, §9.1 | Check the HOL4 Description manual |
| doc-gen4 mis-renders scoped notation unless the namespaces are open | §7.2 (`open_scoped`) | Low risk; confirm when the `lean` view is prototyped |
