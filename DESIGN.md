# imprimatur — design

*Status: draft design. Revision 2 (2026-10-17) takes in a survey of prior art
(§3). Revision 3 (2026-10-17) takes in spikes S1 (external mode) and S2
(stable hashing), under [docs/spikes/](docs/spikes/).*

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

- Running code blocks or capturing program output (a separate concern; see
  project-a's `old_tool`).
- Producing whole documents (as doc-gen4, Verso or Isabelle's document
  preparation do). imprimatur fills holes in documents that humans write in
  ordinary LaTeX.
- Planning a formalisation or drawing dependency graphs (leanblueprint and
  LeanArchitect do this; §3).
- Typesetting proofs.

## 2. Motivating projects

The design was checked against three projects with different needs.

| | project-a (PL paper) | math catalogue | project B (PL paper) |
|---|---|---|---|
| Lean toolchain | v4.28.0-rc1 | v4.34.1 (uses the module system) | v4.31.0 |
| Depends on Mathlib | yes | yes, plus about 15 other libraries | yes |
| Lean project location | `proj/` | `lean/` | `lean/` |
| TeX layout | one large `paper.tex` | one large `overview.tex` | about 20 files joined with `\input` |
| What it needs | inference rules, grammars, theorems and definitions as typeset maths; a provenance index | the statements of the main theorems inside catalogue entries | rules generated from the `Der` inductive; hand-written theorem prose checked against `MyPaper/Results.lean`; an appendix index |
| Existing metadata | hard-coded export lists | `formalization.yaml`, plus a comparator manifest per result in `ComparatorChallenges/*.json` | `MyPaper/Results.lean` restates every numbered result |
| Constraints | already has a hard-wired version of this tool to replace | proof sources must not be edited | anonymous submission; the Lean project is shipped as the supplement and must not change |

project-a's existing implementation (`OldRules.lean`, `OldGrammar.lean`,
`OldConventions.lean`, `OldTranslation.lean`, and the splicing half of
`OldTool.lean`, about 4,000 lines) is the starting point. Its rendering ideas
carry over. Its hard-wired parts do not: rule symbols are chosen by
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
   renamed constant must fail loudly at build time. With project-a's string
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
   passes it explicitly, through `Compat/` (§13).

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
main = "project-b-paper.tex"            # entry point; \input/\include are followed
lean_project = "lean"
mode = "external"                         # external | sidecar | in-project (§6.3)
imports = ["MyPaper.Results"]                # modules to read declarations from
notation = ["tex/PaperTeX.lean"]          # notation modules
strip_namespaces = ["ProjB", "MyPaper.Results"]
open_scoped = []                          # e.g. ["Topology", "BigOperators"], for the lean view
notation_packs = ["core", "logic"]        # §7.5
verbatim_envs = []                        # extra environments the scanner skips (§10.1)
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
import MyPaper.Results
import Imprimatur

open ProjB ProjB.Structural

latex_notation Des.leaf _ _ _ spec          => "L"
latex_notation Ctx.lookup spec i = true    => r"\cbX \in L(#i)"
latex_notation Judg.time i                  => r"\judge{time}(#i)"
latex_notation Tm.app A B                 => r"\app{#A}{#B}"   width := 5

latex_group "Analysis rules" :=
  [Der.t_cb, Der.t_max, Der.ord, Der.m_ord, Der.w_nr, Der.m_cb, Der.i_cb,
   Der.i_ord, Der.t_int, ProjB.Factors.DerF.m_mf, ProjB.Factors.DerF.i_mf,
   Der.i_nest, Der.w_nest, Der.i_cross_l]

latex_entry "Soundness" => MyPaper.Results.theorem1_main  options := "forall"
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
name = "projb-lean"
path = "../lean"
[[require]]
name = "imprimatur"
git = "https://github.com/theorem-press/imprimatur"
rev = "v0.3.0"
subDir = "extract"
[[lean_lib]]
name = "PaperTeX"
```

- `imprimatur init --sidecar` creates it, copies the host's toolchain, and pins
  shared dependencies to the host's manifest.
- It costs one extra checkout of the dependencies; for Mathlib, use
  `lake exe cache get`.
- Use it when the notation module needs Lake features: it spans several
  files, or it defines custom views that must be compiled.

**C. Inside the project.** The host adds `require imprimatur … subDir =
"extract"` and a library for the notation module.

- Because imprimatur has no dependencies, this cannot disturb Mathlib's pins
  (constraint 6).
- It is the simplest mode when you own the project and its lakefile is not
  an artifact in its own right. project-a fits this case.

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
generic `grammar` view, as are project-a's theorem prose and provenance index
(§16).

### 7.4 Rule labels

The label of a `rules` entry is chosen in this order:

1. an explicit `latex_rule_label Der.t_cb "T-CB"`;
2. otherwise, a docstring that starts `Label: …` or `Label.` supplies
   `Label`, following the `/-- T-CB: … -/` convention project B already uses;
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
latex_notation (variant := "named") Tm.app A B => r"\kw{nest}\;#A\;#B"
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
  parenthesises both operands at the rule's own precedence, as project-a does
  for `∧` next to `∨`.
- **`latex_style`** fixes conventions of the renderer for the whole paper:
  `names := raw` writes binder names as they are (they are TeX: `l_c`),
  rather than escaped and in `\mathit`; `applied_variables := call` writes
  an applied variable as `f(a)(b)`. Greek binder names are always macros
  (`\varepsilon`).
- **Order of lookup.**
  1. The project's rules. The most specific pattern wins, and declaration
     order breaks ties.
  2. Notation packs shipped with imprimatur (`core`, `logic`, `sets`, `order`,
     `mathlib-common`). A pack is selected in `imprimatur.toml`, and its rules
     are stored as names, so imprimatur still doesn't depend on Mathlib.
  3. The delaborator fallback (§7.2).
- **Metavariables.** A trailing digit or a Unicode subscript becomes a LaTeX
  subscript. `latex_metavar` renames a binder, for example rendering
  `spec` as `L`.
- **Macros come from the paper.** The bundle records the macros each
  rendering uses (§8), so the splicer can warn about macros that are not
  defined anywhere in the document.

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

Instance binders are always hidden. Each block can override these choices
with `show=` and `hide=` options.

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
  - The bundle records each untrusted member with its reasons (`sorry`,
    `axiom`, `partial`, `unsafe`). The splicer then accepts axioms that
    `allowed_axioms` (or a manifest's `permitted_axioms`) lists. Each constant in the cone is itself checked for `sorry`,
  for disallowed axioms, and for `unsafe` or `partial`.
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

```json
{
  "schema": "imprimatur-bundle/1",
  "producer": { "tool": "imprimatur-export", "version": "0.3.0",
                "lean": "v4.31.0", "project": "projb-lean" },
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
\leanindex                                            % table of every key used in the document
```

The options of `leanblock`:

- **`view`**, **`wrap`** (an environment to put the content in, such as
  `theorem`) and **`label`**;
- **`sum`**, the checksum of the generated content (§10.2);
- **`notation`**, which selects a notation variant (§7.5);
- **`include`** and **`exclude`**, which select constructors for a `rules` or
  `grammar` view, as PLT Redex does. With them, one inductive can be
  presented a few rules at a time across sections;
- **`show`** and **`hide`**, which override premise conventions (§7.6);
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
- **`\leanindex`** replaces project-a's provenance table, and it is how project B's
  Lean appendix lists every result.

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
- **Writing blueprint markers.** `imprimatur build --blueprint-compat` also
  writes `\lean{…}` inside generated blocks, so a paper can feed a blueprint
  dependency graph.

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
  example the constructor's docstring. After that, the text belongs to the
  authors.
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
  the text of its first argument. This is exactly what project-a's splicer does
  today (`mergeDescriptions`). Identifying a slot by formal text is
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
  `\NAMEfalse`, as project-a turns appendices off), nor those in a file reached
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
  - Together with slots, this replaces project-a's special-case rules for
    preserving last-good output and merging paper-side edits.
- **Keeps slot text.** When it regenerates a block, `apply` copies each
  slot's existing text into the new content, matched by slot id (§9.5).
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
- **undefined macros**: macros used by generated content that no scanned
  file defines. This one is only a warning;
- **orphaned slots**: slot text whose slot no longer exists in the
  regenerated block (§9.5). Also only a warning.

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
- `check --anonymous` scans everything generated for strings like `/home/`,
  `@` or `github.com`;
- external mode (§6.3 A) leaves no trace of imprimatur in the host project.

Unlike leanblueprint and doc-gen4, nothing in the output templates contains a
repository URL.

## 12. Commands

| Command | What it does |
|---|---|
| `imprimatur toolchain install <ver>` | build the extractor for a toolchain (external mode) |
| `imprimatur init [--sidecar]` | create `imprimatur.toml`, and the sidecar package if asked |
| `imprimatur build [--profile p] [--blueprint-compat]` | scan, then export, then apply |
| `imprimatur check [--profile p] [--anonymous] [--diff]` | the checks in §10.3 |
| `imprimatur accept <key>…` | record the current statement hash in `\leancheck` |
| `imprimatur strip [-o dir]` | write a copy with the markers removed |
| `imprimatur migrate-slots` | rewrite slots declared by position into `\leanslot` form (§9.5) |
| `imprimatur show <key> [--view v]` | print one rendering, for working on notation |
| `imprimatur lint` | report binder names that differ from the paper's naming convention (generalised from project-a's `binder_lint`) |
| `imprimatur-splice scan\|apply\|check\|strip` | the splicer on its own |
| `imprimatur-export --requests r.json --out b.json` | the extractor on its own |

A typical `Makefile` addition:

```make
all: imprimatur
	latexmk -pdf $(PAPER)
imprimatur:
	imprimatur build
```

## 13. Toolchain compatibility and versioning

- **Supported range.** Each extractor release states the range of toolchains
  it supports (at the time of writing, v4.28 to v4.34). CI builds and runs the
  golden tests on every toolchain in the range.
- **Where version differences live.** Differences between Lean versions are
  confined to `Imprimatur/Compat/`. They include:
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

- **Golden tests for the extractor.** For each view, a fixture project with
  known output, run for every supported toolchain. The fixture includes a
  project that uses the module system.
- **Golden tests for the splicer.** Pairs of TeX files before and after
  `apply`, including:
  - nested `\input`;
  - blocks inside macro arguments;
  - hand-edit protection;
  - slots: edited slot text survives regeneration; a slot whose formal part
    changes keeps its text when identified by `\leanslot` id; orphans are
    reported; slots declared by position match project-a's current behaviour;
  - CRLF line endings and trailing whitespace;
  - Unicode;
  - blueprint `\lean{}`.
- **Trust tests.** A fixture whose theorem has a hypothesis definition
  silently changed to `True`, which must fail `check`. Also fixtures with
  `sorry` deep in the cone, and with a disallowed axiom.
- **Property tests.** `apply` is idempotent; `scan` followed by `apply` on a
  generated document changes nothing; `strip` followed by compiling gives the
  same PDF.
- **End-to-end.** `examples/` builds a small paper and its PDF in CI, in all
  three modes.

## 15. Repository layout

```
imprimatur/
  README.md  DESIGN.md  CHANGELOG.md  LICENSE
  extract/                        Lake package "imprimatur" (no dependencies)
    lakefile.toml  lean-toolchain
    Imprimatur.lean
    Imprimatur/Doc.lean           IR and LaTeX emitter (escaping, precedence, widths, flattening)
    Imprimatur/Render.lean        Expr → Doc; delaborator fallback; telescopes, metavariables
    Imprimatur/Notation.lean      registry, environment extension, latex_notation
    Imprimatur/Conventions.lean   latex_metavar_convention, latex_hide_premise
    Imprimatur/Entries.lean       latex_entry, latex_group, latex_rule_label
    Imprimatur/Views/             Lean.lean Meta.lean Math.lean Prose.lean Rules.lean Grammar.lean
    Imprimatur/Packs/             Core.lean Logic.lean Sets.lean Order.lean MathlibCommon.lean
    Imprimatur/Trust.lean         axioms, sorry, dependency cone, stmtHash, sigHash
    Imprimatur/Bundle.lean        JSON writer
    Imprimatur/Lint.lean
    Imprimatur/Compat/            differences between toolchains
    Main.lean                     imprimatur-export (also the external-mode runner)
    test/
  splice/                         Lake package "imprimatur-splice"
    lakefile.toml  lean-toolchain
    Splice/Text.lean  Splice/Sha256.lean  Splice/Toml.lean  Splice/Config.lean
    Splice/Bundle.lean  Splice/Diag.lean  Splice/Scan.lean  Splice/Doc.lean
    Splice/Slots.lean  Splice/Apply.lean  Splice/Check.lean  Splice/Strip.lean
    Splice/Cli.lean  Splice/Manifests.lean (M3)
    Main.lean                     imprimatur-splice, imprimatur (wrapper)
    test/
  testkit/                        test-only package: harness, golden files, seeded generator
  test/                           fixtures/ (Lean projects), tex/ (documents), bundles/
  scripts/                        test-all.sh, lint.sh, e2e.sh, integration.sh
  schema/bundle.schema.json
  tex/imprimatur.sty
  docs/  blocks.md  notation.md  views.md  trust.md  bundle.md  anonymity.md  prior-art.md
  examples/minimal/  examples/sidecar/  examples/external/  examples/blueprint/
  .github/workflows/              toolchain matrix, release binaries
```

## 16. Adoption in the three projects

**project-a** (inside the project, §6.3 C)

- `OldTool` keeps `codeblock` and `codeoutput`. Its splicing code for the
  `lean*` environments is deleted.
- `defaultTheorems` and `defaultDefinitions` become `latex_entry` lines, and
  `defaultGroups` becomes `latex_group` lines.
- The symbol choices in `ruleName` and `metavar` become notation rules and
  premise conventions. Whatever BigStep-specific rendering remains becomes an
  `@[latex_view "project-a.rules"]`.
- `OldTranslation` is replaced by `\leanindex`.
- **Hand-written grammar descriptions are kept.** The `leangrammar` alias
  declares the description arguments of `\entry`, `\defentry` and
  `\Category` as slots identified by their first argument (§9.5). This
  reproduces `mergeDescriptions` exactly. The defaults in
  `OldGrammar.lean` become constructor docstrings or `latex_entry`
  options.
- **Content specific to project-a moves into project-a.** The binder-convention
  table (`leanconventions`) and the dispatch table become custom views in
  project-a's notation module, not features of imprimatur.
- **The paper is unchanged**, thanks to the alias table. `/paper-rebuild`
  runs `old_tool` for the `codeblock` blocks, then `imprimatur build`.
- **Project A's Lean version must be supported.** It uses `v4.28.0-rc1`, a
  release candidate, so that version must be in imprimatur's supported range
  (§13).
- **A parity test gates the migration.**
  1. Build `paper-a/paper.tex` with the old `old_tool` and with
     imprimatur, from the same commit of `proj/`.
  2. Diff the results. The only allowed differences are the `sum=` options
     that imprimatur adds to each block on its first run.
  3. Only then delete the `Export*.lean` rendering code and the `lean*`
     splicing in `OldTool.lean`.

  The diff in step 2 also lists every rendering special case still to port.

**As done (M5).** The parity gate passed byte for byte on `paper-a` and
`paper-a2`, after which project-a deleted its old exporter (`OldRules.lean`,
`OldGrammar.lean`, `OldTranslation.lean` and `old_tool`'s Lean
splicing) and the gate with it. project-a keeps the port in its own repository
(`imprimatur/`, shared by its documents): notation for every arm of the old
renderer, the groups, labels and entries, and four custom views (theorem
prose, `≜` definitions, the hand-written grammar tables, and the
conventions, dispatch and provenance tables). Its three documents are built
with imprimatur in external mode, and `old_tool` keeps only the `codeblock`
blocks. The binder linter and its conventions table stay in project-a's Lean
sources, and a custom view splices the table from there. In `proj/doc` the gate found two blocks the old tool had left frozen,
stale, because their theorems were not registered: one is now generated, the
other (its theorem gone) became plain text. It also showed the old
renderer's mistakes kept for parity, such as a dropped premise, each now one
line to delete. Generic features came out of the port: binder patterns,
`latex_style`, `latex_entry`, `when` guards, decorated metavariables, alias
labels and templates, comment-delimited blocks, the scanner's reading of
`\newif` switches (so an index leaves out appendices switched off while
their blocks are kept up to date), and the document inventory, which
`\leanindex` (M6) will also use.

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

**project B** (external, `submission` profile)

- The rules figure in `analysis.tex` becomes a generated `rules` group taken
  from `Der` and `DerF`. Labels come from the existing constructor docstrings.
  Premise conventions hide the `Fintype` data.
- The schematic **Lift** rule, a single rule in the paper that stands for four
  constructors, either stays hand-written or gets a small custom view.
- Theorem and proposition prose stays hand-written, with
  `\leancheck[stmt=…]` against the `MyPaper.Results.*` restatements.
- `lean-appendix.tex` gains a `\leanindex` and `lean`-view statements.
- The supplement and `make_lean_supplement.py` are unaffected, and
  `check --anonymous` runs alongside `check-anonymity.sh`.

## 17. Roadmap

| Version | Scope |
|---|---|
| 0.1 | Splicer: scan, apply, check, `--diff`, checksums with normalisation, author-owned slots (both forms), multi-file documents, aliases, strip. Bundle schema 1. Extractor (sidecar and in-project modes) with the `lean` view (semantic macros) and the `meta` view; axioms and `sorry`; profiles with `relative` as the default. **Useful for all three projects with no notation work.** |
| 0.2 | Dependency cones, `stmtHash`/`sigHash`, `\leancheck`, `imprimatur accept`. Comparator and blueprint manifests. External mode with `toolchain install`. |
| 0.3 | `Doc` IR, notation DSL (`width`, `variant`, `flatten`), delaborator fallback, `math` and `prose` views, notation packs. |
| 0.4 | `rules` and `grammar` views ported from project-a, premise conventions, `include`/`exclude`, theorem modifiers, rule labels, custom views, `migrate-slots`. Migrate project-a, gated by the parity test (§16). |
| 0.5 | `\leanindex`, `lint`, `check --anonymous`, undefined-macro warnings, `--blueprint-compat`, release binaries, toolchain CI across the full range. |

The trust features moved earlier than in revision 1. They are where the
survey found the clearest gap, and they don't depend on the notation work.

## 18. Correctness

What does it mean for imprimatur to be correct? A paper is correct with
respect to its Lean development when what it shows is what Lean proved. This
section states that as two theorems, one about the splicer and one about the
notation, with the trusted base they rest on. Theorem 1 and the splicer's
laws are proved for a model of the splicer (`about/lean`); §18.4 says how
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
already parsed into pieces (`about/lean`, presented in
`about/imprimatur-paper.tex`, a paper built and checked with imprimatur). The
splicer itself, which works on TeX source, is property-tested against them
(PLAN §2.3).

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
- premises a convention hides: `latex_hide_premise` premises are erased;
  `latex_metavar_convention P v` premises are restored from the reading
  "the metavariable stands for a `v` with `P v`";
- the names of hypotheses, and the choice of bound names (α-equivalence);
- the association of a `flatten` chain, which the rule declares associative;
- synonyms: a rule that writes a constant as what it is by definition
  (the `core` pack writes `Nat.succ n` as `n + 1`, as Lean does).

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
   sorts, allowed when coercions form no cycle;
3. **consistent precedence:** the precedences and associativities make
   `G_N` unambiguous; this is where `(a b)·e₁ e₂` failed;
4. **injective names:** metavariable renamings (`latex_metavar`, including
   `decorated` ones) are injective on the names in a statement.

**Source and glyphs.** The theorem is about TeX source. A reader sees
glyphs, and two tokens can print alike: `\;` (application) prints as space,
and in `examples/semantics` `\val` prints as `v`. A glyph-level reading needs
one more condition: macros that print alike are reserved for one sort (`v`
stands only for values).

### 18.4 Checking it

The extractor is meta-programming and will not be verified. Instead:

- **the splicer's laws** and Theorem 1 are proved in Lean for a model of the
  splicer (`about/lean`); the splicer's scanner and edits are property-tested;
- **Theorem 2 by translation validation** (`Imprimatur.Validate`), below;
- **the `Doc` emitter's parenthesisation**, a few dozen lines, is proved
  correct with respect to precedence.

**Translation validation.** The extractor reads back every formula a view
renders, as it renders it, and records what it finds in the bundle
(`validation`, per view). `imprimatur check` reports each problem in a
typeset block as a warning, `unfaithful-rendering`, where the block is.

- **The grammar** is `G_N` over TeX tokens: a production for each rule, with
  its holes at the precedences the emitter gives them; the built-in forms
  (`∀`, `∃`, `→`, `λ`, application, and `f(a)` or `f_{a}` under the style that
  writes them); the emitter's parentheses; and the formula's own atoms
  (variables, literals, constants without notation, Lean's fallback text).
- **Sorts** are Lean types: a head constant, `Prop`, a function sort
  `(A → B)`, a type parameter of the statement, or unknown. A hole of a
  type the pattern leaves open (`a ⊔ b` for any `a b : α`) is a type
  variable, bound by what fills the first such hole, so `a = b = c` does not
  read as comparing a proposition with a label. A rule elaborated with a
  defaulted universe applies at any sort.
- **Readings** are trees named by the shapes of the rules' patterns, so
  rules for the same expressions (a variant's and a pack's) give the same
  reading. Coercions, chain association and synonyms are invisible (`≈_N`).
- **One reading** is the original expression, since the grammar mirrors the
  emitter: the renderer's output is a parse of what it rendered. **Two** is
  an ambiguity, reported with both readings. **None** means the grammar does
  not model what the renderer did, and the formula is *not validated*;
  that is a gap in the validator, or a rendering no reader could parse.
- **The trusted part** is that mirroring, `Validate.ofRule` against
  `Render.fillTemplate`, and a small chart parser that counts at most two
  readings, with a work budget.
- **Side conditions** are found per formula, except one checked when the
  notation module is elaborated: a pattern variable that the template neither
  shows nor constrains (`hide`, `when`) is a warning, since two expressions
  that differ there render alike. `validate = false` in `imprimatur.toml`
  turns the reading back off.

Reading back project-a's a conference paper adds about a second to a 50-second
extraction. It reads every formula, and finds about 200 ambiguities, all puns
of its notation: two constants written alike (`stamp` and `labeled`,
`ValS` and `ShapeVal`), and coercions both ways between `Expr` and
`ExprF`, which side condition 2 excludes.

### 18.5 The trusted base

The Lean kernel; the extractor's reading of the environment; collision
resistance of SHA-256; the notation module as the paper's dictionary (Lean
checks its names, not its choice of symbols); TeX, since the theorems stop
at TeX source; and, for attested claims, the person who checked the prose.

**References.** R. Pollack, "How to believe a machine-checked proof", in
*Twenty-Five Years of Constructive Type Theory*, OUP, 1998. F. Wiedijk,
"Pollack-inconsistency", *ENTCS* 285, 2012. N. A. Danielsson and U. Norell,
"Parsing mixfix operators", *IFL 2008*, LNCS 5836, 2011.

## 19. Open questions

1. **Name availability.** In October 2026, a GitHub search found no Lean or
   LaTeX project called "imprimatur". Before creating the repository, also
   check Reservoir, and any other registry the release binaries will be
   published to.
2. **Toolchain support window.** How far back should support go? Each
   additional toolchain adds to the CI matrix and to `Compat/`.
3. **Schematic rules.** Lift in project B, and the ⊕-merged rules elsewhere,
   are single paper rules that stand for several constructors. Should
   merging them be a built-in feature of the `rules` view, or stay a custom
   view?
4. **Where the `\leancheck` hash lives.** Inline as `[stmt=…]`, which
   coauthors can see, or in a lock file, which keeps the TeX tidier. The draft
   keeps it inline, as plectis keeps the reviewed wording next to the claim.
5. **How far the dependency cone goes.** Following definition bodies until
   `trusted_prefixes` catches definitions that were weakened. It can also
   flag harmless refactors of definitions in the project. Should those
   refactors produce a separate, softer kind of drift?
6. ~~**Whether external mode works in practice.**~~ Resolved by spike S1: it
   works on v4.28.0-rc1, v4.31.0 and v4.34.1 against the three motivating
   projects. Custom views compiled in the notation module were not tested, and
   sidecar mode remains the answer for them.

Overleaf, an open question in revision 1, is resolved. Splicing in place
leaves ordinary `.tex` files, which Overleaf compiles as-is; CI runs `check`;
and checksum normalisation (§10.2) handles the line endings introduced by the
git bridge.

---

## Appendix A. Claims from the prior-art survey that still need checking

The survey was produced by an automated research tool. These claims affect
the design and should be checked against primary sources before the work
that depends on them.

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
