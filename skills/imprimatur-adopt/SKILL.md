---
name: imprimatur-adopt
description: Convert a LaTeX paper that describes a Lean development to use imprimatur for its mathematical statements, starting from a paper that does not use imprimatur yet. Use when asked to "adopt imprimatur" for a paper, to generate a paper's theorem statements from Lean, or to tie a paper's results to their Lean proofs. Finds the Lean counterpart of each statement, says how faithful it is, writes the notation and configuration, converts the statements it can, and reports the rest. After every run it records what it learned and improves itself.
---

# Adopting imprimatur in a paper

You convert a paper that already exists, and was written by hand, so that its
mathematical statements come from (or are checked against) the Lean
development they describe. The paper's authors must recognise their paper
afterwards: same numbering, labels, titles and cross-references, and no
claim the Lean does not support.

Read `LESSONS.md` in this directory first: it holds what earlier runs
learned, and it overrides anything here that it contradicts.

## Ground rules

1. **Never let the paper claim more than the Lean proves.** A statement is
   generated from Lean, or checked against it, only if the Lean declaration
   says the same thing. Every other case is reported, not hidden.
2. **Never overwrite the authors' files.** Work on a copy (Phase 0); the
   authors adopt the result.
3. **Evidence for every match:** the Lean name, its file and line, and why it
   says what the paper says. "No counterpart" is a valid finding.
4. **Keep the paper's shape.** Statements stay in the paper's own theorem
   environments, with their numbers, titles and labels, so `\ref`/`\cref`
   still work.
5. **Ask before anything outward-facing** (commits, pushes, PRs) in the
   authors' repository.

## Phase 0: set up

- Find the paper's main file and the Lean project. Check the Lean project
  builds (`lake build` of the relevant modules), and note its toolchain
  (`lean-toolchain`).
- Copy the paper's source to a working directory beside it (for example
  `build/` to `build-imprimatur/`). Typeset the original once as the
  **baseline**: page count, and the `\newlabel` lines of its `.aux` (the
  numbering).
- `imprimatur toolchain install VERSION` for the Lean project's toolchain.

## Phase 1: inventory both sides

```sh
python3 scripts/paper_statements.py MAIN.tex > statements.txt    # or --json
python3 scripts/lean_index.py LEAN_DIR... > index.jsonl
```

`paper_statements.py` lists every theorem-like environment with the number
LaTeX gives it. `lean_index.py` lists every declaration with its full name,
docstring and signature. Restrict the Lean side to the part of the
development the paper is about, but keep enough to find helpers.

## Phase 1b: triage (minutes, before Phase 2)

Before matching every statement, check three signals:

1. **Does the Lean cite the paper?** Theorem numbers, titles or labels in
   docstrings or names (`grep -i` the index for "Theorem", the paper's
   titles, its labels).
2. **Does the main theorem match?** Find the Lean's headline theorem and
   classify the paper's main theorems against it now (Phase 2's rules).
3. **Is the paper's proof in the Lean?** Grep the index for the key objects
   the paper's proof is built from: the terms of its section titles and of its
   definitions.

If the Lean cites the paper and its key objects occur, it formalises the
paper's proof: go on to Phase 2 for every statement. If the main theorem
differs and the key terms are absent, the Lean is an **independent
formalisation**: classify the main results, report that, and ask the user
before matching the rest, which is costly and will find little.

## Phase 2: correspondence

For each statement, find its Lean counterpart and classify it:

| Class | Meaning | What the paper gets |
|---|---|---|
| **exact** | same hypotheses and conclusion, up to notation | generated statement |
| **stronger** | Lean assumes less or proves more | generated statement, or the paper's text checked with `\leancheck`; note it |
| **weaker** | Lean assumes more, or proves less | the paper's text stays; a generated "Lean statement" follows it, and the gap is reported |
| **partial** | Lean proves some parts | as weaker, per part |
| **different** | Lean proves a related but different statement | report only |
| **absent** | nothing found | report only |

What is **not** exact (each was over-claimed in an earlier run):

- the paper's property proved of the Lean's own construction (its model, its
  sets) rather than of the paper's object: **different**;
- "for some generic (or model)" where the paper says "for every": **weaker**;
- transitive models where the paper allows any countable model: **weaker**.

Look also for what the Lean proves and the headline theorem does not state:
a destructured result discarded in the main proof (`_reflection`), or a
conjunct proved inside. Report these as conclusions the Lean authors could
export.

How to search, best first:

1. The main theorems first: the paper's introduction states them, and the
   Lean usually has a final theorem whose name says so. Classify these
   carefully; they matter most.
2. Names and docstrings in `index.jsonl` (`grep -i` for the paper's terms
   and their Lean spellings).
3. Signatures: the Lean types of the paper's objects (find the structure
   that is the paper's "symmetric model", then the theorems about it).
4. Proof structure: what the main theorem's proof calls, recursively. A
   paper lemma used by the main proof often appears there.

Read the whole Lean statement before classifying: every hypothesis, every
conjunct. Compare hypothesis by hypothesis. Typical gaps: an extra
large-cardinal or countability hypothesis, a model-theoretic version where
the paper states consistency, conclusions the paper states and the Lean
does not.

With many statements, split them among subagents by section, each with the
statement texts, the path of `index.jsonl`, and the class definitions above
(including what is not exact), asking for candidates with evidence and a
class. Before acting on a subagent's exact, stronger or weaker verdict, read
the Lean statement yourself: subagents over-claim.

Write the result to `CORRESPONDENCE.md` in the working directory: one row
per statement (number, label, class, Lean name, file:line, evidence, gap).

## Phase 3: configuration and notation

- `imprimatur.toml` in the working directory: `mode = "external"`,
  `lean_project` (relative), `imports` (the modules of the matched
  declarations), `notation = ["imprimatur/PaperTeX.lean"]`,
  `strip_namespaces`, and an alias for a generated statement inside the
  paper's own environment:
  ```toml
  [aliases]
  leanstatement = { view = "prose" }
  ```
- A notation module, `imprimatur/PaperTeX.lean`, written for the paper:
  - if the repository already has an imprimatur notation module (for a
    catalogue or another paper), start from it;
  - use the paper's macros (`\newcommand`s in its preamble): map each Lean
    constant of a matched statement to the paper's own notation, and rename
    the Lean's variables to the paper's letters (`latex_metavar M => "V"`);
  - metavariables (`latex_category`) for the paper's letters: the model
    `N`, the ground model `M`, sets `X, Y`;
  - `imprimatur show KEY` after each change, until the statement reads as the
    paper writes it and validation reports nothing;
  - prefer fewer, faithful rules to a rendering that misleads.

## Phase 4: convert

For each statement, by its class:

- **exact, stronger:** replace the statement's text, inside its environment,
  by a generated block, keeping the environment, title and label:
  ```latex
  \begin{theorem}[Title]\label{thm:x}
  \begin{leanstatement}{Lean.name}{}
  \end{leanstatement}
  \end{theorem}
  ```
  If the generated statement reads clearly worse than the paper's, keep the
  paper's text and add `\leancheck{Lean.name}` instead; say so in the
  report.
- **weaker, partial:** keep the paper's text. After the environment, add a
  heading the reader sees ("Lean statement"), a sentence naming the gap, and
  the generated Lean statement, set off from the prose that follows:
  ```latex
  \paragraph{Lean statement.} The Lean development proves
  Theorem~\ref{thm:x} only in the weaker form below: it assumes …
  \begin{leanstatement}{Lean.name}{}
  \end{leanstatement}
  ```
  with `leanstatement = { view = "prose", wrap = "quote" }` and
  `\leanblockalias{leanstatement}{quote}`. Leave the title empty (`{}`): it is
  passed to the wrapping environment, and `quote` would print it. Do not
  `\leancheck` it: that would certify a claim the Lean does not prove.
- **different, absent:** leave the text alone; they go in the report.

The paper must still typeset: the `\usepackage{imprimatur}` line (copy
`tex/imprimatur.sty` into the working directory), and the aliases with
`\leanblockalias`.

## Phase 5: build and check

```sh
imprimatur build
imprimatur check
latexmk -pdf MAIN.tex
```

- `check` must report no errors. Work through its warnings
  (`unfaithful-rendering`: fix the notation; `undefined-macro`: define it or
  list it in `known_macros`).
- Compare with the baseline: the same numbering (every `\newlabel` of the
  baseline, with the same number), no undefined references, and a page count
  that moved only by what was added.

## Phase 6: report

To the user, and as `REPORT.md` in the working directory:

- counts by class, and the statements converted;
- **every discrepancy**, weaker and partial first, with the Lean statement
  beside the paper's;
- what stays hand-written, and why;
- how to adopt the copy (a diff against the original).

## Phase 7: reflect and improve (every run)

This skill improves itself. After every run, before you finish:

1. **Record the run** at the top of `LESSONS.md`: date, paper, sizes
   (statements, declarations), outcome by class, time spent per phase, and
   what was hard.
2. **Extract lessons.** For each thing that cost time or went wrong, ask
   whether it would recur. If it would, write it as an instruction (what to
   do, when, and why) under "Lessons" in `LESSONS.md`.
3. **Improve the skill.** If a lesson changes how a phase should be done,
   edit that phase of this file, or a script, directly. Keep each edit
   small, say in `LESSONS.md` what changed and why, and never weaken the
   ground rules.
4. **Show the user** the changes to this directory, and ask whether to
   propose them to imprimatur (a pull request, signed off).

This version is tuned for a first adoption, a paper that uses no imprimatur
yet. Routine maintenance of a paper that already uses it is
`imprimatur build` and `check`, and needs no skill.
