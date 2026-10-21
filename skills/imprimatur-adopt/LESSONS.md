# Lessons from running imprimatur-adopt

The skill reads this file first. Newest runs first. Each lesson is an
instruction: what to do, when, and why. Lessons that changed SKILL.md say so.

## Lessons

1. **Triage before matching statement by statement.** (Phase 1b in SKILL.md
   since run 1.) Before matching every statement, spend a few minutes on three
   signals: does the Lean cite the paper (theorem numbers or titles in
   docstrings or names)? Does the main theorem match? Do the paper's key
   terms (the objects its proof is built from) occur in the Lean's names? If
   the main theorem differs and the key terms are absent, the Lean is an
   independent formalisation: classify the main results only, report that,
   and match the rest only if the user asks. *Why:* in run 1, four agents
   spent about 400k tokens to find no exact match among 35 statements, which
   these signals predicted in minutes (0 docstrings, 0 hits for "monoid",
   "diagram", "probe", and a known gap in the main theorem).
2. **The same property of a different object is "different", not "exact".**
   (SKILL.md Phase 2 since run 1.) A Lean theorem that proves the paper's
   property of the Lean's own construction (its model N, its row set) does not
   prove the paper's statement about the paper's object (W, A). *Why:*
   subagents classified Props 3.7 and 3.8 as exact on these grounds.
3. **Check the direction of quantifiers over generics and models.** "For some
   generic below each condition" is weaker than "for every generic"; "for
   transitive models" is weaker than "for every countable model". *Why:*
   Prop 3.9 was reported exact but holds only for some generic.
4. **Look for results the headline proof discards.** A destructuring pattern
   such as `_reflection` in the main proof, or a conjunct proved inside and
   not stated, shows what the Lean proves beyond its headline theorem: report
   it as something the Lean authors could export. *Why:* run 1 found two of
   Theorem 1.2's missing conclusions this way.
5. **Set a generated statement off from the prose,** with an alias that wraps
   it (`wrap = "quote"`, `\leanblockalias{leanstatement}{quote}`), and give
   such blocks an empty title (`{key}{}`): the title is passed to the wrapping
   environment as an optional argument, and `quote` prints it. (SKILL.md
   Phase 4 since run 1.)
6. **Reuse the repository's notation.** If the repository already has an
   imprimatur notation module (for a catalogue or another paper), start from
   it and switch it to the paper's macros. *Why:* run 1 had a working module
   for the main theorem in `imprimatur/PartitionTeX.lean`.
7. **Subagents report confidently; verify before acting.** Read the Lean
   statement of every match a subagent calls exact, stronger or weaker
   before converting it. *Why:* three of run 1's "exact" verdicts were wrong.

## Runs

### Run 1, 2026-10-21: *The Partition Principle does not imply Choice*

- **Paper:** 44 pages, 35 statements (6 theorems, 23 lemmas, 4 propositions,
  2 remarks), 3,366 lines of TeX.
- **Lean:** `lean/OAI/SetTheory/PartitionPrinciple/`, 943 files, 12,408
  declarations, no docstrings; toolchain v4.34.1, external mode.
- **Outcome:** 0 exact or stronger, 3 weaker, 6 partial, 10 different, 16
  absent. The Lean is an independent formalisation, by another route, of a
  weaker form of Theorem 1.2 (it needs an inaccessible; it omits two
  conclusions, proved inside and not stated). One change to the paper: the
  generated Lean statement after Theorem 1.2, with its gaps named. `check`
  clean; 44 pages and all 190 labels unchanged.
- **Cost:** Phase 2 dominated: four parallel subagents, about 400k tokens,
  three minutes each. Phases 3–6 took a few minutes, reusing the
  repository's notation.
- **What was hard:** knowing early that per-statement matching would find
  nothing (lesson 1); subagents over-claiming exact matches (lessons 2, 3,
  7); a title printed by `quote` (lesson 5).
- **Skill changes:** Phase 1b (triage) added; Phase 2's classes say what is
  not exact; Phase 4 wraps generated statements that follow a weaker
  statement in `quote` with an empty title.
