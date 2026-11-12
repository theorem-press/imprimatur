# Proposal: a chart of imprimatur's run time, from CI

Status: implemented (2026-11-12, the same day as the proposal): parts 1 to 4
in `scripts/e2e.sh`, `scripts/timing-fold.py`, `scripts/timing-chart.py` and
the e2e job of `ci.yml`; the page is docs/timing.md; the about paper's
repository does the same in its `refresh.sh` and CI. Differences from the
proposal are noted where they are. Uses `--timing` (CHANGELOG 0.5, docs/blocks.md)
and the end-to-end script (`scripts/e2e.sh`, docs/TESTING.md). The harness of
the about paper (`imprimatur-paper/harness/DESIGN.md`) is the precedent for an
append-only log that a chart and a sentence are computed from.

## The question

imprimatur has been slow three times, and each time someone noticed by hand,
after the fact: the LLMbda paper took 112 s until the cone and axiom memo
brought it to 21 s (29 October); the about paper went from 40 s to 107 s
under route B's chain bound, and LLMbda under the same bound did not finish
in an hour (#87). A chart of the run time of a few papers, one point per
night, would have shown each as a step on the day it happened.

CI measures nothing of the kind today. The durations GitHub records are of
jobs and steps: the e2e job's 250 s is 100 s of installing TeX Live, a cache
restore, Lake builds, four `imprimatur build`s, eight `latexmk`s and eight
`pdftotext`s, and the same commit's jobs differ by half between runs (splice
102 s and 161 s on 89b4819, two runs apart). A regression of imprimatur's
own time, which is seconds, is invisible in that.

## What exists

- **`--timing`.** `imprimatur build --timing` (and `check`, `accept`, `show`)
  writes `.imprimatur/timing.jsonl`, one JSON object per line: the
  splicer's phases (`{"at":"splice","phase":"scan"|"export"|"apply"|"check","ms":…}`),
  the verified checker's run (`{"at":"checker","phase":"con-leche","ms":…}`),
  and the extractor's (`{"at":"extract","phase":"load"|"entries"|"write"|"extractor","ms":…}`,
  one `entry` per key, one `stage` per stage of it, one `view` per view, one
  `formula` per formula read back, with `tokens` and the parser's `steps`).
  It measures imprimatur alone: Lake's build of the development is before
  `load`, and `latexmk` is after `write`. That is the number to chart.
- **The end-to-end script** builds four examples (`external`, `minimal`,
  `semantics`, `sidecar`) in both modes and typesets each with pdflatex and
  lualatex, and in `e2e/checker` builds `semantics` once more with the
  verified checker, with `--timing`. The timing file is written and then
  ignored.
- **The nightly.** `ci.yml` runs on a schedule at 03:17 UTC with the
  10,000-case property gate, on one runner image, so one point a night is
  already there to be taken, on a runner that is the same from night to
  night until GitHub moves the image (which the log must record, since the
  12 November image changed pdftotext's output and would change times too).
- **The papers CI can reach**, in this repository: the four examples (1 to
  19 entries) and `papers/con-leche` (23 entries, the verified checker on).
  The about paper is in `imprimatur-paper`, whose own CI runs `refresh.sh`
  on every push and is where its time is measured (104 entries, 846 formulas:
  the largest paper a workflow can build). The LLMbda papers are private and
  need their Lean project built (`deep/`, v4.28.0-rc1), so they come last.

## The design

Four parts, in the order to build them. Each is useful without the next.

### 1. Measure: every build in e2e with `--timing`, folded to one line per paper

`scripts/e2e.sh` runs each imprimatur step with `--timing` (the flag writes
`.imprimatur/timing.jsonl` in the work directory, one command at a time: a
command starts the file afresh), keeps the last `build`'s and `check`'s files
as `timing-build.jsonl` and `timing-check.jsonl`, and adds `e2e/con-leche`:
`papers/con-leche` built as the examples are, with its checker, when
con-leche is checked out and built beside the repository (the nightly clones
and builds it; a pull request's run skips it). After the examples,
`scripts/timing-fold.py fold` reads every `e2e-out/*/timing-build.jsonl` and
writes `e2e-out/timing.jsonl`, one line per paper:

```json
{"date": "2026-11-12", "sha": "e6695e9", "event": "schedule",
 "image": "ubuntu-26.04/20261101.186.1", "toolchain": "v4.35.0",
 "paper": "semantics", "mode": "external", "checker": true,
 "entries": 19, "views": 14, "formulas": 78, "tokens": 1210, "steps": 48211,
 "ms": {"load": 1209, "entries": 168, "write": 1, "extractor": 1379,
        "scan": 2, "export": 1551, "apply": 22, "checker": 129, "total": 1575},
 "slowest": {"entry": ["Preservation", 41], "view": ["rules", 22],
             "formula": ["\\Gamma \\vdash e : \\tau", 3]}}
```

`total` is the splicer's wall time from `scan` to the end of `apply` or
`check`, which contains the extractor's. `entries`, `formulas`, `tokens` and
`steps` are the sizes, so a paper that grew is not read as a tool that
slowed. The image and the toolchain are the two things that change a time
without a commit. The fold is a hundred lines of Python with no
dependencies, in the style of `scripts/check-bundles.py`.

Every CI run uploads `e2e-out/timing.jsonl` as an artifact
(`timing-<sha>`), so a pull request's numbers can be looked at.

### 2. Keep: the nightly appends to an append-only log on a `timing` branch

Only the scheduled run (and `workflow_dispatch`) appends, so the log has one
point a night from one runner image and no noise from pull requests. The e2e
job, when `github.event_name` is `schedule` or `workflow_dispatch`, checks
out the orphan branch `timing` into `timing/`, appends the night's lines to
`timing/log.jsonl`, and pushes, with `permissions: contents: write` on that
job only and a `concurrency` group so two dispatches do not race. The branch
holds the log, the chart (part 3) and nothing else; it grows by about a
kilobyte a night.

An append-only file of JSON lines, folded by a script, is the harness's
shape. If the about paper should one day quote a CI number with a
`\leancheck`, the log can be folded in Lean as `harness/log.jsonl` is; that
is not proposed now.

### 3. Show: the job summary every run, and a page on the site

**The job summary.** Every e2e run writes to `$GITHUB_STEP_SUMMARY`: a table
of tonight's `total` per paper beside the median of the last ten nightly
points and the ratio, and a Mermaid `xychart-beta` line chart of `total` per
paper over the last thirty nights. GitHub renders Mermaid in summaries, so
the chart is on the run's page with nothing hosted; a pull request's run
shows its own numbers against the nightly medians, without appending.

**The site.** `docs/timing.md` (the Pages site is this repository's
Markdown; the repository is public, so it is served) shows
`timing/chart.svg`, drawn by `scripts/timing-chart.py` in the nightly after
the append and committed to the `timing` branch beside the log: one line per
paper, `total` in seconds against date, with the phases as a stacked area on
a second chart for the largest paper, since a step is in one phase (`load`
for notation elaboration, `entries` for the cone and axioms, `export` for
read-back). The page links the raw log. matplotlib under `uv`, as
`analytics/chart.py` in the about paper does.

### 4. Alarm: the nightly fails when a paper slows

After the append, the nightly compares each paper's `total` with the median
of its last ten nightly points and fails the job when it exceeds
`max(2 × median, median + 2 s)` (the proposal said 10 s, which no example
could reach), saying which paper and which phase grew,
unless `entries` or `formulas` also grew by as much (a bigger paper). The
threshold and the window live in one place at the top of
`timing-fold.py`. A failing nightly already reaches the people who watch
CI; an issue filed by the workflow is a later refinement.

### Noise, and what is done about it

Wall time on a shared runner varies. What keeps the chart readable: only
imprimatur's phases are measured (Lake and TeX are outside the interval);
the nightly uses one image, recorded per point; `steps` counts the parser's
work independent of the machine, so a slower parser shows in `steps` as well
as in `ms`; and the extractor is installed before the examples are built,
so each build runs with a warm toolchain cache, which is the state a paper's
author sees (the proposal's second build was not needed: the memo tables
are per process, and a build is what is measured). If the scatter still hides a step
of less than a factor of two, the fallback is a fixed reference build
(`minimal`) whose time divides the others.

## The about paper, and LLMbda

`imprimatur-paper`'s CI runs `refresh.sh`, which calls `imprimatur build` and
`check`; the same `--timing`, fold and append apply there, to a `timing`
branch of that repository, with the same scripts vendored by the pin. Its
chart is the one to watch for route-B-sized regressions, as it is the
paper that showed them.

The LLMbda papers need a checkout of a private repository (a deploy key) and
a Lake build of `deep/` that is cached across nights; a weekly job rather
than a nightly. They are where the 112 s was found and are worth the
trouble, but after the four parts above are in.

## Steps

| | Work | Exit |
|---|---|---|
| 1 | `e2e.sh` with `--timing` on every build and `e2e/con-leche`; `scripts/timing-fold.py`; the artifact. | A pull request's run has `timing-<sha>` with one line per paper. |
| 2 | The `timing` branch; the nightly appends; `concurrency`; `contents: write` on the e2e job in the schedule only. | Two nights, two points per paper on the branch. |
| 3 | The job summary with the table and the Mermaid chart; `scripts/timing-chart.py`; `docs/timing.md`. | The chart on the site shows the points so far. |
| 4 | The threshold and the window; the nightly fails on a step. | A deliberate slowdown (an `IMPRIMATUR_SLEEP_MS` in a test build, or a reverted memo) fails the next nightly and the summary names the phase. |
| 5 | The same in `imprimatur-paper`; then LLMbda weekly. | |

## Open questions

- Whether `total` should be the splicer's wall time (what the author waits
  for, but including process start-up) or the sum of the extractor's phases
  (what imprimatur computes). Both are in the line; the chart shows the
  first and the alarm can watch either.
- Whether the examples are big enough to show a regression that only a
  large paper exhibits (the route B blow-up was superlinear in grammar
  depth). `con-leche` and the about paper are the answer within reach; a
  synthetic large notation in `examples/` is the alternative if they are
  not.
- Retention: the branch is append-only and small; nothing is proposed for
  pruning it.
