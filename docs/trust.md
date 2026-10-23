# Trust checks

*For authors who want CI to fail when a paper's claims and its Lean
development disagree. [DESIGN.md](../DESIGN.md) §7.7 and §10.3 give the
reasoning behind these checks.*

`imprimatur check` reports four kinds of problem with the results a paper
cites:

| Code | Meaning |
|---|---|
| `untrusted` | the result depends on `sorry`, uses an axiom outside `allowed_axioms`, or has an untrusted constant in its dependency cone |
| `broken-ref` | the key names no declaration |
| `drift` | the statement changed since an author last checked the prose against it |
| `sig-changed` (warning) | the statement reads differently (a binder renamed, notation changed), but means the same |

## The dependency cone

**What the cone is.** A theorem's statement mentions definitions, which
mention others. The cone is every constant reached this way, up to the
trusted modules: those whose names start with an entry of
`[trust].trusted_prefixes` (by default `Mathlib`, `Std`, `Batteries`,
`Lean`, `Init`).

**What a member of the cone may not be.** Each member is checked, and is
untrusted if it:

- is defined using `sorry`;
- is an axiom (unless `allowed_axioms` lists it);
- is `partial`;
- is `unsafe`.

**Why this matters.** Without the cone check, a hypothesis definition could
be changed to `True`. The theorem would become trivial, while its statement
read exactly as before.

## Tying prose to Lean: `\leancheck` and `accept`

When prose states a result in your own words, tie it to Lean:

```latex
Every derivable judgement is sound \leancheck{MyPaper.Results.theorem1_main}.
```

After reading the prose against the Lean statement, record that you did:

```sh
imprimatur accept MyPaper.Results.theorem1_main     # or: imprimatur accept --all
```

This writes the current hashes into the paper:

```latex
\leancheck[stmt=b41c0a9e77d2, sig=07ae13c4f0a1]{MyPaper.Results.theorem1_main}
```

A key can also be the title of a `latex_group` or `latex_display`: its
statement is its members', and its hashes are theirs together.

From then on, `imprimatur check` compares them with the current Lean:

- **`stmt=` differs:** an error (`drift`). Something the statement means
  has changed: the statement itself, or a definition in its cone. Re-read
  the prose, then run `accept` again.
- **Only `sig=` differs:** a warning. The statement is printed differently,
  but means the same.
- **A proof changed:** neither hash changes.

A `\leancheck` without `stmt=` is checked only for broken references and
trust.

**What a statement hash covers.** A `stmt=` hash covers:

- the statement (for a definition, also its definition);
- every definition in its cone: a recursive one by its equation lemmas, any
  other by its body;
- binders, but not their names, and universes, but not their names.

So it is the same on every supported Lean toolchain. With several keys,
`stmt=` covers all of them together.

## Comparator manifests

For a project audited with [comparator](https://github.com/leanprover/comparator),
list its manifests:

```toml
[manifests]
comparator = ["lean/ComparatorChallenges/*.json"]
```

Each theorem in a manifest is checked, even if the paper doesn't mention
it:

- it must exist;
- it must be trusted, using the manifest's `permitted_axioms` in place of
  `allowed_axioms`.

The solution modules are imported automatically. A paper can quote the
audited challenge statement as `KEY@challenge`, for example
`\begin{leanblock}{OAI.X.main@challenge}{…}`. It is rendered from the
challenge module, which is imported on its own, because it declares the
same names as the solution.

## Blueprints

With `[manifests] blueprint = true`, leanblueprint's `\lean{…}` and
`\leanok` are read too:

- every `\lean{…}` key must exist;
- a node marked `\leanok` whose declarations aren't trusted is an error
  (`leanok-untrusted`);
- a `\lean{…}` without `\leanok` is work in progress, so its `sorry` is not
  reported;
- `strip` leaves blueprint markup alone.

## In CI

Run `imprimatur check` in CI and before submitting. It exits non-zero on
any error. Warnings (`sig-changed`, `orphan-slot`, `missing-input`) don't
fail it.
