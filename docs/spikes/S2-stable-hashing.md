# Spike S2: stable statement hashes

*Result: **works**, with three changes to DESIGN §7.7. With these changes the
canonical form of every statement and its dependency cone in the `Trust`
fixture is byte-identical on v4.28.0-rc1, v4.31.0, v4.34.1 and v4.35.0. Run on
2026-10-17.*

## Question

Does a canonical serialisation of `Expr`, with binder names dropped and
universe parameters renamed, give the same hash for the same declaration on
every toolchain? Do the dependency-cone walk and `collectAxioms` behave the
same way (PLAN §3)?

## What was built

- **The `Trust` fixture** (`test/fixtures/Trust`, kept: M3 needs it). It
  covers structural and well-founded recursion, pattern matching, an
  inductive predicate, a structure with an instance, universe polymorphism,
  `sorry` in a proof and three definitions deep in a statement, a custom
  axiom, a `partial` and an `unsafe` definition, and `Trust.uses_hyp`, whose
  hypothesis `Trust.Hyp` has a real and a vacuous version selected by
  `lake build -Kweak=1`. Two pairs of theorems differ only in binder or
  universe names.
- **A serialiser** (thrown away). It writes `Expr` as an s-expression:
  - binder names are dropped, and binder info is kept;
  - universe parameters become `u0`, `u1`, … by position;
  - `mdata` is dropped.
- **A cone walk.** It starts from the constants of the statement and follows
  each constant's type, its definition (see below), the constructors of
  inductives and the inductive of a constructor or recursor. It stops at
  constants whose *module* is trusted.

The fixture was built on each toolchain, with both variants of `Trust.Hyp`.
The serialiser printed every theorem's statement, axioms and cone. The outputs
were then compared.

## Results

**Bodies are not stable across the range.** With definitions serialised by
their values:

- v4.31.0, v4.34.1 and v4.35.0 are byte-identical;
- v4.28.0-rc1 differs. Structural recursion compiles differently: from v4.31
  the body of `double` calls an auxiliary `Trust.double._f`, whereas v4.28
  inlines a matcher application. Matcher bodies also differ (`Eq.ndrec_symm`
  in later versions against `Eq.ndrec` with `Eq.symm` in v4.28).

**Equation lemmas are stable.** Each definition in the cone is serialised by
its type plus the statements of its equation lemmas (`Meta.getEqnsFor?`), and
the walk follows the constants in those statements rather than the body. The
output is then byte-identical on all four toolchains, for both variants. The
walk never reaches `brecOn`, `below`, matchers or `_f` helpers.
`getEqnsFor?` also gives equations for non-recursive definitions such as
`Trust.Hyp` and `Trust.isZero`.

**Hash properties on the fixture** (SHA-256 of the canonical form, first 16
hex digits; identical on all four toolchains):

| Declarations | Hash | As intended? |
|---|---|---|
| `double_even` and `double_even_renamed` (binder renamed) | `7e61db2023a9c3d9` (both) | yes: same |
| `pairMap_fst` and `pairMap_fst_renamed` (universes and binders renamed) | `a8ee792b7376db33` (both) | yes: same |
| `uses_hyp`, real against vacuous `Hyp` | differ, only in the cone entry for `Trust.Hyp` | yes: drift is caught |

**`collectAxioms` agrees on all four toolchains**:

- `[]` for `double_even`;
- `[propext, Quot.sound]` for `norm1_add`;
- `[sorryAx]` for `direct_sorry`, `uses_direct_sorry` and `deep_sorry`;
- `[Trust.custom_axiom]` for `uses_custom_axiom`.

For `deep_sorry`, whose proof is honest but whose statement mentions a
definition built on `sorry`, `collectAxioms` reports `sorryAx`, because it
follows definitions in types. The `partial` `collatz` appears in the cone as
an `opaque` constant with no body, and `collectAxioms` doesn't flag it, so
the cone check must (DESIGN §7.7).

## Changes to the design

1. **`trusted_prefixes` are module prefixes, not namespaces.** Core
   constants such as `Nat.add`, `HAdd.hAdd` and `instAddNat` are declared in
   module `Init.Prelude` but live in no `Init` namespace. A namespace test
   would pull all of core into every cone. The walk uses
   `env.getModuleIdxFor?` and tests the module name. DESIGN §6.1 and §7.7 are
   updated.
2. **Definitions in the cone are hashed by their equation lemmas, not their
   bodies.** For each definition: its type, then the types of
   `getEqnsFor?`, in order. Fall back to the body only when there are no
   equations. Matchers, `brecOn`, `below` and other auxiliary constants never
   enter the cone. DESIGN §7.7 is updated.
3. **Import with `loadExts := true`.** Without it, `getEqnsFor?` fails on an
   imported environment ("failed to generate equational theorem … no
   progress"), and `Meta.isMatcherCore` returns `false` for matchers. With
   it, both work on all four toolchains. It needs
   `enableInitializersExecution`, and so an `unsafe` entry point (see also S1,
   finding 2).
4. **Normalise `sorry`.** An elaborated `sorry` is `sorryAx` applied to a
   unique tag (a `Lean.Name` literal that encodes where the `sorry` was
   written). A canonical form that kept the tag would change with unrelated
   edits above the `sorry`. The serialiser must replace every `sorryAx`
   application by one fixed token.

## Remaining risks for M3

- **Equation shapes may still change.** Complex pattern matches (overlapping
  patterns, `match` with side conditions, mutual and nested recursion,
  `where` clauses) produce equations whose shape could change between
  toolchains. The fixture has only simple cases. M3 extends `Trust` with these
  before the cross-toolchain golden test is trusted. PLAN's fallback stands:
  per-toolchain hashes with "toolchain changed, run `accept`".
- **Generated names enter the hash.** Cone entries include constant names, so
  an auto-generated instance name (`Trust.instAddPoint`) is part of the hash.
  The scheme for these names has changed in Lean's past. It was stable across
  v4.28–v4.35 on the fixture.
- **Cost on Mathlib-sized cones isn't measured.** Equation generation runs
  once per project definition in the cone (trusted modules are skipped).
  Measure it in the M3 integration run.

The spike code is not kept in the repository (PLAN §3). The fixture is kept.

## Revised in M3

The math catalogue's comparator manifests, run in external mode
(`scripts/integration.sh`), changed two of the conclusions above:

1. **Equation lemmas only for recursive definitions.** Generating equation
   lemmas for one non-recursive definition (`ProducedMarkedSeamEquations`,
   a few `let`s) used more than 12 GB. That work happens where the extractor's
   heartbeat limit doesn't reach it. Equation lemmas are needed only where
   the compiled form differs between toolchains, which is recursion.
   - A recursive definition is now hashed by its equation lemmas.
   - Any other definition is hashed by its body, which is what the author
     wrote.
   - Matchers and auxiliary recursors are hashed by their type alone.
   - The fixtures' hashes are still identical on v4.28.0-rc1 to v4.35.0.
2. **The serialisation must follow sharing.** The same definition's body is
   3,813 shared nodes, but more than 10^8 as a tree. The serialisation is now
   a Merkle hash memoised on pointers, and is linear in the shared size. The
   memo table must be keyed on pointers, not on `Expr` equality, which
   ignores binder annotations that the serialisation keeps. A
   hash-invariance property caught that mistake.
