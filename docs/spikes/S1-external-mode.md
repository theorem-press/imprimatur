# Spike S1: external mode

*Result: **works** on all three motivating toolchains. External mode stays the
recommended default (DESIGN §6.3 A). Run on 2026-10-17.*

## Question

Can a prebuilt extractor combine its own `.olean` files with a host's
`lake env` search path, elaborate a notation file in-process with Lean's
frontend, and then see the host's modules at `private` level? This must work on
v4.28.0-rc1, v4.31.0 and v4.34.1 (PLAN §3).

## What was built

A Lake package, built once per toolchain outside every host project, with two
parts:

- **`SpikeLib`**, standing in for `Imprimatur`. It registers an environment
  extension with `initialize`, and defines a command
  `latex_spike <ident> => "<str>"`. The command resolves the identifier with
  `realizeGlobalConstNoOverloadWithInfo`, so a misspelt name is an error
  (DESIGN §4, constraint 3), and records it in the extension.
- **`runner`**, an executable (`supportInterpreter = true`) that takes a host
  directory, a notation file, a host module and a declaration, and then:
  1. checks that the host's `lean-toolchain` matches `Lean.versionString`;
  2. runs `lake env printenv LEAN_PATH` in the host directory (elan picks the
     host's toolchain from there), and appends its own
     `IO.appDir / ".." / "lib" / "lean"`;
  3. calls `initSearchPath (← findSysroot) path` and
     `enableInitializersExecution`;
  4. elaborates the notation file with
     `Lean.Elab.runFrontend input {} fileName `Notation`;
  5. reads the extension's entries from the resulting environment, checks that
     the declaration's proof body is present, and runs `collectAxioms` on it;
  6. separately, imports the host module with
     `importModules … (loadExts := true) (level := .private)` and repeats
     step 5.

The notation file imports the host modules and `SpikeLib`, then uses
`latex_spike` on a constructor and a theorem.

## Results

| Host | Toolchain | Notation file | Steps 1–5 | Step 6 | Wall time | Peak RSS |
|---|---|---|---|---|---|---|
| project-a `proj/` (`Semantics.BigStep`) | v4.28.0-rc1 | 11 s | ✓ | ✓ | 27 s | 4.1 GB |
| project B (`MyPaper.Results`, Mathlib) | v4.31.0 | 92 s | ✓ | ✓ after fix below | 2 min 24 s | 11.4 GB |
| math catalogue (`…Uniformization.RiemannDiskSeed`, a `module` file, Mathlib) | v4.34.1 | 95 s | ✓ | ✓ after fix below | 3 min 11 s | 10.8 GB |

In every run:

- the command elaborated and recorded both entries, so the extractor's own
  `.olean` files and compiled elaborators combine with the host's search path;
- the proof body of the target theorem was present and `collectAxioms`
  returned `[propext, Classical.choice, Quot.sound]`. For the math catalogue the
  target is in a `module` file, so this confirms that a non-`module` notation
  file sees `private` data (DESIGN §6.2);
- nothing was written to the host projects (`git status` unchanged in all
  three).

## Findings that change the design or the plan

1. **One import, not two.** Step 6 is redundant. The environment from
   elaborating the notation file already contains the host modules at
   `private` level. Importing them again doubled peak memory, from about 6.5–7
   to about 11 GB on the Mathlib hosts. The extractor should take its
   environment from the notation file, or from a generated one when there is no
   notation file, and never import twice.
2. **`runFrontend` turns initializer execution off again** on v4.31.0 and
   v4.34.1, but not on v4.28.0-rc1. Calling `importModules (loadExts := true)`
   afterwards fails with "`enableInitializersExecution` must be run before
   calling `importModules (loadExts := true)`". Any later import must call
   `enableInitializersExecution` again. This belongs in `Compat/`.
3. **The frontend API is the same on all three toolchains** for what external
   mode needs. Positional `runFrontend input opts fileName mainModuleName`
   returns `IO (Option Environment)` everywhere; later versions only add
   optional parameters. `importModules` has `loadExts` and
   `level := .private` on all three, which also confirms the Appendix A claim
   for v4.28 and v4.31.
4. **Memory is the real cost.** Elaborating a notation file that imports
   Mathlib-based modules peaks at about 7 GB and takes about 90 s on this WSL
   machine. The page cache was cold for the first run. Most of this is
   presumably loading Mathlib, which any tool that imports these modules pays.
   The spike didn't time plain `lake env lean` on the same file for
   comparison. README should state the memory needed. Running two Mathlib
   hosts in parallel on a 16 GB machine isn't safe.
5. **`String.trim` is already deprecated in v4.28.0-rc1** (replaced by
   `String.trimAscii`). This is another API to avoid in code that must build
   across the toolchain range (see CONTRIBUTING.md).
6. **Matching the toolchain.** Compare the host's `lean-toolchain` with
   `"leanprover/lean4:v" ++ Lean.versionString`. `Lean.versionStringCore` drops
   the `-rc1` suffix and must not be used for this.

## Not tested

- Notation files that define `@[latex_view]` functions, which would need to
  be compiled, or interpreted with `evalConst`. Sidecar mode remains the
  answer for those (DESIGN §6.3 B).
- Hosts with `precompileModules` or native plugins.
- macOS and Windows.

The spike code is not kept in the repository (PLAN §3).
