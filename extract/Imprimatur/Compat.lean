/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Differences between toolchains

Everything that depends on the Lean version lives here (DESIGN §13). The
supported range is v4.28.0-rc1 to v4.35.0. Spikes S1 and S2 found these
differences, all handled below:

- `importModules` takes `level` and `loadExts` on every supported toolchain.
  `loadExts := true` is needed for equation lemmas and matcher information
  (spike S2), and it needs `enableInitializersExecution` first.
- From v4.31, `Elab.runFrontend` turns initializer execution off again, so it
  must be turned back on before a later import (spike S1). `importModules`
  does the same, so each import is preceded by `enableInitializersExecution`.
- Below the `private` level, a public theorem of a `module` file is imported
  as an axiom with no body, and `collectAxioms` gives a wrong answer that
  differs between toolchains. The `ModuleSys` fixture tests this.
-/

namespace Imprimatur.Compat

open Lean

/-- Import modules at the `private` level, so that proof bodies are present
(DESIGN §4, constraint 7). The search path must already be set. -/
unsafe def importPrivate (modules : Array Name) : IO Environment := do
  enableInitializersExecution
  importModules (modules.map fun m => { module := m }) {} (loadExts := true) (level := .private)

/-- The modules an environment imports, by index. -/
def moduleName? (env : Environment) (idx : ModuleIdx) : Option Name :=
  env.header.moduleNames[idx.toNat]?

end Imprimatur.Compat
