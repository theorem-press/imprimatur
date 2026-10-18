/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Render

/-!
# Custom views

A project adds a view in its notation module (DESIGN §7.3):

```lean
@[latex_view "paper.rules"]
def paperRules : Imprimatur.ViewFn := fun key c opts => do
  …
```

The extractor finds it through the attribute and runs it with `evalConst`. A
custom view gets the key as written in the TeX, the declaration (if the key
names one), and the block's options. It runs in `RenderM`, so it can use the
notation in scope (`Imprimatur.Render.render`).
-/

namespace Imprimatur

open Lean Meta

/-- A custom view: the key, the declaration it names (if any), and the
block's options; the TeX to splice. -/
abbrev ViewFn := String → Option ConstantInfo → Array (String × String) → Render.RenderM String

/-- `@[latex_view "name"]` registers a `ViewFn` as the view `name`. -/
initialize registerBuiltinAttribute {
  name := `latex_view
  descr := "a custom imprimatur view (DESIGN §7.3)"
  add := fun decl stx _ => do
    let some name := stx[1].isStrLit?
      | throwError "usage: @[latex_view \"name\"]"
    let ty := (← getConstInfo decl).type
    unless ty.isConstOf ``ViewFn do
      throwError "a latex_view must have type Imprimatur.ViewFn"
    modifyEnv (notationExt.addEntry · (.view name decl))
}

/-- Syntax of the attribute. -/
syntax (name := latex_view) "latex_view " str : attr

/-- Run a custom view (the implementation). -/
unsafe def runCustomViewImpl (fn : Name) (key : String) (c : Option ConstantInfo)
    (opts : Array (String × String)) : Render.RenderM String := do
  let f ← evalConstCheck ViewFn ``ViewFn fn
  f key c opts

/-- Run a custom view. -/
@[implemented_by runCustomViewImpl]
opaque runCustomView (fn : Name) (key : String) (c : Option ConstantInfo)
    (opts : Array (String × String)) : Render.RenderM String

end Imprimatur
