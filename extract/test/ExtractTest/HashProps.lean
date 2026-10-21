/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# Hash invariance (docs/TESTING.md, Properties)

Properties of the canonical serialisation behind `stmtHash`, on random
expressions:

- renaming bound variables doesn't change it;
- renaming universe parameters doesn't change it;
- changing a constant does;
- metadata and the tag inside `sorry` don't matter.
-/

open Testkit Imprimatur Lean

namespace ExtractTest.HashProps

/-- Universe parameters of generated expressions. -/
def params : List Name := [`u, `v]

/-- A random universe level. -/
partial def genLevel : Gen Level := do
  Gen.frequency [
    (2, pure .zero),
    (3, do return .param (← Gen.elem params.toArray)),
    (1, do return .succ (← Gen.resize 0 genLevel)),
    (1, do return .max (← Gen.resize 0 genLevel) (.param `u))]

/-- A random expression with `depth` bound variables in scope. -/
partial def genExpr (depth : Nat) : Gen Expr := do
  let size ← Gen.size
  let leaf : Gen Expr := Gen.frequency [
    (if depth == 0 then 0 else 3, do return .bvar (← Gen.nat depth)),
    (2, do return .const (← Gen.elem #[`Nat, `Nat.add, `Eq, `Foo.bar]) [← genLevel]),
    (1, do return .sort (← genLevel)),
    (1, do return .lit (.natVal (← Gen.nat 10)))]
  if size == 0 then leaf else
  let smaller {α : Type} (g : Gen α) : Gen α := Gen.resize (size / 2) g
  Gen.frequency [
    (2, leaf),
    (2, do return .app (← smaller (genExpr depth)) (← smaller (genExpr depth))),
    (2, do return .forallE (← Gen.elem #[`x, `y, `h, `α]) (← smaller (genExpr depth))
            (← smaller (genExpr (depth + 1))) (← Gen.elem #[.default, .implicit, .instImplicit])),
    (1, do return .lam (← Gen.elem #[`x, `y]) (← smaller (genExpr depth))
            (← smaller (genExpr (depth + 1))) .default),
    (1, do return .mdata {} (← smaller (genExpr depth)))]

/-- Rename every binder. -/
partial def renameBinders : Expr → Expr
  | .forallE n t b i => .forallE (n.appendAfter "'") (renameBinders t) (renameBinders b) i
  | .lam n t b i => .lam (n.appendAfter "_renamed") (renameBinders t) (renameBinders b) i
  | .app f a => .app (renameBinders f) (renameBinders a)
  | .mdata m e => .mdata m (renameBinders e)
  | e => e

/-- Rename universe parameters `u, v` to `a, b`, changing nothing else.
(`instantiateLevelParams` would also simplify levels.) -/
def renameLevel : Level → Level
  | .param p => .param (if p == `u then `a else if p == `v then `b else p)
  | .succ l => .succ (renameLevel l)
  | .max x y => .max (renameLevel x) (renameLevel y)
  | .imax x y => .imax (renameLevel x) (renameLevel y)
  | l => l

/-- Rename universe parameters throughout an expression. -/
def renameLevels (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .sort l => some (.sort (renameLevel l))
    | .const n ls => some (.const n (ls.map renameLevel))
    | _ => none

/-- Replace every `Nat.add` by `Nat.mul`. -/
def changeConst (e : Expr) : Expr :=
  e.replace fun x => if x.isConstOf ``Nat.add then some (.const ``Nat.mul x.constLevels!) else none

/-- Remove every `mdata` node. -/
partial def dropMData : Expr → Expr
  | .mdata _ e => dropMData e
  | .app f a => .app (dropMData f) (dropMData a)
  | .forallE n t b i => .forallE n (dropMData t) (dropMData b) i
  | .lam n t b i => .lam n (dropMData t) (dropMData b) i
  | e => e

/-- Show an expression. -/
def render (e : Expr) : String := Trust.ser params e

/-- All the properties. -/
def tests : TestM Unit := group "hash-properties" do
  forAll "extract/prop/hash-binder-names" (genExpr 0) render fun e =>
    expect (Trust.ser params e == Trust.ser params (renameBinders e)) "renaming binders changed it"
  forAll "extract/prop/hash-universe-names" (genExpr 0) render fun e =>
    expect (Trust.ser params e == Trust.ser [`a, `b] (renameLevels e)) "renaming universes changed it"
  forAll "extract/prop/hash-sees-constants" (genExpr 0) render fun e =>
    if e.find? (·.isConstOf ``Nat.add) |>.isSome then
      expect (Trust.ser params e != Trust.ser params (changeConst e)) "a changed constant went unnoticed"
    else .ok ()
  forAll "extract/prop/hash-ignores-mdata" (genExpr 0) render fun e =>
    expect (Trust.ser params e == Trust.ser params (dropMData e)) "metadata changed it"
  let sorryAt (tag : Nat) : Expr :=
    mkApp3 (.const ``sorryAx [.zero]) (.const ``Nat []) (.const ``Bool.false []) (.lit (.natVal tag))
  checkEq "extract/hash/sorry-tag-ignored" (Trust.ser [] (sorryAt 1)) (Trust.ser [] (sorryAt 2))
  -- A term that is small when shared but has 2^60 nodes as a tree: the
  -- serialisation must follow the sharing (the math catalogue has such terms).
  let dag := (List.range 60).foldl (fun e _ => Expr.app e e) (.const ``Nat [])
  let t0 ← IO.monoMsNow
  let d := Trust.ser [] dag
  check "extract/hash/shared-terms-linear" (d.startsWith "#" && (← IO.monoMsNow) - t0 < 2000)
    s!"serialising a shared term took {(← IO.monoMsNow) - t0} ms"
  check "extract/hash/binder-kind-matters"
    (Trust.ser [] (.forallE `x (.const ``Nat []) (.bvar 0) .default) !=
      Trust.ser [] (.forallE `x (.const ``Nat []) (.bvar 0) .implicit))

end ExtractTest.HashProps
