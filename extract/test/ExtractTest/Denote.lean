/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# Unit tests of what a reading denotes (DESIGN §18.4)

Readings over the core pack, denoted against `Init` alone: the term built,
whether it is well typed, and whether it agrees with an expression at
reducible transparency or by skeleton.
-/

open Testkit Imprimatur Imprimatur.Validate Lean Meta

namespace ExtractTest.DenoteTests

/-- A leaf, or a node with children. -/
def l (n : String) : Reading := .node n []
/-- See `l`. -/
def n (name : String) (kids : List Reading) : Reading := .node name kids

/-- Run a `MetaM` computation in an environment with `Init`. -/
unsafe def runMeta {α : Type} (env : Environment) (x : MetaM α) : IO α := do
  let (a, _) ← (x.run' {} {}).toIO { fileName := "<denote>", fileMap := default } { env }
  return a

/-- The cases, over `a b : ℕ` and `p : Prop`, as booleans named for the
check each stands for. -/
unsafe def cases (env : Environment) : IO (Array (String × Bool)) := runMeta env do
  let rules := Packs.core ++ Packs.logic
  let nat := mkConst ``Nat
  withLocalDeclD `a nat fun a => withLocalDeclD `b nat fun b =>
  withLocalDeclD `p (mkSort Level.zero) fun p => do
    let atoms : Array Atom := #[
      { tex := "a", sort := "Nat", fvar := some a.fvarId!, name := "a", expr := some a },
      { tex := "b", sort := "Nat", fvar := some b.fvarId!, name := "b", expr := some b },
      { tex := "p", sort := "Prop", fvar := some p.fvarId!, name := "p", expr := some p },
      { tex := "2", sort := "Nat", expr := some (mkRawNatLit 2) },
      { tex := "4", sort := "Nat", expr := some (mkRawNatLit 4) }]
    let denote (r : Reading) : MetaM (Option (Expr × Array MVarId × Denote.Denotation)) := do
      match ← Denote.run rules atoms r with
      | .ok d => pure (some (d.term, d.insts, d))
      | .error _ => pure none
    let prop := mkSort Level.zero
    let mut out := #[]
    -- `a + b` denotes `a + b`, well typed as a natural, and is it.
    let some (c, insts, d) ← denote (n "HAdd.hAdd" [l "a", l "b"]) | return #[("denote/a+b", false)]
    out := out.push ("denote/a+b-typed", ← Denote.wellTyped c insts (some nat))
    out := out.push ("denote/a+b-agrees", ← Denote.agrees rules (← mkAppM ``HAdd.hAdd #[a, b]) d)
    out := out.push ("denote/a+b-not-b+a", !(← Denote.agrees rules (← mkAppM ``HAdd.hAdd #[b, a]) d))
    -- `2 + 2` is not `4`: reducible transparency does not compute.
    let some (c, insts, d) ← denote (n "HAdd.hAdd" [l "2", l "2"]) | return #[("denote/2+2", false)]
    out := out.push ("denote/2+2-typed", ← Denote.wellTyped c insts (some nat))
    out := out.push ("denote/2+2-not-4", !(← Denote.agrees rules (mkNatLit 4) d))
    -- `a ≠ b` is `¬ a = b`: `Ne` is reducible.
    let some (c, insts, d) ← denote (n "Ne" [l "a", l "b"]) | return #[("denote/ne", false)]
    out := out.push ("denote/ne-typed", ← Denote.wellTyped c insts (some prop))
    out := out.push ("denote/ne-is-not-eq", ← Denote.agrees rules (mkNot (← mkAppM ``Eq #[a, b])) d)
    -- `a = 2` is well typed as a proposition, and not as a natural.
    let some (c, insts, d) ← denote (n "Eq" [l "a", l "2"]) | return #[("denote/eq", false)]
    out := out.push ("denote/eq-typed", ← Denote.wellTyped c insts (some prop))
    out := out.push ("denote/eq-not-nat", !(← Denote.wellTyped c insts (some nat)))
    out := out.push ("denote/eq-agrees", ← Denote.agrees rules (← mkAppM ``Eq #[a, mkNatLit 2]) d)
    -- `a = p` compares a natural with a proposition: no denotation fits, or
    -- an ill-typed one.
    let ill : Bool ← do
      match ← denote (n "Eq" [l "a", l "p"]) with
      | none => pure true
      | some (c, insts, _) => do
        let ok ← Denote.wellTyped c insts (some prop)
        pure (!ok)
    out := out.push ("denote/ill-typed", ill)
    -- `(a : ℤ) = b` renders as `a = b`: the casts are invisible, and the
    -- skeletons agree where reducible unfolding does not.
    let int := mkConst ``Int
    let cast (x : Expr) : MetaM Expr := mkAppOptM ``Nat.cast #[some int, none, some x]
    let orig ← mkAppM ``Eq #[← cast a, ← cast b]
    let some (c, insts, d) ← denote (n "Eq" [l "a", l "b"]) | return #[("denote/cast", false)]
    out := out.push ("denote/cast-typed", ← Denote.wellTyped c insts (some prop))
    out := out.push ("denote/cast-skeleton", ← Denote.agrees rules orig d)
    out := out.push ("denote/cast-not-plus", !(← Denote.agrees rules (← mkAppM ``Eq #[← cast a, ← cast (← mkAppM ``HAdd.hAdd #[b, b])]) d))
    -- `∀ x : ℕ, x = x` by the built-in form, with the bound variable named by the text.
    let r := n "∀" [l "x", l "\\mathbb{N}", n "Eq" [l "x", l "x"]]
    let atoms' := atoms.push { tex := "\\mathbb{N}", sort := "Sort", expr := some nat }
    match ← Denote.run rules atoms' r with
    | .error _ => out := out.push ("denote/forall", false)
    | .ok d =>
      let c := d.term
      out := out.push ("denote/forall-typed", ← Denote.wellTyped c d.insts (some prop))
      let orig ← withLocalDeclD `y nat fun y => do mkForallFVars #[y] (← mkAppM ``Eq #[y, y])
      out := out.push ("denote/forall-agrees", ← Denote.agrees rules orig d)
    -- A rule's node that no rule reads is no denotation.
    out := out.push ("denote/unknown", (← denote (n "Nowhere.nothing" [l "a"])).isNone)
    return out

/-- All the denotation tests. -/
unsafe def tests : TestM Unit := group "denote" do
  initSearchPath (← findSysroot)
  let env ← Compat.importPrivate #[`Init]
  for (name, ok) in ← cases env do
    check s!"extract/{name}" ok

end ExtractTest.DenoteTests
