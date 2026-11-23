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
    -- `a` where an integer is expected is `↑a`: the whole reading is fit to
    -- the type expected, through Lean's coercion.
    match ← Denote.run rules atoms (l "a") (some int) with
    | .error _ => out := out.push ("denote/fit-whole", false)
    | .ok d =>
      out := out.push ("denote/fit-whole-typed", ← Denote.wellTyped d.term d.insts (some int))
      out := out.push ("denote/fit-whole-agrees", ← Denote.agrees rules (← cast a) d)
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
    -- With `Option.some` hidden by a rule: `∃ S, g S = S ∧ S = a`, where
    -- `g : ℕ → Option ℕ`, reads with `S` a natural, as its second use has
    -- it, and the first use through `some`; the first use alone would make
    -- `S` an option, and the second ill typed.
    let hide (c : Name) (vars : Array (Name × String)) (template : String) (sort : String)
        (prec : Nat := 1024) : NotationRule :=
      { pat := .app c (vars.map (.var ·.1)), template, prec, assoc := "left", sort, holeSorts := vars }
    let rules' := rules.push (hide ``Option.some #[(`x, "*")] "#x" "*")
      |>.push (hide ``HAppend.hAppend #[(`a, "?α"), (`b, "?β")] "#a \\mathbin{+\\!\\!+} #b" "?α" 65)
    let optNat ← mkAppM ``Option #[nat]
    let listInt ← mkAppM ``List #[int]
    let gTy ← mkArrow nat optNat
    let more : Array (String × Bool) ← withLocalDeclD `g gTy fun g => withLocalDeclD `ys listInt fun ys => do
      let mut out : Array (String × Bool) := #[]
      let atoms' := atoms.push { tex := "g", sort := "*", fvar := some g.fvarId!, name := "g", expr := some g }
        |>.push { tex := "ys", sort := "*", fvar := some ys.fvarId!, name := "ys", expr := some ys }
      let r := n "∃" [l "S", n "And" [n "Eq" [n "app" [l "g", l "S"], l "S"], n "Eq" [l "S", l "a"]]]
      match ← Denote.run rules' atoms' r (some prop) with
      | .error _ => out := out.push ("denote/postponed-some", false)
      | .ok d =>
        out := out.push ("denote/postponed-some-typed", ← Denote.wellTyped d.term d.insts (some prop))
        let orig ← withLocalDeclD `S nat fun S => do
          let eq1 ← mkAppM ``Eq #[mkApp g S, ← mkAppM ``Option.some #[S]]
          let eq2 ← mkAppM ``Eq #[S, a]
          mkAppM ``Exists #[← mkLambdaFVars #[S] (mkAnd eq1 eq2)]
        out := out.push ("denote/postponed-some-agrees", ← Denote.agrees rules' orig d)
      -- `[a] ++ ys` with `ys : List ℤ`: the holes of `++` have their own
      -- type variables, which the default instance of `HAppend` ties, so
      -- the literal's element is cast to ℤ.
      let r := n "HAppend.hAppend" [n "list" [l "a"], l "ys"]
      match ← Denote.run rules' atoms' r (some listInt) with
      | .error _ => out := out.push ("denote/default-group", false)
      | .ok d =>
        out := out.push ("denote/default-group-typed", ← Denote.wellTyped d.term d.insts (some listInt))
        let orig ← mkAppM ``HAppend.hAppend #[← mkAppM ``List.cons #[← cast a, ← mkAppOptM ``List.nil #[some int]], ys]
        out := out.push ("denote/default-group-agrees", ← Denote.agrees rules' orig d)
      return out
    return out ++ more

/-- All the denotation tests. -/
unsafe def tests : TestM Unit := group "denote" do
  initSearchPath (← findSysroot)
  let env ← Compat.importPrivate #[`Init]
  for (name, ok) in ← cases env do
    check s!"extract/{name}" ok

end ExtractTest.DenoteTests
