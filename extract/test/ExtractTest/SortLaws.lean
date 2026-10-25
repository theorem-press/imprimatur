/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur
import Testkit

/-!
# The laws of Lean's sorts (docs/coercion-chains.md, B2)

Phase B4 normalises a derivation with chains of any length to one the
chain rule admits, by cutting every sort at depth `D + 1`, where `D` is
the depth of the grammar. That the cut derivation is still one rests on
laws of the algebra `Imprimatur.Validate.leanSorts`, each a property here
and a theorem in phase B3:

- **Sorts are terms.** `STerm.parse` reads back what `STerm.render` writes.
- **The cut.** `trunc d` keeps a sort within depth `d`, is the sort when
  it was within already, and is below it: `below σ' σ` says `σ'` is `σ`
  with some parts replaced by `*`.
- **Compatibility is monotone**, in both sorts: a sort below a compatible
  one is compatible, since `*` matches anything.
- **Binding is monotone**: a hole's sort of depth at most `D` bound to a
  filler cut at `D + 1` binds the same variables, to parts below those the
  filler binds. (Cut at the depth of a variable, a filler may bind fewer
  variables, and a later occurrence may bind a variable to something
  else; the law needs the cut below every variable.)
- **The expected sort is monotone** in the bindings, and no deeper than
  the hole's sort and the deepest binding together.
-/

open Testkit Imprimatur Imprimatur.Validate

namespace ExtractTest.SortLaws

/-- A sort's depth: atoms at zero, parts one deeper. -/
partial def depth : STerm → Nat
  | .atom _ => 0
  | .arrow a b => 1 + max (depth a) (depth b)
  | .app _ as => 1 + (as.map depth).foldl max 0

/-- A sort cut at depth `d`: every part at that depth is `*`. -/
partial def trunc (d : Nat) : STerm → STerm
  | .atom a => .atom a
  | t => match d with
    | 0 => .atom "*"
    | d + 1 => match t with
      | .arrow a b => .arrow (trunc d a) (trunc d b)
      | .app h as => .app h (as.map (trunc d))
      | t => t

/-- `below σ' σ`: `σ'` is `σ` with some parts replaced by `*`. -/
partial def below : STerm → STerm → Bool
  | .atom "*", _ => true
  | .atom a, .atom b => a == b
  | .arrow a b, .arrow c d => below a c && below b d
  | .app h as, .app h' bs => h == h' && as.length == bs.length && (as.zip bs).all fun (a, b) => below a b
  | _, _ => false

/-- What `env` binds `v` to, or `*`. -/
def lookup (env : Env) (v : String) : String := ((env.find? (·.1 == v)).map (·.2)).getD "*"

/-- The type variables of sorts. -/
def tyvars : Array String := #["?α", "?β"]

/-- The atoms sorts are built from: types, universes, the unknown sort, type
variables and a type parameter. -/
def atoms : Array String := #["Nat", "Bool", "Prop", "Sort", "Sort*", "*", "?α", "?β", "'x"]

/-- A random sort, of depth at most `d`. -/
partial def genSort (d : Nat) : Gen STerm := do
  let leaf : Gen STerm := do return .atom (← Gen.elem atoms)
  if d == 0 then leaf else
  Gen.frequency [
    (2, leaf),
    (2, do return .app (← Gen.elem #["Option", "List", "Box"]) [← genSort (d - 1)]),
    (1, do return .app (← Gen.elem #["Prod", "Sum"]) [← genSort (d - 1), ← genSort (d - 1)]),
    (1, do return .arrow (← genSort (d - 1)) (← genSort (d - 1)))]

/-- Random bindings of the type variables. -/
def genEnv : Gen Env := do
  let mut env : Env := #[]
  for v in tyvars do
    if ← Gen.bool then env := env.push (v, (← genSort 2).render)
  return env

/-- The algebra. -/
def A : SortAlgebra := leanSorts

/-- The laws. -/
def tests : TestM Unit := group "sort-laws" do
  forAll "extract/prop/sort-parse-render" (genSort 3) (·.render) fun t =>
    expect (STerm.parse t.render == t) s!"parses as {repr (STerm.parse t.render)}"
  forAll "extract/prop/sort-trunc"
      (do return (← genSort 4, ← Gen.nat 5)) (fun (t, d) => s!"{t.render} at {d}") fun (t, d) => do
    let c := trunc d t
    expect (depth c ≤ d) s!"the cut {c.render} is deeper than {d}"
    expect (below c t) s!"the cut {c.render} is not below"
    expect (depth t > d || c == t) s!"cut within its depth, {c.render} is not the sort"
  forAll "extract/prop/sort-compat-monotone"
      (do let s ← genSort 3; let e ← genSort 3; return (s, trunc (← Gen.nat 4) s, e, trunc (← Gen.nat 4) e))
      (fun (s, s', e, e') => s!"{s.render} ⊒ {s'.render} against {e.render} ⊒ {e'.render}") fun (s, s', e, e') => do
    if A.compat s.render e.render then
      expect (A.compat s'.render e.render) s!"the cut {s'.render} is not compatible with {e.render}"
      expect (A.compat s.render e'.render) s!"{s.render} is not compatible with the cut {e'.render}"
      expect (A.compat s'.render e'.render) s!"the cut {s'.render} is not compatible with the cut {e'.render}"
  forAll "extract/prop/sort-bind-monotone"
      (do let s ← genSort 2; let f ← genSort 4; return (s, f, ← genEnv))
      (fun (s, f, env) => s!"{s.render} to {f.render} under {env}") fun (s, f, env) => do
    let D := depth s
    let full := A.bind env s.render f.render
    let cut := A.bind env s.render (trunc (D + 1) f).render
    for v in tyvars do
      let (a, b) := (STerm.parse (lookup cut v), STerm.parse (lookup full v))
      expect ((a == .atom "*") == (b == .atom "*")) s!"{v} is bound to {b.render}, but to {a.render} from the cut"
      expect (below a b) s!"{v} is bound to {b.render}, and to {a.render}, not below it, from the cut"
    for (v, b) in full do
      if !env.any (·.1 == v) then
        expect (depth (STerm.parse b) ≤ depth f) s!"{v} is bound to {b}, deeper than the filler"
  forAll "extract/prop/sort-expected-monotone"
      (do let t ← genSort 2; let env ← genEnv
          let mut env' : Env := #[]
          for (v, b) in env do env' := env'.push (v, (trunc (← Gen.nat 3) (STerm.parse b)).render)
          return (t, env, env'))
      (fun (t, env, env') => s!"{t.render} under {env} ⊒ {env'}") fun (t, env, env') => do
    let (e, e') := (STerm.parse (A.expected env t.render), STerm.parse (A.expected env' t.render))
    expect (below e' e) s!"expects {e.render}, but {e'.render}, not below it, under the cut bindings"
    let deepest := (env.map fun (_, b) => depth (STerm.parse b)).foldl max 0
    expect (depth e ≤ depth t + deepest) s!"expects {e.render}, deeper than the sort and the bindings"

end ExtractTest.SortLaws
