/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Imprimatur.Compat
import Imprimatur.Sha256

/-!
# Trust: dependency cones and statement hashes

DESIGN §7.7, as revised by spike S2 (`docs/spikes/S2-stable-hashing.md`).

**The dependency cone** of a declaration is every constant in its type,
followed transitively until a constant declared in a trusted module is reached.
A module is trusted when its name starts with one of `trusted_prefixes`
(`Mathlib`, `Init`, …): the test is on modules, not namespaces. The walk
follows:

- a recursive definition through its equation lemmas (`Meta.getEqnsFor?`),
  because compiled recursion differs between toolchains;
- any other definition through its body;
- a matcher or auxiliary recursor through its type only;
- an inductive type through its constructors;
- a constructor or recursor to its inductive type;
- every other constant through its type only.

Each constant of the cone is checked. It is untrusted if it:

- depends on `sorry`;
- is an axiom declared outside the trusted modules;
- is `partial`;
- is `unsafe`.

**`stmtHash`** is the SHA-256 of a canonical serialisation of the type and of
every constant in the cone. The serialisation is a Merkle hash, memoised on
shared subterms (see `ser`). In it:

- binder names are dropped, and universe parameters are numbered by position;
- metadata is dropped;
- every `sorryAx` application is one token, because an elaborated `sorry`
  carries a tag that encodes where it was written;
- a recursive definition is represented by its type and its equation lemmas,
  never its compiled body, which is not stable across toolchains.

Proofs are never followed, so a changed proof leaves the hash unchanged.
-/

namespace Imprimatur.Trust

open Lean Meta

/-! ## Canonical serialisation -/

/-- A universe level, with parameters numbered by their position in `ps`. -/
def serLevel (ps : List Name) : Level → String
  | .zero => "0"
  | .succ l => s!"(s {serLevel ps l})"
  | .max a b => s!"(max {serLevel ps a} {serLevel ps b})"
  | .imax a b => s!"(imax {serLevel ps a} {serLevel ps b})"
  | .param p => match ps.idxOf? p with
    | some i => s!"u{i}"
    | none => s!"?{p}"
  | .mvar _ => "?m"

/-- A binder's kind, which is part of the meaning of a signature. -/
def serBinder : BinderInfo → String
  | .default => "" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

/-- Serialised nodes longer than this are replaced by their SHA-256. -/
def digestOver : Nat := 64

/-- The SHA-256 of a string, in hexadecimal. -/
def sha (s : String) : String :=
  Sha256.hex (Sha256.hash s.toUTF8)

/-- One node of the serialisation, given its children's serialisations. Any
result longer than `digestOver` characters is replaced by `#` and its SHA-256. -/
def serNode (ps : List Name) (e : Expr) (kids : Array String) : String :=
  let k (i : Nat) := kids.getD i ""
  let raw := if e.isAppOf ``sorryAx then "(SORRY)" else
    match e with
    | .bvar i => s!"#{i}"
    | .sort l => s!"(S {serLevel ps l})"
    | .const n us => s!"(C {n}{String.join (us.map (" " ++ serLevel ps ·))})"
    | .app .. => s!"(A {k 0} {k 1})"
    | .lam _ _ _ i => s!"(L{serBinder i} {k 0} {k 1})"
    | .forallE _ _ _ i => s!"(P{serBinder i} {k 0} {k 1})"
    | .letE .. => s!"(Z {k 0} {k 1} {k 2})"
    | .lit (.natVal n) => s!"(N {n})"
    | .lit (.strVal s) => s!"(T {(Json.str s).compress})"
    | .mdata .. => k 0
    | .proj s i _ => s!"(J {s} {i} {k 0})"
    | .fvar _ => "?fvar"
    | .mvar _ => "?mvar"
  if e matches .mdata .. then raw
  else if raw.length > digestOver then "#" ++ sha raw else raw

/-- The children a node's serialisation is made from. A `sorryAx`
application has none: all its arguments are ignored. -/
def serKids (e : Expr) : Array Expr :=
  if e.isAppOf ``sorryAx then #[] else
  match e with
  | .app f a => #[f, a]
  | .lam _ t b _ | .forallE _ t b _ => #[t, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ b | .proj _ _ b => #[b]
  | _ => #[]

/-- The serialisation as a plain tree walk: the reference definition. -/
partial def serTree (ps : List Name) (e : Expr) : String :=
  serNode ps e ((serKids e).map (serTree ps))

/-- The same, memoised on pointers, so the cost is linear in the size of the
expression as Lean shares it. (Memoising on `Expr` equality would be wrong:
it ignores binder annotations, which the serialisation keeps.) -/
unsafe def serShared (ps : List Name) (e : Expr) : String :=
  (go e).run' mkPtrMap
where
  go (e : Expr) : StateM (PtrMap Expr String) String := do
    if let some s := (← get).find? e then return s
    let kids ← (serKids e).mapM go
    let out := serNode ps e kids
    modify (·.insert e out)
    return out

/-- The canonical serialisation of an expression (see the module docs), as a
Merkle hash: each node is written in terms of its children's serialisations,
and any serialisation longer than `digestOver` characters is replaced by its
SHA-256. A tree walk without sharing can take exponential time and memory:
spike S2's fixtures had no such terms, but the math catalogue does, so the
compiled code memoises on shared subterms (`serShared`). -/
@[implemented_by serShared]
def ser (ps : List Name) (e : Expr) : String :=
  serTree ps e

/-! ## The dependency cone -/

/-- Why a constant in a cone is untrusted. -/
inductive Issue where
  /-- It depends on `sorry`. -/
  | usesSorry
  /-- It is an axiom outside the trusted modules. -/
  | axiom_
  /-- It is `partial`: the kernel sees an opaque constant, not the function. -/
  | partial_
  /-- It is `unsafe`. -/
  | unsafe_
  deriving BEq, Repr, Inhabited

/-- How an issue is written in the bundle. -/
def Issue.name : Issue → String
  | .usesSorry => "sorry" | .axiom_ => "axiom" | .partial_ => "partial" | .unsafe_ => "unsafe"

/-- A declaration's cone. -/
structure Cone where
  /-- The constants, sorted, each with its canonical serialisation. -/
  members : Array (Name × String)
  /-- Untrusted members and why. -/
  issues : Array (Name × Issue)

/-- Whether `n` is declared in a trusted module. Constants of the current
module (none, in an imported environment) are not trusted. -/
def isTrusted (env : Environment) (prefixes : Array Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    match Compat.moduleName? env idx with
    | some m => prefixes.any (·.isPrefixOf m)
    | none => false
  | none => false

/-- Whether `n` was declared with `partial`: the kernel sees an opaque
constant, implemented by `n._unsafe_rec`. (Structural and well-founded
recursion also generate `_unsafe_rec` helpers, but stay definitions.) -/
def isPartial (env : Environment) (ci : ConstantInfo) : Bool :=
  ci matches .opaqueInfo .. && env.contains (Name.str ci.name "_unsafe_rec")

/-- Whether `n` is defined by structural or well-founded recursion. -/
def isRecursive (env : Environment) (n : Name) : Bool :=
  (Elab.Structural.eqnInfoExt.find? env n).isSome || (Elab.WF.eqnInfoExt.find? env n).isSome

/-- Whether `n` is a helper the elaborator generates: a matcher, an auxiliary
recursor (`casesOn`, `recOn`, `brecOn`, …), `noConfusion`, or an internal
name. These are hashed by their type alone. -/
def isAux (env : Environment) (n : Name) : Bool :=
  Meta.isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n || n.isInternal

/-- Whether an expression mentions `sorryAx`. -/
def mentionsSorry (e : Expr) : Bool :=
  (e.find? (·.isConstOf ``sorryAx)).isSome

/-- The most members a cone may have; beyond this the walk stops with an
error rather than exploring a whole library. -/
def maxCone : Nat := 2000

/-- The cone of a declaration. For a theorem or an axiom, the statement is
its type, so the walk starts from the type's constants: the proof doesn't
count. For anything else (a definition, an inductive type, …), what the
declaration means includes its own definition, so the walk starts from the
declaration itself. -/
partial def cone (prefixes : Array Name) (ci : ConstantInfo) : MetaM Cone := do
  let mut seen : NameSet := {}
  let mut todo : Array Name := match ci with
    | .thmInfo _ | .axiomInfo _ => ci.type.getUsedConstants
    | _ => ci.type.getUsedConstants.push ci.name
  let mut members : Array (Name × String) := #[]
  let mut issues : Array (Name × Issue) := #[]
  while !todo.isEmpty do
    if members.size ≥ maxCone then
      throwError "the dependency cone has more than {maxCone} members outside the trusted \
        modules; if it reaches into libraries the project depends on, add their module \
        prefixes to [trust].trusted_prefixes"
    let c := todo.back!
    todo := todo.pop
    let env ← getEnv
    if seen.contains c || isTrusted env prefixes c || c == ``sorryAx then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    if (← (IO.getEnv "IMPRIMATUR_TRACE" : IO _)) == some "1" then
      IO.eprintln s!"imprimatur-export:   cone {members.size}: {c} ({← IO.monoMsNow})"
    let ps := ci.levelParams
    -- What represents the constant, and what the walk follows from it.
    let mut parts : Array Expr := #[ci.type]
    let mut next : Array Name := #[]
    match ci with
    | .defnInfo d =>
      if isAux env c then
        -- A matcher or recursor helper is determined by its type.
        pure ()
      else if isRecursive env c then
        -- Compiled recursion differs between toolchains; its equations don't.
        let eqns ← try getEqnsFor? c catch _ => pure none
        match eqns with
        | some es =>
          for e in es do
            parts := parts.push (← getConstInfo e).type
        | none => parts := parts.push d.value
      else
        -- A non-recursive body is what the author wrote. (Generating
        -- equations for it can be very expensive, spike S2 notwithstanding.)
        parts := parts.push d.value
    | .inductInfo i => next := next ++ i.ctors.toArray
    | .ctorInfo i => next := next.push i.induct
    | .recInfo i => next := next.push i.getMajorInduct
    | _ => pure ()
    let text := String.join (parts.toList.map (ser ps)) ++ s!" [{kindTag ci}]"
    members := members.push (c, text)
    for p in parts do
      next := next ++ p.getUsedConstants
    todo := todo ++ next
    -- Problems with this constant.
    if parts.any mentionsSorry then issues := issues.push (c, .usesSorry)
    if ci.isUnsafe then issues := issues.push (c, .unsafe_)
    if isPartial env ci then issues := issues.push (c, .partial_)
    if ci matches .axiomInfo .. then issues := issues.push (c, .axiom_)
  let byName := fun (a b : Name × String) => decide (a.1.toString < b.1.toString)
  return { members := members.qsort byName,
           issues := issues.qsort (fun a b => decide (a.1.toString < b.1.toString)) }
where
  /-- A short tag for the kind of constant. -/
  kindTag : ConstantInfo → String
    | .defnInfo _ => "def" | .thmInfo _ => "thm" | .axiomInfo _ => "ax" | .opaqueInfo _ => "opaque"
    | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"

/-- The canonical text whose hash is `stmtHash`: the type, then each member
of the cone with its name. -/
def stmtText (ci : ConstantInfo) (c : Cone) : String :=
  "type " ++ ser ci.levelParams ci.type ++ "\n" ++
    String.join (c.members.toList.map fun (n, t) => s!"{n} {t}\n")

end Imprimatur.Trust
