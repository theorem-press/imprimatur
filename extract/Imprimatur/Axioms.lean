/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# The axioms a constant depends on

What Lean's `collectAxioms` computes, with a cache that outlives one call:
the axioms reachable from a constant through the constants of its type and
its value (and an inductive type's constructors), each axiom counting
itself. Lean's collector walks the whole proof afresh for every call, and an
export asks it once per entry, over proofs that share most of their
constants; here the answer for each constant is kept for the export.

A constant whose exploration meets a constant still being explored (a
cycle: an inductive type and its constructors, mutual definitions) has
only a partial answer there, so it is not kept unless the only such
constant was itself, the root of its cycle, whose answer is complete.
-/

namespace Imprimatur.Axioms

open Lean

/-- The answers kept so far. The entries of one export share one
environment; `reset` clears it before an export in another. -/
initialize memo : IO.Ref (NameMap (Array Name)) ← IO.mkRef {}

/-- Forget the answers: the environment is about to change. -/
def reset : IO Unit := memo.set {}

/-- The walk's state: the answers, and the constants being explored. -/
structure State where
  /-- Complete answers. -/
  memo : NameMap (Array Name)
  /-- The constants on the path from the root. -/
  inProgress : NameSet := {}

/-- The axioms reachable from `c`, without repeats, and the constants in
progress its exploration met. -/
partial def go (env : Environment) (c : Name) : StateM State (Array Name × Array Name) := do
  if let some axs := (← get).memo.find? c then return (axs, #[])
  if (← get).inProgress.contains c then return (#[], #[c])
  modify fun s => { s with inProgress := s.inProgress.insert c }
  let (own, exprs, more) : Bool × Array Expr × Array Name := match env.find? c with
    | some (.axiomInfo v) => (true, #[v.type], #[])
    | some (.defnInfo v) => (false, #[v.type, v.value], #[])
    | some (.thmInfo v) => (false, #[v.type, v.value], #[])
    | some (.opaqueInfo v) => (false, #[v.type, v.value], #[])
    | some (.quotInfo _) => (false, #[], #[])
    | some (.ctorInfo v) => (false, #[v.type], #[])
    | some (.recInfo v) => (false, #[v.type], #[])
    | some (.inductInfo v) => (false, #[v.type], v.ctors.toArray)
    | none => (false, #[], #[])
  let mut acc : Array Name := if own then #[c] else #[]
  let mut have_ : NameSet := if own then ({} : NameSet).insert c else {}
  let mut met : Array Name := #[]
  let deps := exprs.foldl (fun ds e => ds ++ e.getUsedConstants) more
  for d in deps do
    let (axs, m) ← go env d
    for a in axs do
      unless have_.contains a do
        acc := acc.push a
        have_ := have_.insert a
    met := met ++ m
  modify fun s => { s with inProgress := s.inProgress.erase c }
  let others := met.filter (· != c)
  if others.isEmpty then modify fun s => { s with memo := s.memo.insert c acc }
  return (acc, others)

/-- The axioms `c` depends on, in the order found. -/
def collect {m : Type → Type} [Monad m] [MonadEnv m] [MonadLiftT IO m] (c : Name) : m (Array Name) := do
  let env ← getEnv
  let kept ← (memo.get : IO _)
  let ((axs, _), st) := (go env c).run { memo := kept }
  (memo.set st.memo : IO Unit)
  return axs

end Imprimatur.Axioms
