/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A seeded generator

Random values for property tests. The generator is SplitMix64, written out
here so that a seed produces the same values on every toolchain and
platform; that is what lets a printed seed reproduce a failure.
-/

namespace Testkit

/-- The state of a SplitMix64 generator. -/
structure Rng where
  /-- The current state word. -/
  state : UInt64

/-- Advance the generator, returning 64 random bits. -/
def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- A 64-bit FNV-1a hash of a string's UTF-8 bytes; stable across toolchains,
unlike `String.hash`. -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.data.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001B3) 0xCBF29CE484222325

/-- A generator of `α`s. It reads a size bound, which grows over a property
run, and threads the random state. -/
abbrev Gen (α : Type) := ReaderT Nat (StateM Rng) α

namespace Gen

/-- Run a generator from a seed at a given size. -/
def run {α : Type} (g : Gen α) (seed : UInt64) (size : Nat) : α :=
  (ReaderT.run g size |>.run ⟨seed⟩).1

/-- The current size bound. -/
def size : Gen Nat := read

/-- Run `g` with the size bound replaced by `n`. -/
def resize {α : Type} (n : Nat) (g : Gen α) : Gen α :=
  withReader (fun _ => n) g

/-- 64 random bits. -/
def u64 : Gen UInt64 :=
  modifyGet Rng.next

/-- A number in `[0, n)`; `0` when `n = 0`. -/
def nat (n : Nat) : Gen Nat := do
  if n == 0 then return 0
  return (← u64).toNat % n

/-- A number in `[lo, hi]`. -/
def natIn (lo hi : Nat) : Gen Nat := do
  return lo + (← nat (hi + 1 - lo))

/-- A fair coin. -/
def bool : Gen Bool := do
  return (← nat 2) == 1

/-- `true` with probability `num / den`. -/
def chance (num den : Nat) : Gen Bool := do
  return (← nat den) < num

/-- One of the given values, chosen uniformly. -/
def elem {α : Type} [Inhabited α] (xs : Array α) : Gen α := do
  return xs[← nat xs.size]!

/-- One of the given generators, chosen uniformly. -/
def oneOf {α : Type} [Inhabited α] (gs : Array (Gen α)) : Gen α := do
  if gs.isEmpty then return default
  gs[← nat gs.size]!

/-- One of the given generators, chosen with the given weights. -/
def frequency {α : Type} [Inhabited α] (gs : List (Nat × Gen α)) : Gen α := do
  let total := gs.foldl (fun n p => n + p.1) 0
  let rec pick : Nat → List (Nat × Gen α) → Gen α
    | _, [] => return default
    | k, (w, g) :: rest => if k < w then g else pick (k - w) rest
  pick (← nat total) gs

/-- A list of up to `size` elements. -/
def listOf {α : Type} (g : Gen α) : Gen (List α) := do
  let n ← nat ((← size) + 1)
  let mut xs := []
  for _ in [0:n] do
    xs := (← g) :: xs
  return xs

/-- A string of up to `size` characters drawn from `chars`. -/
def stringOf (chars : Array Char) : Gen String := do
  return String.ofList (← listOf (elem chars))

end Gen

end Testkit
