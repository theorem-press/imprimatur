/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! Stubs with Mathlib's names and explicit arities, so that the `mathlib`
pack's rules have a golden use with no Mathlib (docs/TESTING.md, Fixtures).
Each stands for the Mathlib constant of the same name; its type keeps the
explicit arguments and the result's head, which is all a pack rule sees. -/

/-- The real numbers. -/
structure Real where
  val : Nat

instance : OfNat Real n := ⟨⟨n⟩⟩
instance : LT Real := ⟨fun a b => a.val < b.val⟩
instance : LE Real := ⟨fun a b => a.val ≤ b.val⟩
instance : Add Real := ⟨fun a b => ⟨a.val + b.val⟩⟩
instance : Mul Real := ⟨fun a b => ⟨a.val * b.val⟩⟩
instance : Div Real := ⟨fun a b => ⟨a.val / b.val⟩⟩
instance : Neg Real := ⟨fun a => a⟩
instance : NatCast Real := ⟨fun n => ⟨n⟩⟩

/-- The complex numbers, whose projections are `Complex.re` and `Complex.im`. -/
structure Complex where
  re : Real
  im : Real

def Complex.I : Complex := ⟨0, 1⟩
def Real.log (x : Real) : Real := x
def Real.exp (x : Real) : Real := x
def Real.sqrt (x : Real) : Real := x
def Real.pi : Real := 3
def Real.sin (x : Real) : Real := x
def Real.cos (x : Real) : Real := x
def Real.logb (_b x : Real) : Real := x
def abs {α : Type} (a : α) : α := a
def Norm.norm {α : Type} (_a : α) : Real := 0
/-- Casts from the rationals, and the cast itself. -/
class RatCast (α : Type) where
  ratCast : Rat → α
instance : RatCast Real := ⟨fun q => ⟨q.num.toNat⟩⟩
def Rat.cast {α : Type} [RatCast α] (q : Rat) : α := RatCast.ratCast q
structure NNReal where
  val : Real
def NNReal.toReal (x : NNReal) : Real := x.val
structure PNat where
  val : Nat
structure EReal where
  val : Real
def Real.toEReal (x : Real) : EReal := ⟨x⟩
def Irrational (_x : Real) : Prop := True
def Int.floor (x : Real) : Int := x.val
def Int.ceil (x : Real) : Int := x.val
def Nat.floor (x : Real) : Nat := x.val
def Nat.ceil (x : Real) : Nat := x.val

def Nat.factorial (n : Nat) : Nat := n
def Nat.choose (n _k : Nat) : Nat := n
def Nat.totient (n : Nat) : Nat := n
def Nat.primeCounting (n : Nat) : Nat := n
def Nat.Prime (_n : Nat) : Prop := True
def Odd {α : Type} (_n : α) : Prop := True
def Even {α : Type} (_n : α) : Prop := True
def Squarefree {α : Type} (_r : α) : Prop := True
def IsSquare {α : Type} (_a : α) : Prop := True
def Int.ModEq (_n a b : Int) : Prop := a = b
def StrictMono {α β : Type} (_f : α → β) : Prop := True
def Monotone {α β : Type} (_f : α → β) : Prop := True
def Function.Bijective {α β : Type} (_f : α → β) : Prop := True

/-- Sets, as predicates. -/
def Set (α : Type) := α → Prop
instance {α : Type} : Membership α (Set α) := ⟨fun s a => s a⟩
def Set.ofPred {α : Type} (p : α → Prop) : Set α := p
def Set.Infinite {α : Type} (_s : Set α) : Prop := True
def Set.Finite {α : Type} (_s : Set α) : Prop := True
def Set.Nonempty {α : Type} (s : Set α) : Prop := ∃ a, s a
def Set.Icc {α : Type} [LE α] (a b : α) : Set α := fun x => a ≤ x ∧ x ≤ b
def Set.ncard {α : Type} (_s : Set α) : Nat := 0

/-- Finite sets, as lists. -/
structure Finset (α : Type) where
  elems : List α
def Finset.card {α : Type} (s : Finset α) : Nat := s.elems.length
def Finset.Nonempty {α : Type} (s : Finset α) : Prop := s.elems ≠ []
def Finset.sum {α β : Type} [Add β] [OfNat β 0] (s : Finset α) (f : α → β) : β :=
  s.elems.foldl (fun acc a => acc + f a) 0
def Finset.prod {α β : Type} [Mul β] [OfNat β 1] (s : Finset α) (f : α → β) : β :=
  s.elems.foldl (fun acc a => acc * f a) 1
def Finset.univ {α : Type} : Finset α := ⟨[]⟩
def Finset.filter {α : Type} (p : α → Prop) [DecidablePred p] (s : Finset α) : Finset α :=
  ⟨s.elems.filter fun a => decide (p a)⟩
def Finset.Icc (a b : Nat) : Finset Nat := ⟨List.range (b + 1 - a) |>.map (· + a)⟩
def Finset.range (n : Nat) : Finset Nat := ⟨List.range n⟩
def Fintype.card (_α : Type) : Nat := 0

/-- Summation filters, and unconditional sums. -/
structure SummationFilter (β : Type) where
  unit : Unit := ()
def SummationFilter.unconditional (β : Type) : SummationFilter β := {}
def tsum {α β : Type} [OfNat α 0] (_f : β → α) (_L : SummationFilter β) : α := 0

/-- Filters, and limits along them. -/
structure Filter (α : Type) where
  sets : Set (Set α)
def Filter.atTop {α : Type} : Filter α := ⟨fun _ => True⟩
def Filter.atBot {α : Type} : Filter α := ⟨fun _ => True⟩
def nhds {X : Type} (_x : X) : Filter X := ⟨fun _ => True⟩
def Filter.Tendsto {α β : Type} (_f : α → β) (_l₁ : Filter α) (_l₂ : Filter β) : Prop := True
def Filter.Eventually {α : Type} (_p : α → Prop) (_f : Filter α) : Prop := True
def Filter.Frequently {α : Type} (_p : α → Prop) (_f : Filter α) : Prop := True

/-- Bundled functions, coerced to functions. -/
class DFunLike (F : Type) (α : Type) (β : Type) where
  coe : F → α → β

/-- Simple graphs, whose projection is `SimpleGraph.Adj`. -/
structure SimpleGraph (V : Type) where
  Adj : V → V → Prop
def SimpleGraph.chromaticNumber {V : Type} (_G : SimpleGraph V) : Nat := 0
def SimpleGraph.maxDegree {V : Type} (_G : SimpleGraph V) : Nat := 0
def SimpleGraph.minDegree {V : Type} (_G : SimpleGraph V) : Nat := 0
def SimpleGraph.cliqueNum {V : Type} (_G : SimpleGraph V) : Nat := 0
def SimpleGraph.edgeFinset {V : Type} (_G : SimpleGraph V) : Finset (V × V) := ⟨[]⟩
def SimpleGraph.Connected {V : Type} (_G : SimpleGraph V) : Prop := True
def SimpleGraph.completeGraph (V : Type) : SimpleGraph V := ⟨fun _ _ => True⟩
def SimpleGraph.cycleGraph (n : Nat) : SimpleGraph (Fin n) := ⟨fun _ _ => True⟩

/-- Polynomials, as coefficient lists. -/
structure Polynomial (R : Type) where
  coeffs : List R
def Polynomial.eval {R : Type} (_x : R) (_p : Polynomial R) : R := _x
def Polynomial.X {R : Type} [OfNat R 0] [OfNat R 1] : Polynomial R := ⟨[0, 1]⟩
def Polynomial.degree {R : Type} (p : Polynomial R) : Nat := p.coeffs.length

/-- Residues, a structure so that a cast into it is a cast. -/
structure ZMod (_n : Nat) where
  val : Int
instance {n : Nat} : NatCast (ZMod n) := ⟨fun a => ⟨a⟩⟩
instance {n : Nat} : IntCast (ZMod n) := ⟨fun a => ⟨a⟩⟩

/-- Classes, for the instance binders the pack states as hypotheses. -/
class Fintype (_α : Type) where
  elems : Nat
class Finite (_α : Type) : Prop where
  finite : True
class Infinite (_α : Type) : Prop where
  infinite : True
class Nontrivial (_α : Type) : Prop where
  nontrivial : True
class Group (G : Type) where
  mul : G → G → G
class CommGroup (G : Type) extends Group G
class AddCommGroup (G : Type) where
  add : G → G → G
class Ring (R : Type) where
  mul : R → R → R
  one : R
/-- An element of a ring, for a statement whose body depends on an instance. -/
def Ring.unit {R : Type} [Ring R] : R := Ring.one
class CommRing (R : Type) extends Ring R
class Field (K : Type) extends CommRing K
class CharZero (_R : Type) : Prop where
  charZero : True
class IsNoetherianRing (_R : Type) : Prop where
  noetherian : True
class IsLocalRing (_R : Type) : Prop where
  local_ : True
class TopologicalSpace (X : Type) where
  IsOpen : Set X → Prop
class MetricSpace (X : Type) where
  dist : X → X → Real
class CompleteSpace (_X : Type) : Prop where
  complete : True
class ConnectedSpace (_X : Type) : Prop where
  connected : True
class NormedAddCommGroup (E : Type) where
  norm : E → Real
class Module (R M : Type) where
  smul : R → M → M
class Module.Finite (_R _M : Type) : Prop where
  finite : True
class FiniteDimensional (_K _V : Type) : Prop where
  finite : True
class Algebra (R A : Type) where
  smul : R → A → A
class NormedSpace (k E : Type) where
  smul : k → E → E
class ChartedSpace (H M : Type) where
  atlas : H → M
class Fact (p : Prop) : Prop where
  out : p
