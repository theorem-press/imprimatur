/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MathlibPack.Stubs

/-! Statements that use every rule of the `mathlib` pack, once each, so the
golden bundle shows each rendering and the read-back of each. -/

namespace MathlibPack

/-- A bundled function, for the coercion to functions. -/
structure Hom where
  f : Nat → Nat
instance : DFunLike Hom Nat Nat := ⟨Hom.f⟩

/-- Types, and the coercions that are not shown. -/
theorem types (x : Real) (z : Complex) (q : Rat) (r : NNReal) (m : PNat) (h : Hom)
    (k : ZMod 7) :
    Rat.cast q = x ∧ NNReal.toReal r = x ∧ PNat.val m = 1 ∧ Real.toEReal x = Real.toEReal x ∧
      DFunLike.coe h 1 = 1 ∧ k = k ∧ z = z := by
  sorry

/-- Functions of the reals and the complex numbers. -/
theorem functions (x y : Real) (z : Complex) (v : Complex) :
    Real.log x = Real.exp (x + 1) ∧ Real.sqrt x < Real.pi ∧ Real.sin x = Real.cos y ∧
      Real.logb 2 x = Real.log (Real.logb x y) ∧ Complex.re z + Complex.im z = Complex.re Complex.I ∧
      abs x = Norm.norm v := by
  sorry

/-- Arithmetic functions. -/
theorem arithmetic (n k : Nat) (x : Real) :
    Nat.factorial (n + 1) = Nat.choose n k * Nat.totient n + Nat.primeCounting n ∧
      Int.floor x + Int.ceil x = Nat.floor x + Nat.ceil x := by
  sorry

/-- Cardinalities. -/
theorem cards (s : Finset Nat) (t : Set Nat) (α : Type) : Finset.card s + Set.ncard t = Fintype.card α := by
  sorry

/-- Predicates, as sentences. -/
theorem predicates (p n m : Nat) (x : Real) (s : Set Nat) (t : Finset Nat) (f : Nat → Nat)
    (G : SimpleGraph Nat) (a b : Int) :
    Nat.Prime p ∧ Odd n ∧ Even m ∧ Irrational x ∧ Squarefree n ∧ IsSquare m ∧
      Set.Infinite s ∧ Set.Finite s ∧ Set.Nonempty s ∧ Finset.Nonempty t ∧
      StrictMono f ∧ Monotone f ∧ Function.Bijective f ∧ SimpleGraph.Connected G ∧ Nat.Coprime n m ∧
      Int.ModEq 7 a b := by
  sorry

/-- Sets and finsets: intervals, set-builder notation, filters. -/
theorem sets (a b : Nat) (s : Finset Nat) (x : Real) :
    (1 ∈ Set.Icc a b) ∧ Finset.card (Finset.Icc a b) = Finset.card (Finset.range b) ∧
      Set.Infinite (Set.ofPred fun n => Nat.Prime n) ∧ Set.Finite (Set.ofPred fun n => n < 5) ∧
      Finset.card (Finset.filter (fun n => n < 5) s) ≤ 5 ∧ x = x := by
  sorry

/-- Sums and products, over a finset, over everything, and infinite. -/
theorem sums (s : Finset Nat) (f : Nat → Real) :
    Finset.sum s (fun i => i) = Finset.sum Finset.univ (fun i : Fin 3 => (i : Nat)) ∧
      Finset.prod s (fun i => i + 1) = Finset.prod Finset.univ (fun i : Fin 3 => (i : Nat)) ∧
      tsum (fun n => f n) (SummationFilter.unconditional Nat) = tsum (fun n => f n) (SummationFilter.unconditional Nat) := by
  sorry

/-- Limits along `atTop`: to a point, to infinity, to minus infinity; what
holds eventually and frequently. -/
theorem limits (f : Nat → Real) (a : Real) :
    Filter.Tendsto (fun n => f n) Filter.atTop (nhds a) ∧
      Filter.Tendsto (fun n => f (2 * n)) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n => -f n) Filter.atTop Filter.atBot ∧
      Filter.Eventually (fun n => a < f n) Filter.atTop ∧
      Filter.Frequently (fun n => f n < a) Filter.atTop := by
  sorry

/-- Graphs. -/
theorem graphs (G : SimpleGraph Nat) (u v : Nat) :
    SimpleGraph.chromaticNumber G ≤ SimpleGraph.maxDegree G + 1 ∧
      SimpleGraph.minDegree G ≤ SimpleGraph.cliqueNum G ∧
      Finset.card (SimpleGraph.edgeFinset G) = 3 ∧
      SimpleGraph.Adj G u v ∧ SimpleGraph.completeGraph Nat = G ∧
      SimpleGraph.cycleGraph 5 = SimpleGraph.cycleGraph 5 := by
  sorry

/-- Polynomials. -/
theorem polynomials (p : Polynomial Nat) (x : Nat) :
    Polynomial.eval x p = Polynomial.eval x Polynomial.X ∧ Polynomial.degree p ≤ 2 := by
  sorry

end MathlibPack
