/-! The host's development. -/

namespace Host

/-- Reverse a list onto an accumulator. -/
def revAcc {α : Type} : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

/-- `revAcc` agrees with `List.reverse`. -/
theorem revAcc_eq {α : Type} (xs acc : List α) : revAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [revAcc]
  | cons x xs ih => simp [revAcc, ih]

end Host
