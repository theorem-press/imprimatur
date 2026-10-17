/-! A tiny development for the end-to-end example. -/

namespace Minimal

/-- Double a natural number. -/
def double (n : Nat) : Nat := n + n

/-- Doubling distributes over addition. -/
theorem double_add (m n : Nat) : double (m + n) = double m + double n := by
  unfold double
  omega

/-- Doubling is injective, for all `m` and `n`: if `double m = double n` then
`m = n`. -/
theorem double_injective {m n : Nat} (h : double m = double n) : m = n := by
  unfold double at h
  omega

end Minimal
