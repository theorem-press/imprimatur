/-! Rectangles with natural-number sides. -/

namespace Shapes

/-- A rectangle. -/
structure Rect where
  /-- Width. -/
  w : Nat
  /-- Height. -/
  h : Nat

/-- The area of a rectangle. -/
def Rect.area (r : Rect) : Nat := r.w * r.h

/-- Swapping the sides keeps the area. -/
theorem Rect.area_swap (r : Rect) : (Rect.mk r.h r.w).area = r.area := by
  unfold Rect.area
  exact Nat.mul_comm _ _

end Shapes
