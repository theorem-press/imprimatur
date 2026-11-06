import Shapes

/-- The host's executable: a module named `Main`, as the extractor's own is.
The paper cites this one. -/
def main : IO Unit :=
  IO.println (Shapes.Rect.area { w := 3, h := 4 })
