import Shapes
import Imprimatur

/-! The paper's notation, outside the host project (external mode). -/

open Shapes

latex_notation Rect.area r => r"|#r|"
latex_notation Rect.mk w h => r"#w \times #h"
latex_notation Rect.w r => r"#r_{\mathrm{w}}"
latex_notation Rect.h r => r"#r_{\mathrm{h}}"
