/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Version information
-/

namespace Splice

/-- The version of the splicer. -/
def version : String := "0.0.0"

/-- The bundle schemas this splicer reads: the current and the previous
major version (DESIGN §13). -/
def acceptedSchemas : List String := ["imprimatur-bundle/1"]

end Splice
