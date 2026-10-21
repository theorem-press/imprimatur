/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Diagnostics

Every error and warning the splicer reports has a stable code, so tests and
CI scripts can rely on it (CONTRIBUTING.md, principle 5).
-/

namespace Splice

/-- How serious a diagnostic is. Errors make `check` and `apply` fail;
warnings don't (DESIGN §10.3). -/
inductive Severity where
  /-- Fails the command. -/
  | error
  /-- Reported only. -/
  | warning
  deriving Repr, BEq, Inhabited

/-- A diagnostic. -/
structure Diag where
  /-- Error or warning. -/
  severity : Severity
  /-- A stable code, such as `hand-edit` or `missing-key`. -/
  code : String
  /-- `path:line:col`, or empty for diagnostics about the whole run. -/
  loc : String
  /-- What is wrong, and what to do about it. -/
  message : String
  deriving Repr, Inhabited

/-- An error. -/
def Diag.err (code loc message : String) : Diag :=
  { severity := .error, code, loc, message }

/-- A warning. -/
def Diag.warn (code loc message : String) : Diag :=
  { severity := .warning, code, loc, message }

/-- The diagnostic as one line of output (continuation lines indented). -/
def Diag.render (d : Diag) : String :=
  let sev := match d.severity with | .error => "error" | .warning => "warning"
  let pre := if d.loc.isEmpty then "" else d.loc ++ ": "
  let msg := "\n  ".intercalate (d.message.splitOn "\n")
  s!"{pre}{sev}[{d.code}]: {msg}"

/-- Whether any diagnostic is an error. -/
def hasErrors (ds : Array Diag) : Bool :=
  ds.any (·.severity == .error)

end Splice
