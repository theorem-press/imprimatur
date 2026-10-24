/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# What the scanner finds

The forms of imprimatur's markup in a TeX file, and the TeX the scanner must
recognise to find them: conditionals and the commands that define others.
Shared by the scanner (`Splice.Core.Scan`) and the code that uses what it
finds.
-/

namespace Splice

/-- The forms of markup (DESIGN §9.1). -/
inductive ItemKind where
  /-- A block environment: `leanblock` or an alias. -/
  | block
  /-- `\leaninline[opts]{key}{content}`. -/
  | inline
  /-- `\leanref[opts]{key}{content}`. -/
  | ref
  /-- `\leancheck[opts]{key, …}`, or blueprint `\lean{key, …}`. -/
  | check
  /-- `\leanindex`. -/
  | index
  /-- Blueprint `\leanok` (DESIGN §9.3), read when `manifests.blueprint` is on. -/
  | leanok
  /-- `\leanhypref{key}{h}`: a reference to hypothesis `h` of a result, so its
  prose view labels `h` (it labels no hypothesis the paper doesn't refer to). -/
  | hypref
  deriving Repr, DecidableEq, Inhabited

/-- One `key=value` option, with the position of its value. -/
structure Opt where
  /-- The key. -/
  key : String
  /-- The value, without surrounding braces. -/
  value : String
  /-- Index of the first character of the value as written. -/
  valueStart : Nat
  /-- One past the last character of the value as written. -/
  valueEnd : Nat
  deriving Repr, Inhabited

/-- One piece of markup in a file. All positions are character indices. -/
structure Item where
  /-- The form. -/
  kind : ItemKind
  /-- The environment or macro name (`leanblock`, `leanlemma`, `leaninline`, …). -/
  name : String
  /-- Index of the opening backslash. -/
  start : Nat
  /-- One past the end of the item. -/
  stop : Nat
  /-- Where `[sum=…]` is inserted when the item has no options. -/
  insertAt : Nat
  /-- Indices of `[` and one past `]`, if there are options. -/
  optsSpan : Option (Nat × Nat) := none
  /-- The options, in order. -/
  opts : Array Opt := #[]
  /-- The key (blocks, inline, ref, hypref). -/
  key : String := ""
  /-- The hypothesis referred to (hypref). -/
  hyp : String := ""
  /-- The keys (check). -/
  keys : Array String := #[]
  /-- The title (blocks). -/
  title : String := ""
  /-- One past the last header argument (blocks). -/
  headerEnd : Nat := 0
  /-- The generated region. -/
  regionStart : Nat := 0
  /-- One past the end of the generated region. -/
  regionEnd : Nat := 0
  /-- Index of `\end` (blocks). -/
  endStart : Nat := 0
  /-- Which LaTeX environment the item is in: an id unique within the file,
  or 0 outside every environment. Pairs blueprint `\leanok` with `\lean{…}`. -/
  env : Nat := 0
  /-- Whether the item is typeset: false inside a conditional branch that is
  off (`\iffalse`, a `\newif` switch set false), or in a file reached only
  from one. Such items are still maintained. -/
  live : Bool := true
  deriving Repr, Inhabited

/-- The value of an option. -/
def Item.opt? (it : Item) (k : String) : Option String :=
  (it.opts.find? (·.key == k)).map (·.value)

/-- What scanning one file finds. -/
structure ScanResult where
  /-- Markup, in order. -/
  items : Array Item := #[]
  /-- Files to follow: the macro, the path as written, its position, and
  whether the input is typeset. -/
  inputs : Array (String × String × Nat × Bool) := #[]
  /-- The typeset `\label{name}`s, with their positions: the document's own
  anchors, which an index view can refer to. -/
  labels : Array (String × Nat) := #[]
  deriving Repr, Inhabited

/-- The switches declared with `\newif`, and their values. They are threaded
through the files of a document, in the order the files are scanned. -/
abbrev Switches := Array (String × Bool)

namespace Scan

/-- Control sequences that start with `if` but are macros taking braced
arguments, not conditionals closed by `\fi` (`ifthen` and `etoolbox`). -/
def notConditionals : List String :=
  ["ifthenelse", "ifstrequal", "ifstrempty", "ifblank", "ifnumequal", "ifnumless",
   "ifnumgreater", "ifnumcomp", "ifnumodd", "ifdimequal", "ifdimless", "ifdimgreater", "ifdimcomp",
   "ifdefempty", "ifdefvoid", "ifcsdef", "ifcsundef", "ifundef", "ifdef", "ifboolexpr",
   "iftoggle", "ifnottoggle", "ifcsstring", "ifdefstring", "ifdefequal", "ifcsequal",
   "ifstrmacro", "ifdefmacro", "ifcsmacro", "ifdefparam", "ifcsparam", "ifdefprefix",
   "ifcsprefix", "ifdefprotected", "ifcsprotected", "ifdefltxprotect", "ifcsltxprotect",
   "ifdefchar", "ifcschar", "ifpatchable", "ifbool", "ifdeflength", "ifcslength",
   "ifdefcounter", "ifcscounter", "ifltxcounter", "ifinlist", "ifinlistcs", "ifrmnum",
   "ifcsvoid", "ifdefmacro", "ifx"]

/-- Commands that define the command named after them. -/
def definingCommands : List String :=
  ["newcommand", "renewcommand", "providecommand", "DeclareRobustCommand",
   "NewDocumentCommand", "RenewDocumentCommand", "ProvideDocumentCommand",
   "DeclareDocumentCommand", "NewExpandableDocumentCommand", "def", "edef", "gdef", "xdef",
   "let", "newenvironment", "renewenvironment", "NewDocumentEnvironment"]

/-- Whether a control sequence opens a TeX conditional (closed by `\fi`).
`\ifx` is one, but takes no part in nesting decisions of its own: it is
listed above only to keep the list honest. -/
def isConditional (name : String) : Bool :=
  name.startsWith "if" && name.length > 2 && (name == "ifx" || !notConditionals.contains name)

end Scan

end Splice
