/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Data.HashMap
import Imprimatur.Doc
import Imprimatur.Commands
import Imprimatur.TeX

/-!
# Translation validation of renderings

DESIGN §18.3–§18.4. A rendering is *faithful* when a reader who knows the
paper's notation reads it back as the expression it came from. This module
reads it back: the notation in scope is a grammar over TeX tokens, and a
rendered formula is checked to have exactly one reading.

**The grammar.** Each notation rule is a production (`ofRule`): its
template's tokens are terminals, and its holes are nonterminals of the sort
of their variables, at the precedence the emitter (`Doc.render`) gives them.
Built-in forms (`∀`, `∃`, `→`, `λ`, application) are productions too, and so
are the formula's variables, numerals and other atoms. The emitter's
parentheses are a production of every sort.

**Sorts** are Lean types, as `sortKey` writes them. `*` is unknown and
matches every sort. `?α` is a rule's type variable: its holes must agree,
and the first that is filled binds it. Function sorts are compared part by
part.

**Readings** are trees, named by the shapes of the rules' patterns, with the
children in the patterns' order. Two parses are the same reading when they
are the same tree: coercions (templates that are a bare hole,
`Option.some x => #x`) do not appear in it, a chain's operands are never
the same chain, and synonyms are not productions. `readBack` finds up to two.

- one reading: the rendering is faithful;
- two: it is *ambiguous*, and a reader cannot tell which is meant;
- none: the grammar does not cover the formula (an unmodelled form), and it
  is *not validated*.
-/

namespace Imprimatur.Validate

/-! ## Tokens -/

/-- TeX tokens: control words (`\vdash`), control symbols (`\,`, `\{`,
`\ `), and single characters; spaces separate tokens and are dropped.
`\LeanMathCode{…}`, Lean's own rendering of what has no notation, is one
opaque token, and `\LeanBreak` (a line break) is dropped. -/
def tokenize (s : String) : Array String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array String := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == ' ' || c == '\n' || c == '\t' then
      i := i + 1
    else if c == '\\' then
      let mut j := i + 1
      while j < cs.size && cs[j]!.isAlpha do j := j + 1
      if j == i + 1 then
        -- A control symbol: one character after the backslash.
        out := out.push (String.ofList [c, cs.getD (i + 1) ' '])
        i := i + 2
      else
        let name := String.ofList (cs.extract (i + 1) j).toList
        if name == "LeanMathCode" && cs.getD j ' ' == '{' then
          -- One opaque token, to the matching brace.
          let mut k := j + 1
          let mut depth := 1
          while k < cs.size && depth > 0 do
            if cs[k]! == '\\' then k := k + 2; continue
            if cs[k]! == '{' then depth := depth + 1
            if cs[k]! == '}' then depth := depth - 1
            k := k + 1
          out := out.push (String.ofList (cs.extract i k).toList)
          i := k
        else
          unless name == "LeanBreak" do out := out.push ("\\" ++ name)
          i := j
    else
      out := out.push c.toString
      i := i + 1
  return out

/-! ## The grammar -/

/-- A symbol of a production. -/
inductive Sym where
  /-- A terminal. -/
  | tok (t : String)
  /-- An expression of a sort, at a minimum precedence. -/
  | hole (sort : String) (prec : Nat)
  /-- A bound variable's name. -/
  | var
  /-- One or more repetitions of `elem`, separated by `sep`, at least `min`. -/
  | list (elem : Array Sym) (sep : Array String) (min : Nat)
  deriving Inhabited, Repr

/-- A production: what it reads as, its sort and precedence, its symbols. -/
structure Prod where
  /-- What it reads as (a constant, a built-in form), for messages. -/
  name : String
  /-- The sort of what it produces. -/
  sort : String
  /-- Its precedence. -/
  prec : Nat
  /-- Its symbols. -/
  syms : Array Sym
  /-- A coercion: one hole, and the result has that hole's precedence. -/
  coercion : Bool := false
  /-- An atom that is a variable's name. -/
  isVar : Bool := false
  /-- A flattened chain (`flatten`), which the notation declares
  associative: its operands are never the same chain. -/
  chain : Bool := false
  /-- For a rule's production without lists, the position in the pattern
  of each child, in the order the template shows them. -/
  order : Option (Array Nat) := none
  deriving Inhabited, Repr

/-- A sort that is a rule's type variable (`?α`): its holes of that sort
must agree (DESIGN §18.3). -/
def isTyVar (s : String) : Bool := s.startsWith "?"

/-- A sort as a term: a function sort `(A → B)`, and a type applied to type
arguments `Option(Label)`, have parts. -/
inductive STerm where
  /-- A sort without parts. -/
  | atom (s : String)
  /-- A function sort. -/
  | arrow (a b : STerm)
  /-- A type constant applied to types. -/
  | app (head : String) (args : Array STerm)
  deriving Inhabited, BEq

/-- Split at the commas that are not nested in parentheses. -/
def splitTop (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  for c in s.toList do
    if c == '(' then depth := depth + 1
    if c == ')' then depth := depth - 1
    if c == ',' && depth == 0 then
      out := out.push cur.trimAscii.toString
      cur := ""
    else cur := cur.push c
  return out.push cur.trimAscii.toString

/-- Read a sort (`sortKey`'s format). -/
partial def STerm.parse (s : String) : STerm := Id.run do
  if s.startsWith "(" && s.endsWith ")" then
    let cs := ((s.drop 1).dropEnd 1).toString.toList.toArray
    let mut depth := 0
    for i in [0:cs.size] do
      let c := cs[i]!
      if c == '(' then depth := depth + 1
      else if c == ')' then depth := depth - 1
      else if c == '→' && depth == 0 && i ≥ 1 then
        let l := String.ofList (cs.extract 0 (i - 1)).toList
        let r := String.ofList (cs.extract (i + 2) cs.size).toList
        return .arrow (STerm.parse l) (STerm.parse r)
  if s.endsWith ")" then
    if let some k := s.toList.findIdx? (· == '(') then
      if k > 0 then
        let head := String.ofList (s.toList.take k)
        let inner := String.ofList ((s.toList.drop (k + 1)).dropLast)
        return .app head ((splitTop inner).map STerm.parse)
  return .atom s

/-- Write a sort back. -/
partial def STerm.render : STerm → String
  | .atom s => s
  | .arrow a b => s!"({a.render} → {b.render})"
  | .app h as => s!"{h}({", ".intercalate (as.map STerm.render).toList})"

/-- Sorts compatible, the first found where the second is expected: equal up
to unknowns (`*`, and type variables, which are unknown until bound), part
by part. A type written without its arguments (as the packs write `Option`)
stands for it with any. -/
partial def STerm.compat : STerm → STerm → Bool
  -- A proposition is a type.
  | .atom a, .atom b => a == b || unknown a || unknown b || univFits a b
  | .app h as, .app h' bs =>
    h == h' && (as.size != bs.size || (as.zip bs).all fun (x, y) => x.compat y)
  | .app h _, .atom b => unknown b || h == b
  | .atom a, .app h _ => unknown a || a == h
  -- What is found (on the left) may be of a named type that is a function
  -- type by definition (`Matrix R C α` is `R → C → α`), which the reader does
  -- not unfold; but a function is not of a named type.
  | .atom a, .arrow .. => unknown a || named a
  | .app .., .arrow .. => true
  | .arrow .., .atom b => unknown b
  | .arrow .., .app .. => false
  | .arrow a b, .arrow c d => a.compat c && b.compat d
where
  unknown (s : String) : Bool := s == "*" || s.startsWith "?"
  -- Propositions and types: a universe (`Sort*` is one that may be `Prop`).
  univ (s : String) : Bool := s == "Prop" || s == "Sort" || s == "Sort*"
  -- A proposition is read where a type is expected, and `Sort*` (either) is
  -- read where either is; but a type is not a proposition.
  univFits (a b : String) : Bool :=
    (a == "Prop" && (b == "Sort" || b == "Sort*")) || (a == "Sort" && b == "Sort*") ||
    (a == "Sort*" && (b == "Prop" || b == "Sort"))
  named (s : String) : Bool := !univ s && !s.startsWith "'"

/-- Sorts compatible (see `STerm.compat`). -/
def compat (a b : String) : Bool :=
  a == b || a == "*" || b == "*" || isTyVar a || isTyVar b || (STerm.parse a).compat (STerm.parse b)

/-- The productions of the built-in forms of `Render.render`. An applied
variable is written `f(a)` or `f_{a}` only under the style that asks for it
(`latex_style applied_variables`), so those forms are read only then. -/
def builtins (call subscript : Bool := false) (cases : Bool := false) (lists : Bool := false) :
    Array Prod :=
  let forms : Array Prod := #[
  { name := "implication", sort := "Prop", prec := 25,
    syms := #[.hole "Prop" 26, .tok "\\implies", .hole "Prop" 25] },
  { name := "function type", sort := "Sort", prec := 25,
    syms := #[.hole "Sort" 26, .tok "\\to", .hole "Sort" 25] },
  { name := "∀", sort := "Prop", prec := 0,
    syms := #[.tok "\\forall", .var, .tok ":", .hole "Sort" 1, .tok ",", .tok "\\ ", .hole "Prop" 0] },
  -- A dependent function type, written the same way; the same reading.
  { name := "∀", sort := "Sort", prec := 0,
    syms := #[.tok "\\forall", .var, .tok ":", .hole "Sort" 1, .tok ",", .tok "\\ ", .hole "Sort" 0] },
  { name := "bounded ∀", sort := "Prop", prec := 0,
    syms := #[.tok "\\forall", .var, .tok "\\in", .hole "*" 50, .tok ",", .tok "\\ ", .hole "Prop" 0] },
  { name := "∃", sort := "Prop", prec := 0,
    syms := #[.tok "\\exists", .var, .tok ",", .tok "\\ ", .hole "Prop" 0] },
  { name := "bounded ∃", sort := "Prop", prec := 0,
    syms := #[.tok "\\exists", .var, .tok "\\in", .hole "*" 50, .tok ",", .tok "\\ ", .hole "Prop" 0] },
  { name := "λ", sort := "*", prec := 0,
    syms := #[.tok "\\lambda", .var, .tok ".", .tok "\\,", .hole "*" 0] },
  { name := "application", sort := "*", prec := Doc.maxPrec - 1,
    syms := #[.hole "*" Doc.maxPrec, .list #[.tok "\\,", .hole "*" Doc.maxPrec] #[] 1] }]
  let callForm : Prod :=
  { name := "application f(a)", sort := "*", prec := Doc.maxPrec,
    syms := #[.hole "*" Doc.maxPrec, .list #[.tok "(", .hole "*" 0, .tok ")"] #[] 1] }
  let subscriptForm : Prod :=
  { name := "application f_{a}", sort := "*", prec := Doc.maxPrec,
    syms := #[.hole "*" Doc.maxPrec, .tok "_", .tok "{",
      .list #[.hole "*" 0] #[","] 1, .tok "}"] }
  -- `latex_style pattern_matching := cases`: a case analysis.
  let caseForm : Prod :=
  { name := "case", sort := "*", prec := 0,
    syms := (tokenize "\\mathsf{case}\\ ").map .tok ++
      #[.list #[.hole "*" 1] #[",", "\\ "] 1] ++ (tokenize "\\ \\mathsf{of}\\ ").map .tok ++
      #[.list #[.list #[.hole "*" 1] #[",", "\\ "] 1, .tok "\\Rightarrow", .hole "*" 1] #["\\mid"] 1] }
  -- `latex_style lists := literal`: a list literal.
  let listForm : Prod :=
  { name := "list", sort := "List(*)", prec := Doc.maxPrec,
    syms := #[.tok "[", .list #[.hole "*" 0] #[",", "\\ "] 1, .tok "]"] }
  forms ++ (if call then #[callForm] else #[]) ++ (if subscript then #[subscriptForm] else #[]) ++
    (if cases then #[caseForm] else #[]) ++ (if lists then #[listForm] else #[])

/-- The shape of a pattern, without its variables' names: a reading names
the expression a rule matches by its pattern's shape, so two rules for the
same expressions (a variant's, a pack's) give the same reading. -/
partial def _root_.Imprimatur.Pat.shape : Pat → String
  | .var _ | .wild => "_"
  | .app h args =>
    if args.all (fun | .var _ | .wild => true | _ => false) then h.toString
    else s!"({h} {" ".intercalate (args.map Pat.shape).toList})"
  | .lit e => s!"{e}"
  | .constrained p cs => s!"{p.shape}\{{", ".intercalate (cs.map fun (i, c) => s!"{i}:{c.shape}").toList}}"
  | .lam _ b => s!"(fun _ => {b.shape})"
  | .pi _ d b => s!"(∀ _ : {d.shape}, {b.shape})"
  | .arrow d c => s!"({d.shape} → {c.shape})"

/-- The production of a notation rule. It mirrors `Render.fillTemplate`:
the template's text is terminals; a shown variable is a hole of its sort,
at the precedence the emitter needs there (none inside braces or in an
atomic template; the rule's own on the side its associativity allows, one
more elsewhere); a flattened chain repeats its second operand after the
separator; a folded binder's variable is a list, each of its own type. A
rule that shows one variable and nothing else is a coercion; a synonym has
no production. -/
def ofRule (r : NotationRule) : Option Prod := Id.run do
  if r.synonym then return none
  let vars := r.pat.vars.map (·.toString)
  let name := r.pat.shape
  let some parts := (splitTemplate r.template vars).toOption | return none
  let hidden := r.hides.map (·.1.toString)
  let sortOf (v : String) : String := ((r.holeSorts.find? (·.1.toString == v)).map (·.2)).getD "*"
  let topCount := Id.run do
    let mut d := 0
    let mut n := 0
    for p in parts do
      match p with
      | .inl t => d := TeX.braceDepth t d
      | .inr _ => if d == 0 then n := n + 1
    return n
  let chain := r.flatten && r.pat.binder?.isNone
  let folded : Option String := if r.flatten then r.pat.binder?.map (·.1.toString) else none
  let mut syms : Array Sym := #[]
  let mut depth := 0
  let mut holeIdx := 0
  let mut topIdx := 0
  let mut chainSep : Array String := #[]
  let mut shownVars : Array String := #[]
  let mut partIdx := 0
  for p in parts do
    partIdx := partIdx + 1
    match p with
    | .inl t =>
      let ts := tokenize t
      if chain && holeIdx == 1 && chainSep.isEmpty then chainSep := ts
      syms := syms ++ ts.map .tok
      depth := TeX.braceDepth t depth
    | .inr v =>
      if hidden.contains v then
        holeIdx := holeIdx + 1
        continue
      -- The precedence the hole needs: the renderer's own policy.
      let need := Doc.holeNeeds r.prec r.assoc depth (partIdx == 1 || partIdx == parts.size)
        (topIdx == 0) (topIdx + 1 == topCount)
      -- A chain's operands may each be of their own type (a tuple
      -- `(a, b, c)`), so a type variable among them is left open.
      let so := sortOf v
      let so := if chain && so.contains '?' then "*" else so
      let hole := Sym.hole so need
      shownVars := shownVars.push v
      if chain && holeIdx == 1 then
        syms := syms.push (.list #[hole] chainSep 1)
      else if folded == some v then
        -- The variables of a fold each have their own type.
        syms := syms.push (.list #[.hole "*" need] (tokenize r.sep) 1)
      else
        syms := syms.push hole
      holeIdx := holeIdx + 1
      if depth == 0 then topIdx := topIdx + 1
  let coercion := match syms with
    | #[.hole ..] => true
    | _ => false
  let hasList := syms.any fun | .list .. => true | _ => false
  let order := if hasList then none else some (shownVars.map fun v => vars.idxOf v)
  -- Likewise the sort of a chain whose type the pattern leaves open is known
  -- only by its head (`Prod`).
  let sort := if chain && r.sort.contains '?' then (r.sort.splitOn "(")[0]! else r.sort
  return some { name, sort, prec := r.prec, syms, coercion, chain, order }

/-! ## Counting readings -/

/-- A symbol after compilation: lists become their first element followed
by a *tail*, a nonterminal for the rest. -/
inductive ASym where
  /-- A terminal. -/
  | tok (t : String)
  /-- An expression of a sort, at a minimum precedence, other than one
  made by production `excl` (an operand of a chain). -/
  | hole (sort : String) (prec : Nat) (excl : Option Nat := none)
  /-- A bound variable's name. -/
  | var
  /-- The rest of list `l`, with `r` more elements required. -/
  | tail (l : Nat) (r : Nat)
  deriving Inhabited, Repr, BEq, Hashable

/-- A compiled grammar. -/
structure Grammar where
  /-- The productions, with their compiled bodies. -/
  prods : Array (Prod × Array ASym)
  /-- The lists: element and separator, compiled. -/
  lists : Array (Array ASym × Array ASym)

/-- Compile symbols, collecting lists. The holes of a chain (production
`chain`) exclude it. -/
partial def compile (syms : Array Sym) (lists : Array (Array ASym × Array ASym))
    (chain : Option Nat := none) :
    Array ASym × Array (Array ASym × Array ASym) := Id.run do
  let mut out : Array ASym := #[]
  let mut lists := lists
  for s in syms do
    match s with
    | .tok t => out := out.push (.tok t)
    | .hole so p => out := out.push (.hole so p chain)
    | .var => out := out.push .var
    | .list elem sep min =>
      let (e, ls) := compile elem lists chain
      lists := ls
      let idx := lists.size
      lists := lists.push (e, sep.map ASym.tok)
      out := out ++ e
      out := out.push (.tail idx (min - 1))
  return (out, lists)

/-- Add productions to a grammar. -/
def Grammar.extend (g : Grammar) (ps : Array Prod) : Grammar := Id.run do
  let mut lists := g.lists
  let mut prods := g.prods
  for p in ps do
    let (b, ls) := compile p.syms lists (if p.chain then some prods.size else none)
    lists := ls
    prods := prods.push (p, b)
  return { prods, lists }

/-- Compile productions into a grammar. -/
def Grammar.of (ps : Array Prod) : Grammar := Grammar.extend { prods := #[], lists := #[] } ps

/-- The grammar of the notation in scope, for a notation variant: its rules
and the built-in forms. A formula's atoms are added to it (`Grammar.extend`). -/
def notationGrammar (rules : Array NotationRule) (variant : Option String) (call subscript : Bool)
    (cases lists : Bool := false) : Grammar :=
  let rules := rules.filter fun r => r.variant.isNone || r.variant == variant
  Grammar.of (rules.filterMap ofRule ++ builtins call subscript cases lists)

/-- A binding of a production's type variables to sorts. -/
abbrev Env := Array (String × String)

/-- What the reader remembers. -/
structure CState where
  /-- Readings of a nonterminal, with their sorts, by sort, precedence,
  excluded production and span. -/
  memo : Std.HashMap (String × Nat × Option Nat × Nat × Nat) (Array (String × String)) := {}
  /-- Readings of a suffix of a body: its children's readings, and the
  type variables bound, by body, position, bindings and span. -/
  memoSeq : Std.HashMap (String × Nat × Env × Nat × Nat) (Array (Array String × Env)) := {}
  /-- Nonterminals being read, to cut coercion cycles. -/
  active : Std.HashMap (String × Nat × Option Nat × Nat × Nat) Unit := {}
  /-- Work done, against a budget. -/
  steps : Nat := 0
  /-- Whether to log what is read (`IMPRIMATUR_VALIDATE_DEBUG`). -/
  trace : Bool := false
  /-- The log. -/
  log : Array String := #[]
  /-- `reachable`, by sort: those that start with a token, by the token,
  and the others. -/
  reach : Std.HashMap String (Std.HashMap String (Array Nat) × Array Nat) := {}

/-- The reader's monad. -/
abbrev CountM := StateM CState

/-- The readings to keep of a list: at most two different readings (by
`key`; two readings that are written the same are the same reading), each
with up to 32 different sorts or bindings (by `variant`), since a reading
can be of several sorts (an atom, or the same atom through a coercion). A
variant that is `top` (an unknown sort, no bindings) is as good as any other
for what follows, so it stands alone. -/
def keep2 {α : Type} (key : α → String) (variant : α → String) (xs : Array α)
    (top : String := "*") : Array α := Id.run do
  let mut out : Array α := #[]
  let mut keys : Array String := #[]
  for x in xs do
    let k := key x
    if !keys.contains k then
      if keys.size ≥ 2 then continue
      keys := keys.push k
    if out.any (fun y => key y == k && variant y == top) then continue
    if variant x == top then
      out := (out.filter (key · != k)).push x
      continue
    if (out.filter (key · == k)).size ≥ 32 then continue
    unless out.any (fun y => key y == k && variant y == variant x) do out := out.push x
  return out

/-- The number of different readings among some. -/
def distinct {α : Type} (key : α → String) (xs : Array α) : Nat :=
  (xs.foldl (fun (acc : Array String) x => if acc.contains (key x) then acc else acc.push (key x)) #[]).size

/-- The work budget: past it, a formula is not validated. -/
def budget : Nat := 3000000

section
variable (g : Grammar) (ts : Array String)

/-- The productions that can make an expression of sort `s`: those of a
compatible sort, coercions included. A bound variable's name is not an
expression, so is not among them. -/
def reachable (s : String) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:g.prods.size] do
    let (p, _) := g.prods[i]!
    if !p.isVar && compat p.sort s then out := out.push i
  return out

/-- The productions that are application. -/
def appNames : List String :=
  ["application", "application f(a)", "application f_{a}", "DFunLike.coe", "CoeFun.coe"]

/-- A reading: the production's name, with its children's readings, in the
order of the rule's pattern. -/
def reading (p : Prod) (children : Array String) : String :=
  let children := match p.order with
    | some o =>
      if o.size == children.size then
        ((o.zip children).toList.mergeSort (fun (a b : Nat × String) => a.1 ≤ b.1)).toArray.map
          (fun (x : Nat × String) => x.2)
      else children
    | none => children
  -- Application, however written, is one reading: `f\,a`, `f(a)`, `f_{a}`,
  -- and `⇑f a` through the coercion to a function, which is invisible; and
  -- `f(a)(b)` is `f` applied to `a` and `b`.
  if appNames.contains p.name then
    let (f, rest) := match children[0]? with
      | some c =>
        if c.startsWith "app[" then
          let inner := ((c.drop 4).dropEnd 1).toString
          (inner, children.extract 1 children.size)
        else (c, children.extract 1 children.size)
      | none => ("", #[])
    -- A constant applied is the constant's own reading: `\mathsf{inr}\,y`
    -- by a rule for `Sum.inr` alone and by one for `Sum.inr j` is one term.
    if !f.contains '[' && f.contains '.' && !f.contains '\\' then
      s!"{f}[{"; ".intercalate rest.toList}]"
    else s!"app[{"; ".intercalate (f :: rest.toList)}]"
  else if children.isEmpty then p.name else s!"{p.name}[{"; ".intercalate children.toList}]"

/-- The reading of a form the renderer does not say how to read: it matches
any reading. -/
def anyReading : String := "⁇"

/-- A reading matches what was expected (`expected`, with `anyReading` for any
subterm). -/
partial def readingMatches (expected found : String) : Bool :=
  go expected.toList found.toList
where
  /-- Match, with `⁇` matching any balanced subterm. -/
  go : List Char → List Char → Bool
    | [], g => g.isEmpty
    | '⁇' :: e, g => Id.run do
      -- The subterm ends at the first `;` or `]` outside its own brackets,
      -- or at the end.
      let mut depth := 0
      let mut rest := g
      let mut taken := 0
      for c in g do
        if depth == 0 && (c == ';' || c == ']') then
          return taken > 0 && go e rest
        if c == '[' then depth := depth + 1
        if c == ']' then depth := depth - 1
        rest := rest.tail
        taken := taken + 1
      return depth == 0 && taken > 0 && go e rest
    | c :: e, d :: g => c == d && go e g
    | _ :: _, [] => false

/-- The sort a hole expects, under the type variables bound so far. -/
partial def expected (env : Env) (s : String) : String :=
  if !s.contains '?' then s
  else if isTyVar s then ((env.find? (·.1 == s)).map (·.2)).getD "*"
  else
    let rec go : STerm → STerm
      | .atom a =>
        if isTyVar a then STerm.parse (((env.find? (·.1 == a)).map (·.2)).getD "*") else .atom a
      | .arrow a b => .arrow (go a) (go b)
      | .app h as => .app h (as.map go)
    (go (STerm.parse s)).render

/-- Bind a hole's type variables to the parts of the sort of what fills it. -/
partial def bind (env : Env) (s found : String) : Env :=
  if !s.contains '?' then env
  else
    let rec go (env : Env) : STerm → STerm → Env
      | .atom a, f =>
        let fr := f.render
        if isTyVar a && fr != "*" && !isTyVar fr && !env.any (·.1 == a) then env.push (a, fr) else env
      | .arrow a b, .arrow c d => go (go env a c) b d
      | .app h as, .app h' bs =>
        if h == h' && as.size == bs.size then (as.zip bs).foldl (fun e (x, y) => go e x y) env else env
      | _, _ => env
    go env (STerm.parse s) (STerm.parse found)

mutual
  /-- Readings of `ts[i:j]` as an expression of sort `s` at precedence `p`,
  not made by production `excl`, with their sorts: at most two. -/
  partial def expr (s : String) (p : Nat) (excl : Option Nat) (i j : Nat) :
      CountM (Array (String × String)) := do
    if i ≥ j then return #[]
    let key := (s, p, excl, i, j)
    if let some n := (← get).memo[key]? then return n
    if (← get).active.contains key then return #[]
    modify fun st => { st with active := st.active.insert key (), steps := st.steps + 1 }
    let (byTok, others) ← match (← get).reach[s]? with
      | some r => pure r
      | none =>
        let mut byTok : Std.HashMap String (Array Nat) := {}
        let mut others := #[]
        for k in reachable g s do
          match g.prods[k]!.2[0]? with
          | some (ASym.tok t) => byTok := byTok.insert t ((byTok.getD t #[]).push k)
          | _ => others := others.push k
        modify fun st => { st with reach := st.reach.insert s (byTok, others) }
        pure (byTok, others)
    let known := s != "*" && !isTyVar s
    let mut out : Array (String × String) := #[]
    -- Every production is tried, even after two readings: a reading found
    -- again can be of another sort, which a hole's binding may need.
    let cands := byTok.getD ts[i]! #[] ++ others
    for k in cands do
      if excl == some k then continue
      let (pr, body) := g.prods[k]!
      if pr.coercion then continue
      if pr.prec < p then continue
      -- A body that starts or ends with a token must match it.
      if let some (ASym.tok t) := body[0]? then
        if ts[i]! != t then continue
      if let some (ASym.tok t) := body.back? then
        if ts[j - 1]! != t then continue
      for (cs, env) in ← seq s!"p{k}" body 0 #[] i j do
        -- The sort of the reading: the production's, under its bindings.
        let so := expected env pr.sort
        if !compat so s then continue
        out := keep2 (·.1) (·.2) (out.push (reading pr cs, if known then s else so))
    -- Coercions are invisible: a reading through one is its argument's, at
    -- the precedence asked for, and its sort is the coercion's, with the
    -- argument's sort bound (`Option.some` of a label is an `Option(Label)`).
    -- An argument of the sort asked for is among the readings above, and
    -- others are read afresh.
    for k in cands do
      let (pr, body) := g.prods[k]!
      if !pr.coercion then continue
      let some (ASym.hole s' _ _) := body[0]? | continue
      let es' := expected #[] s'
      let args ← if es' == s then pure out else expr es' p none i j
      for (r, so) in args do
        let sort := expected (bind #[] s' so) pr.sort
        if !compat sort s then continue
        out := keep2 (·.1) (·.2) (out.push (r, if known then s else sort))
    -- The emitter's parentheses, and its TeX groups (`{k_{1}}_{x}`), which
    -- do not print.
    if distinct (·.1) out < 2 && j - i ≥ 3 && ts[i]! == "(" && ts[j - 1]! == ")" then
      out := keep2 (·.1) (·.2) (out ++ (← expr s 0 none (i + 1) (j - 1)))
    if distinct (·.1) out < 2 && j - i ≥ 3 && ts[i]! == "{" && ts[j - 1]! == "}" then
      out := keep2 (·.1) (·.2) (out ++ (← expr s p none (i + 1) (j - 1)))
    modify fun st => { st with memo := st.memo.insert key out, active := st.active.erase key }
    if (← get).trace then
      modify fun st => { st with log := st.log.push s!"{s} @{p} [{i},{j}) {ts.extract i j}: {out}" }
    return out

  /-- Readings of `ts[i:j]` as a bound variable's name. -/
  partial def var (i j : Nat) : CountM (Array String) := do
    for (pr, body) in g.prods do
      if pr.isVar && body.size == j - i &&
          (List.range body.size).all (fun d => body[d]! == ASym.tok ts[i + d]!) then
        return #[pr.name]
    return #[]

  /-- Readings of `ts[i:j]` as `body[pos:]` (of production or list `id`)
  under bindings `env`: the readings of its holes, variables and lists, and
  the bindings after them. -/
  partial def seq (id : String) (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) :
      CountM (Array (Array String × Env)) := do
    if (← get).steps > budget then return #[]
    if pos == body.size then return if i == j then #[(#[], env)] else #[]
    let key := (id, pos, env, i, j)
    if let some n := (← get).memoSeq[key]? then return n
    modify fun st => { st with steps := st.steps + 1 }
    let n ← match body[pos]! with
      | .tok t => if i < j && ts[i]! == t then seq id body (pos + 1) env (i + 1) j else pure #[]
      | .hole s p x =>
        split (fun env a b => do
            return (← expr (expected env s) p x a b).map fun (r, so) => (#[r], bind env s so))
          id body pos env i j
      | .var => split (fun env a b => do return (← var a b).map (#[·], env)) id body pos env i j
      | .tail l r => split (fun env a b => tail l r env a b) id body pos env i j
    modify fun st => { st with memoSeq := st.memoSeq.insert key n }
    return n

  /-- Readings of `ts[i:j]` as a nonterminal then `body[pos+1:]`. -/
  partial def split (nt : Env → Nat → Nat → CountM (Array (Array String × Env))) (id : String)
      (body : Array ASym) (pos : Nat) (env : Env) (i j : Nat) : CountM (Array (Array String × Env)) := do
    if pos + 1 == body.size then return ← nt env i j
    let mut out : Array (Array String × Env) := #[]
    -- What follows the nonterminal, if a token, must be where it ends.
    let next : Option String := match body[pos + 1]! with
      | .tok t => some t
      | _ => none
    -- Only the rest of a list can be empty.
    let start := match body[pos]! with
      | .tail .. => i
      | _ => i + 1
    for m in [start:j + 1] do
      if let some t := next then
        if ts[m]? != some t then continue
      for (as, env₁) in ← nt env i m do
        for (rest, env₂) in ← seq id body (pos + 1) env₁ m j do
          out := keep2 (fun (cs, _) => toString cs) (fun (_, e) => toString e) (out.push (as ++ rest, env₂)) (top := "#[]")
    return out

  /-- Readings of `ts[i:j]` as the rest of list `l`, `r` more required. -/
  partial def tail (l r : Nat) (env : Env) (i j : Nat) : CountM (Array (Array String × Env)) := do
    let (elem, sep) := g.lists[l]!
    let mut out : Array (Array String × Env) := if r == 0 && i == j then #[(#[], env)] else #[]
    if i < j then
      let more := sep ++ elem ++ #[ASym.tail l (r - 1)]
      out := keep2 (fun (cs, _) => toString cs) (fun (_, e) => toString e) (out ++ (← seq s!"t{l}.{r}" more 0 env i j)) (top := "#[]")
    return out
end

/-- The readings of a whole formula as sort `s`: at most two. -/
def readings (s : String) : CountM (Array String) := do
  let rs := (← expr g ts s 0 none 0 ts.size).map (·.1)
  return rs.foldl (fun acc r => if acc.contains r then acc else acc.push r) #[]

end

/-- The readings (at most two) of a token sequence as an expression of sort
`s`, and whether the budget ran out. -/
def readBack (g : Grammar) (ts : Array String) (s : String) : Array String × Bool :=
  let (rs, st) := (readings g ts s).run {}
  (rs, st.steps > budget)

/-- `readBack`, with a log of what was read where. -/
def readBackLog (g : Grammar) (ts : Array String) (s : String) : Array String × Array String :=
  let (rs, st) := (readings g ts s).run { trace := true }
  (rs, st.log)

/-- The number of readings (0, 1, or 2 for "more than one"), and whether
the budget ran out. -/
def count (g : Grammar) (ts : Array String) (s : String) : Nat × Bool :=
  let (rs, over) := readBack g ts s
  (rs.size, over)

end Imprimatur.Validate
