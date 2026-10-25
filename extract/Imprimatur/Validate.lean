/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.ReadBack
import Imprimatur.Doc
import Imprimatur.Commands
import Imprimatur.TeX

/-!
# Translation validation of renderings

DESIGN §18.3–§18.4. A rendering is *faithful* when a reader who knows the
paper's notation reads it back as the expression it came from. The reading
back itself, tokens, the grammar's symbols, the parser that counts readings
and the matching of a reading against the expected one, is the shared
module `Imprimatur.ReadBack` (docs/verified-validator.md), proved in the
splice package. This module is what is Lean's: the algebra of sorts, the
productions of the notation rules and the built-in forms, and the grammar
of the notation in scope.

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

/-! ## Sorts -/

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

/-- The type variables of a sort. -/
partial def STerm.tyvars : STerm → List String
  | .atom a => if isTyVar a then [a] else []
  | .arrow a b => a.tyvars ++ b.tyvars
  | .app _ as => as.toList.flatMap STerm.tyvars

/-- A sort with its type variables renamed. -/
partial def STerm.mapVars (f : String → String) : STerm → STerm
  | .atom a => .atom (if isTyVar a then f a else a)
  | .arrow a b => .arrow (a.mapVars f) (b.mapVars f)
  | .app h as => .app h (as.map (STerm.mapVars f))

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
    syms := [.hole "Prop" 26, .tok "\\implies", .hole "Prop" 25] },
  { name := "function type", sort := "Sort", prec := 25,
    syms := [.hole "Sort" 26, .tok "\\to", .hole "Sort" 25] },
  { name := "∀", sort := "Prop", prec := 0,
    syms := [.tok "\\forall", .var, .tok ":", .hole "Sort" 1, .tok ",", .tok "\\ ", .hole "Prop" 0] },
  -- A dependent function type, written the same way; the same reading.
  { name := "∀", sort := "Sort", prec := 0,
    syms := [.tok "\\forall", .var, .tok ":", .hole "Sort" 1, .tok ",", .tok "\\ ", .hole "Sort" 0] },
  { name := "bounded ∀", sort := "Prop", prec := 0,
    syms := [.tok "\\forall", .var, .tok "\\in", .hole "*" 50, .tok ",", .tok "\\ ", .hole "Prop" 0] },
  { name := "∃", sort := "Prop", prec := 0,
    syms := [.tok "\\exists", .var, .tok ",", .tok "\\ ", .hole "Prop" 0] },
  { name := "bounded ∃", sort := "Prop", prec := 0,
    syms := [.tok "\\exists", .var, .tok "\\in", .hole "*" 50, .tok ",", .tok "\\ ", .hole "Prop" 0] },
  { name := "λ", sort := "*", prec := 0,
    syms := [.tok "\\lambda", .var, .tok ".", .tok "\\,", .hole "*" 0] },
  { name := "application", sort := "*", prec := Doc.maxPrec - 1,
    syms := [.hole "*" Doc.maxPrec, .list [.tok "\\,", .hole "*" Doc.maxPrec] [] 1] }]
  let callForm : Prod :=
  { name := "application f(a)", sort := "*", prec := Doc.maxPrec,
    syms := [.hole "*" Doc.maxPrec, .list [.tok "(", .hole "*" 0, .tok ")"] [] 1] }
  let subscriptForm : Prod :=
  { name := "application f_{a}", sort := "*", prec := Doc.maxPrec,
    syms := [.hole "*" Doc.maxPrec, .tok "_", .tok "{",
      .list [.hole "*" 0] [","] 1, .tok "}"] }
  -- `latex_style pattern_matching := cases`: a case analysis.
  let caseForm : Prod :=
  { name := "case", sort := "*", prec := 0,
    syms := (tokenize "\\mathsf{case}\\ ").toList.map .tok ++
      [.list [.hole "*" 1] [",", "\\ "] 1] ++ (tokenize "\\ \\mathsf{of}\\ ").toList.map .tok ++
      [.list [.list [.hole "*" 1] [",", "\\ "] 1, .tok "\\Rightarrow", .hole "*" 1] ["\\mid"] 1] }
  -- `latex_style lists := literal`: a list literal.
  let listForm : Prod :=
  { name := "list", sort := "List(*)", prec := Doc.maxPrec,
    syms := [.tok "[", .list [.hole "*" 0] [",", "\\ "] 1, .tok "]"] }
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
  -- A type variable that one hole alone mentions, and the rule's sort does
  -- not, is bound by what fills that hole and read by nothing (`HAppend α β
  -- γ` gives each operand its own): it is left unknown, so that the hole's
  -- fillers of several sorts make one answer, not one each.
  let mentions (s : String) : List String := (STerm.tyvars (STerm.parse s)).eraseDups
  let counts : List String :=
    (vars.filter (!hidden.contains ·)).toList.flatMap (fun v => mentions (sortOf v)) ++ mentions r.sort
  let lone (a : String) : Bool := counts.count a == 1 && !(mentions r.sort).contains a
  let sortOf (v : String) : String :=
    let so := sortOf v
    if (mentions so).any lone then ((STerm.parse so).mapVars fun a => if lone a then "*" else a).render else so
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
        syms := syms.push (.list [hole] chainSep.toList 1)
      else if folded == some v then
        -- The variables of a fold each have their own type.
        syms := syms.push (.list [.hole "*" need] (tokenize r.sep).toList 1)
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
  return some { name, sort, prec := r.prec, syms := syms.toList, coercion, chain, order }

/-- The grammar of the notation in scope, for a notation variant: its rules
and the built-in forms. A formula's atoms are added to it (`Grammar.extend`). -/
def notationGrammar (rules : Array NotationRule) (variant : Option String) (call subscript : Bool)
    (cases lists : Bool := false) : Grammar :=
  let rules := rules.filter fun r => r.variant.isNone || r.variant == variant
  Grammar.of (rules.filterMap ofRule ++ builtins call subscript cases lists)


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

/-- Lean's types, as the parser's sorts. -/
def algebra : SortAlgebra := { compat, expected, bind, anySort := fun s => s == "*" || isTyVar s }

/-- The readings (at most two) of a token sequence as an expression of sort
`s`, and where the reader gave up. -/
def readBack (g : Grammar) (ts : Array String) (s : String) : Array Reading × Flags :=
  readBackWith algebra g ts s

/-- `readBack`, with a log of what was read where. -/
def readBackLog (g : Grammar) (ts : Array String) (s : String) : Array Reading × Array String :=
  readBackLogWith algebra g ts s

/-- The number of readings (0, 1, or 2 for "more than one"), and whether
the reader gave up. -/
def count (g : Grammar) (ts : Array String) (s : String) : Nat × Bool :=
  let (rs, flags) := readBack g ts s
  (rs.size, flags.any)

end Imprimatur.Validate
