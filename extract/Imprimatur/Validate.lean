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

/-- A sort as a term: a function sort `(A → B)` has parts. -/
inductive STerm where
  /-- A sort without parts. -/
  | atom (s : String)
  /-- A function sort. -/
  | arrow (a b : STerm)
  deriving Inhabited, BEq

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
  return .atom s

/-- Write a sort back. -/
partial def STerm.render : STerm → String
  | .atom s => s
  | .arrow a b => s!"({a.render} → {b.render})"

/-- Sorts compatible: equal up to unknowns (`*`, and type variables, which
are unknown until bound), part by part. -/
partial def STerm.compat : STerm → STerm → Bool
  | .atom a, .atom b => a == b || unknown a || unknown b
  | .atom a, _ => unknown a
  | _, .atom b => unknown b
  | .arrow a b, .arrow c d => a.compat c && b.compat d
where
  unknown (s : String) : Bool := s == "*" || s.startsWith "?"

/-- Sorts compatible (see `STerm.compat`). -/
def compat (a b : String) : Bool :=
  a == b || a == "*" || b == "*" || isTyVar a || isTyVar b ||
    match STerm.parse a, STerm.parse b with
    | .atom x, .atom y => x == y
    | x, y => x.compat y

/-- The productions of the built-in forms of `Render.render`. An applied
variable is written `f(a)` or `f_{a}` only under the style that asks for it
(`latex_style applied_variables`), so those forms are read only then. -/
def builtins (call subscript : Bool := false) : Array Prod :=
  let forms : Array Prod := #[
  { name := "implication", sort := "Prop", prec := 25,
    syms := #[.hole "Prop" 26, .tok "\\implies", .hole "Prop" 25] },
  { name := "function type", sort := "Sort", prec := 25,
    syms := #[.hole "Sort" 26, .tok "\\to", .hole "Sort" 25] },
  { name := "∀", sort := "Prop", prec := 0,
    syms := #[.tok "\\forall", .var, .tok ":", .hole "Sort" 1, .tok ",", .tok "\\ ", .hole "Prop" 0] },
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
  forms ++ (if call then #[callForm] else #[]) ++ (if subscript then #[subscriptForm] else #[])

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
  for p in parts do
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
      let need :=
        if depth > 0 || r.prec ≥ Doc.maxPrec then 0
        else
          let first := topIdx == 0
          let last := topIdx + 1 == topCount
          match r.assoc with
          | "left" => if first then r.prec else r.prec + 1
          | "right" => if last then r.prec else r.prec + 1
          | _ => r.prec + 1
      let hole := Sym.hole (sortOf v) need
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
  return some { name, sort := r.sort, prec := r.prec, syms, coercion, chain, order }

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
def notationGrammar (rules : Array NotationRule) (variant : Option String) (call subscript : Bool) :
    Grammar :=
  let rules := rules.filter fun r => r.variant.isNone || r.variant == variant
  Grammar.of (rules.filterMap ofRule ++ builtins call subscript)

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
  /-- `reachable`, by sort: those that start with a token, by the token,
  and the others. -/
  reach : Std.HashMap String
    (Std.HashMap String (Array (Nat × Option String)) × Array (Nat × Option String)) := {}

/-- The reader's monad. -/
abbrev CountM := StateM CState

/-- At most two of a list of readings, without repeats by `key`: two
readings that are written the same are the same reading. -/
def keep2 {α : Type} (key : α → String) (xs : Array α) : Array α := Id.run do
  let mut out : Array α := #[]
  for x in xs do
    if out.size ≥ 2 then break
    unless out.any (key · == key x) do out := out.push x
  return out

/-- The work budget: past it, a formula is not validated. -/
def budget : Nat := 3000000

section
variable (g : Grammar) (ts : Array String)

/-- The productions reachable from sort `s` through coercions, each once,
with the sort of the outermost coercion on the way (none when reached
directly, `*` when the paths disagree). A bound variable's name is not an expression, so is not among
them. -/
partial def reachable (s : String) : Array (Nat × Option String) := Id.run do
  let mut sorts : Array (String × Option String) := #[(s, none)]
  let mut changed := true
  while changed do
    changed := false
    for (p, b) in g.prods do
      if !p.coercion then continue
      if let some (_, via) := sorts.find? (compat p.sort ·.1) then
        if let some (ASym.hole s' _ _) := b[0]? then
          let s' := if isTyVar s' then "*" else s'
          unless sorts.any (·.1 == s') do
            sorts := sorts.push (s', some (via.getD p.sort))
            changed := true
  let mut out := #[]
  for i in [0:g.prods.size] do
    let (p, _) := g.prods[i]!
    if p.coercion || p.isVar then continue
    -- Reached on several paths that give it different sorts (directly, and
    -- through a coercion), its sort is unknown.
    let vias := (sorts.filter (compat p.sort ·.1)).map (·.2)
    if let some v := vias[0]? then
      out := out.push (i, if vias.all (· == v) then v else some "*")
  return out

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
  if children.isEmpty then p.name else s!"{p.name}[{"; ".intercalate children.toList}]"

/-- The sort a hole expects, under the type variables bound so far. -/
partial def expected (env : Env) (s : String) : String :=
  if !s.contains '?' then s
  else if isTyVar s then ((env.find? (·.1 == s)).map (·.2)).getD "*"
  else
    let rec go : STerm → STerm
      | .atom a => if isTyVar a then .atom (((env.find? (·.1 == a)).map (·.2)).getD "*") else .atom a
      | .arrow a b => .arrow (go a) (go b)
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
        let mut byTok : Std.HashMap String (Array (Nat × Option String)) := {}
        let mut others := #[]
        for (k, via) in reachable g s do
          match g.prods[k]!.2[0]? with
          | some (ASym.tok t) => byTok := byTok.insert t ((byTok.getD t #[]).push (k, via))
          | _ => others := others.push (k, via)
        modify fun st => { st with reach := st.reach.insert s (byTok, others) }
        pure (byTok, others)
    let mut out : Array (String × String) := #[]
    for (k, via) in byTok.getD ts[i]! #[] ++ others do
      if out.size ≥ 2 then break
      if excl == some k then continue
      let (pr, body) := g.prods[k]!
      if pr.prec < p then continue
      -- A body that starts or ends with a token must match it.
      if let some (ASym.tok t) := body[0]? then
        if ts[i]! != t then continue
      if let some (ASym.tok t) := body.back? then
        if ts[j - 1]! != t then continue
      for (cs, env) in ← seq s!"p{k}" body 0 #[] i j do
        -- The sort of the reading: the production's, under its bindings, or
        -- the outermost coercion's when it was reached through coercions.
        let so := match via with
          | some c => if isTyVar c then "*" else c
          | none => expected env pr.sort
        if via.isNone && !compat so s then continue
        let known := s != "*" && !isTyVar s
        out := keep2 (·.1) (out.push (reading pr cs, if known then s else so))
    -- The emitter's parentheses.
    if out.size < 2 && j - i ≥ 3 && ts[i]! == "(" && ts[j - 1]! == ")" then
      out := keep2 (·.1) (out ++ (← expr s 0 none (i + 1) (j - 1)))
    modify fun st => { st with memo := st.memo.insert key out, active := st.active.erase key }
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
      if out.size ≥ 2 then break
      if let some t := next then
        if ts[m]? != some t then continue
      for (as, env₁) in ← nt env i m do
        for (rest, env₂) in ← seq id body (pos + 1) env₁ m j do
          out := keep2 (fun (cs, _) => toString cs) (out.push (as ++ rest, env₂))
    return out

  /-- Readings of `ts[i:j]` as the rest of list `l`, `r` more required. -/
  partial def tail (l r : Nat) (env : Env) (i j : Nat) : CountM (Array (Array String × Env)) := do
    let (elem, sep) := g.lists[l]!
    let mut out : Array (Array String × Env) := if r == 0 && i == j then #[(#[], env)] else #[]
    if i < j then
      let more := sep ++ elem ++ #[ASym.tail l (r - 1)]
      out := keep2 (fun (cs, _) => toString cs) (out ++ (← seq s!"t{l}.{r}" more 0 env i j))
    return out
end

/-- The readings of a whole formula as sort `s`: at most two. -/
def readings (s : String) : CountM (Array String) := do
  return (← expr g ts s 0 none 0 ts.size).map (·.1)

end

/-- The readings (at most two) of a token sequence as an expression of sort
`s`, and whether the budget ran out. -/
def readBack (g : Grammar) (ts : Array String) (s : String) : Array String × Bool :=
  let (rs, st) := (readings g ts s).run {}
  (rs, st.steps > budget)

/-- The number of readings (0, 1, or 2 for "more than one"), and whether
the budget ran out. -/
def count (g : Grammar) (ts : Array String) (s : String) : Nat × Bool :=
  let (rs, over) := readBack g ts s
  (rs.size, over)

end Imprimatur.Validate
