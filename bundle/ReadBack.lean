/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std.Data.HashMap

/-!
# Reading renderings back

Translation validation (DESIGN §18.4, docs/verified-validator.md): the
notation in scope is a grammar over TeX tokens, and a rendered formula must
have exactly one reading in it, the reading the renderer expected. This
module is the reading back: tokens, readings as trees, the grammar's
symbols and their compilation, the parser that counts readings, and the
matching of a reading against the expected one. The source is
`bundle/ReadBack.lean`, copied into both packages (`extract/Imprimatur/
ReadBack.lean`, `splice/Imprimatur/ReadBack.lean`); the lint keeps the
copies equal. It holds definitions only, every one total, and depends on
Lean's core and `Std.HashMap` only, so that the theorems about it, proved in
the splice package, are about the functions the extractor runs.

**Sorts** are a parameter, `SortAlgebra`: how sorts are compared, how a
hole's sort is specialised by the type variables bound so far, and how a
hole's filling binds them. The extractor instantiates it with Lean's types;
the theorems hold for every algebra.

**The parser** is a memoised chart parser. It is total by a fuel that bounds
its depth, and reports when it gave up: `over` (the work budget, or the
fuel), `pruned` (a variant of a reading dropped past the cap). A formula
with either flag set is not validated.

**Cuts.** A question already being asked (the same sort, precedence,
exclusion and span, reached again through a chain of coercions) is cut: it
has no answer yet, and a reading that needs it would go round in a circle.
A cut loses nothing of the question itself, since a derivation that comes
back to its own question can be shortened to the inner one. But a question
asked in between has an answer that lacks what the cut question would have
given, so it is remembered together with the questions it was cut on, and
the memory is used only while those are still being asked, when asking
again would be cut the same way; afterwards it is asked afresh. What is
remembered is therefore complete whenever it is used.
-/

namespace Imprimatur.Validate

/-! ## Tokens -/

/-- `\LeanMathCode{` -/
def codeOpen : List Char := "\\LeanMathCode{".toList

/-- How many characters reach the brace that closes `depth` open ones, a
`\`-escaped character skipped with its escape. -/
def toClose : List Char → Nat → Nat
  | [], _ => 0
  | '\\' :: _ :: cs, depth => 2 + toClose cs depth
  | ['\\'], _ => 1
  | '{' :: cs, depth => 1 + toClose cs (depth + 1)
  | '}' :: cs, depth => if depth ≤ 1 then 1 else 1 + toClose cs (depth - 1)
  | _ :: cs, depth => 1 + toClose cs depth

/-- Tokens, onto `acc` (held reversed): control words (`\vdash`), control
symbols (`\,`, `\{`, `\ `), and single characters; spaces separate tokens and
are dropped. `\LeanMathCode{…}`, Lean's own rendering of what has no
notation, is one opaque token, and `\LeanBreak` (a line break) is dropped. -/
def tokenizeGo : List Char → List String → List String
  | [], acc => acc.reverse
  | ['\\'], acc => (String.ofList ['\\', ' '] :: acc).reverse
  | '\\' :: d :: rest, acc =>
    if d.isAlpha then
      let name := (d :: rest).takeWhile Char.isAlpha
      let after := (d :: rest).drop name.length
      if name = "LeanMathCode".toList ∧ after.head? = some '{' then
        -- One opaque token, to the matching brace.
        let n := toClose after.tail 1
        tokenizeGo (after.tail.drop n) (String.ofList (codeOpen ++ after.tail.take n) :: acc)
      else if name = "LeanBreak".toList then tokenizeGo after acc
      else tokenizeGo after (String.ofList ('\\' :: name) :: acc)
    else
      -- A control symbol: one character after the backslash.
      tokenizeGo rest (String.ofList ['\\', d] :: acc)
  | c :: cs, acc =>
    if c = ' ' ∨ c = '\n' ∨ c = '\t' then tokenizeGo cs acc else tokenizeGo cs (c.toString :: acc)
termination_by cs => cs.length
decreasing_by
  all_goals simp_wf
  all_goals (try simp only [List.length_cons, List.length_drop, List.length_tail])
  all_goals omega

/-- TeX tokens. -/
def tokenize (s : String) : Array String := (tokenizeGo s.toList []).toArray

/-! ## Readings -/

/-- A reading: a tree named by what it reads as (a production's name, an
atom's TeX, a bound variable's name), with its children in the order of the
rule's pattern; or `any`, which the renderer writes for a form it does not
say how to read, and which matches any subterm. -/
inductive Reading where
  /-- Any reading (`⁇`). -/
  | any
  /-- A reading named `name`, with its children. -/
  | node (name : String) (kids : List Reading)
  deriving Inhabited, Repr

mutual
/-- A reading as the bundle writes it: `name`, or `name[kid; kid]`. -/
def Reading.text : Reading → String
  | .any => "⁇"
  | .node n [] => n
  | .node n (k :: ks) => n ++ "[" ++ Reading.textList (k :: ks) ++ "]"
termination_by r => sizeOf r

/-- Readings, separated by `; `. -/
def Reading.textList : List Reading → String
  | [] => ""
  | [k] => k.text
  | k :: k' :: ks => k.text ++ "; " ++ Reading.textList (k' :: ks)
termination_by ks => sizeOf ks
end

mutual
/-- Readings equal. -/
def Reading.beq : Reading → Reading → Bool
  | .any, .any => true
  | .node n ks, .node n' ks' => n == n' && Reading.beqList ks ks'
  | _, _ => false
termination_by r _ => sizeOf r

/-- Lists of readings equal. -/
def Reading.beqList : List Reading → List Reading → Bool
  | [], [] => true
  | k :: ks, k' :: ks' => Reading.beq k k' && Reading.beqList ks ks'
  | _, _ => false
termination_by ks _ => sizeOf ks
end

instance : BEq Reading := ⟨Reading.beq⟩

mutual
/-- A reading matches the expected one: `any` matches any reading, and a
node matches a node of the same name whose children match. -/
def Reading.matches : Reading → Reading → Bool
  | .any, _ => true
  | .node n ks, .node n' ks' => n == n' && Reading.matchesList ks ks'
  | .node _ _, .any => false
termination_by r _ => sizeOf r

/-- Children match, pairwise. -/
def Reading.matchesList : List Reading → List Reading → Bool
  | [], [] => true
  | k :: ks, k' :: ks' => Reading.matches k k' && Reading.matchesList ks ks'
  | _, _ => false
termination_by ks _ => sizeOf ks
end

/-- The productions that are application. -/
def appNames : List String :=
  ["application", "application f(a)", "application f_{a}", "DFunLike.coe", "CoeFun.coe"]

/-- An application, of `fs` (the function, or the parts of an application
in function position, which is the same application) to `rest`: a constant
applied is the constant's own reading (`\mathsf{inr}\,y` by a rule for
`Sum.inr` alone and by one for `Sum.inr j` is one term), so a constant's name
in function position names the node. -/
def appOf (fs rest : List Reading) : Reading :=
  match fs with
  | [.node n []] =>
    if n.contains '.' && !n.contains '\\' && !n.contains '[' then .node n rest
    else .node "app" (fs ++ rest)
  | _ => .node "app" (fs ++ rest)

/-- Children in the order of the rule's pattern, from the order the template
shows them, when the rule gives one for this many. -/
def reorder (order : Option (Array Nat)) (kids : Array Reading) : List Reading :=
  match order with
  | some o =>
    if o.size == kids.size then
      ((o.zip kids).toList.mergeSort (fun a b => a.1 ≤ b.1)).map (·.2)
    else kids.toList
  | none => kids.toList

/-- The reading of a production named `name` with these children.
Application, however written, is one reading: `f\,a`, `f(a)`, `f_{a}`, and
`⇑f a` through the coercion to a function, which is invisible; and
`f(a)(b)` is `f` applied to `a` and `b`. -/
def mkReading (name : String) (order : Option (Array Nat)) (kids : Array Reading) : Reading :=
  let kids := reorder order kids
  if appNames.contains name then
    match kids with
    | .node "app" inner :: rest => appOf inner rest
    | f :: rest => appOf [f] rest
    | [] => .node "app" []
  else .node name kids

/-- The reading of a form the renderer does not say how to read: it matches
any reading. -/
def anyReading : Reading := .any

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
  | list (elem : List Sym) (sep : List String) (min : Nat)
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
  syms : List Sym
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

/-- The lists of a grammar: each element and separator, compiled. -/
abbrev Lists := Array (Array ASym × Array ASym)

mutual
/-- Compile symbols, collecting lists. The holes of a chain (production
`chain`) exclude it. -/
def compileSyms (chain : Option Nat) : List Sym → Lists → Array ASym × Lists
  | [], lists => (#[], lists)
  | s :: ss, lists =>
    let (a, lists) := compileSym chain s lists
    let (b, lists) := compileSyms chain ss lists
    (a ++ b, lists)

/-- Compile one symbol. -/
def compileSym (chain : Option Nat) : Sym → Lists → Array ASym × Lists
  | .tok t, lists => (#[.tok t], lists)
  | .hole so p, lists => (#[.hole so p chain], lists)
  | .var, lists => (#[.var], lists)
  | .list elem sep min, lists =>
    let (e, lists) := compileSyms chain elem lists
    let idx := lists.size
    (e.push (.tail idx (min - 1)), lists.push (e, (sep.map ASym.tok).toArray))
end

/-- A compiled grammar. -/
structure Grammar where
  /-- The productions, with their compiled bodies. -/
  prods : Array (Prod × Array ASym)
  /-- The lists: element and separator, compiled. -/
  lists : Lists

/-- Add productions to a grammar. -/
def Grammar.extend (g : Grammar) (ps : Array Prod) : Grammar :=
  ps.foldl (fun g p =>
    let (b, lists) := compileSyms (if p.chain then some g.prods.size else none) p.syms g.lists
    { prods := g.prods.push (p, b), lists }) g

/-- Compile productions into a grammar. -/
def Grammar.of (ps : Array Prod) : Grammar := Grammar.extend { prods := #[], lists := #[] } ps

/-! ## Sorts -/

/-- A sort that is a rule's type variable (`?α`): its holes of that sort
must agree (DESIGN §18.3). -/
def isTyVar (s : String) : Bool := s.startsWith "?"

/-- A binding of a production's type variables to sorts. -/
abbrev Env := Array (String × String)

/-- How sorts behave: the parser's parameter. -/
structure SortAlgebra where
  /-- Sorts compatible: the first found where the second is expected. -/
  compat : String → String → Bool
  /-- The sort a hole expects, under the type variables bound so far. -/
  expected : Env → String → String
  /-- Bind a hole's type variables to the parts of the sort of what fills it. -/
  bind : Env → String → String → Env

/-! ## Counting readings -/

/-- What the reader remembers. -/
structure CState where
  /-- Readings of a nonterminal, with their sorts, by sort, precedence,
  excluded production and span; and the questions they were cut on, which
  must still be active for them to hold. -/
  memo : Std.HashMap (String × Nat × Option Nat × Nat × Nat)
    (Array (Reading × String) × Array (String × Nat × Option Nat × Nat × Nat)) := {}
  /-- Readings of a suffix of a body: its children's readings, and the
  type variables bound, by body, position, bindings and span; and the
  questions they were cut on. -/
  memoSeq : Std.HashMap (String × Nat × Env × Nat × Nat)
    (Array (Array Reading × Env) × Array (String × Nat × Option Nat × Nat × Nat)) := {}
  /-- Nonterminals being read, to cut coercion cycles. -/
  active : Std.HashMap (String × Nat × Option Nat × Nat × Nat) Unit := {}
  /-- The questions cut, in order, so that an answer that lacks one is not
  remembered. -/
  cuts : Array (String × Nat × Option Nat × Nat × Nat) := #[]
  /-- Work done, against a budget. -/
  steps : Nat := 0
  /-- The budget, or the fuel, ran out. -/
  over : Bool := false
  /-- A variant of a reading was dropped past the cap. -/
  pruned : Bool := false
  /-- Whether to log what is read (`IMPRIMATUR_VALIDATE_DEBUG`). -/
  trace : Bool := false
  /-- The log. -/
  log : Array String := #[]
  /-- `reachable`, by sort: those that start with a token, by the token,
  and the others. -/
  reach : Std.HashMap String (Std.HashMap String (Array Nat) × Array Nat) := {}

/-- The reader's monad. -/
abbrev CountM := StateM CState

/-- The variants of a reading kept: past them, the reading is not validated. -/
def variantCap : Nat := 256

/-- The readings to keep of a list: at most two different readings (by
`key`; two readings that are written the same are the same reading), each
with up to `variantCap` different sorts or bindings (by `variant`), since a reading
can be of several sorts (an atom, or the same atom through a coercion). A
variant that is `top` (an unknown sort, no bindings) is as good as any other
for what follows, so it stands alone. Whether a variant was dropped past
the cap is returned with them. -/
def keep2 {α : Type} (key : α → String) (variant : α → String) (xs : Array α)
    (top : String := "*") : Array α × Bool := Id.run do
  let mut out : Array α := #[]
  let mut keys : Array String := #[]
  let mut pruned := false
  for x in xs do
    let k := key x
    if !keys.contains k then
      if keys.size ≥ 2 then continue
      keys := keys.push k
    if out.any (fun y => key y == k && variant y == top) then continue
    if variant x == top then
      out := (out.filter (key · != k)).push x
      continue
    if (out.filter (key · == k)).size ≥ variantCap then
      pruned := true
      continue
    unless out.any (fun y => key y == k && variant y == variant x) do out := out.push x
  return (out, pruned)

/-- `keep2`, noting a dropped variant in the state. -/
def keep2M {α : Type} (key : α → String) (variant : α → String) (xs : Array α)
    (top : String := "*") : CountM (Array α) := do
  let (out, pruned) := keep2 key variant xs top
  if pruned then modify fun st => { st with pruned := true }
  return out

/-- The number of different readings among some. -/
def distinct {α : Type} (key : α → String) (xs : Array α) : Nat :=
  (xs.foldl (fun (acc : Array String) x => if acc.contains (key x) then acc else acc.push (key x)) #[]).size

/-- The work budget: past it, a formula is not validated. -/
def budget : Nat := 3000000

/-- The least number of tokens a symbol reads: one, or, for the rest of a
list, one per element still required. -/
def minLen : ASym → Nat
  | .tail _ r => r
  | _ => 1

/-- The least number of tokens `body[pos:]` reads. -/
def minLenFrom (body : Array ASym) (pos : Nat) : Nat :=
  (body.toList.drop pos).foldl (fun n s => n + minLen s) 0

/-- The productions that can make an expression of sort `s`: those of a
compatible sort, coercions included. A bound variable's name is not an
expression, so is not among them. -/
def reachable (A : SortAlgebra) (g : Grammar) (s : String) : Array Nat :=
  (List.range g.prods.size).foldl (fun out i =>
    match g.prods[i]? with
    | some (p, _) => if !p.isVar && A.compat p.sort s then out.push i else out
    | none => out) #[]

/-- The text of readings, as a key. -/
def readingsKey (cs : Array Reading) : String := Reading.text (.node "" cs.toList)

/-- A binding environment, as a key. -/
def envKey (env : Env) : String := toString env

mutual
  /-- Readings of `ts[i:j]` as an expression of sort `s` at precedence `p`,
  not made by production `excl`, with their sorts: at most two. -/
  def expr (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Nat → Option Nat → Nat → Nat → CountM (Array (Reading × String))
    | 0, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, s, p, excl, i, j => do
      if i ≥ j then return #[]
      let key := (s, p, excl, i, j)
      if let some (n, on) := (← get).memo[key]? then
        if on.all (← get).active.contains then return n
      if (← get).active.contains key then
        modify fun st => { st with cuts := st.cuts.push key }
        return #[]
      let cutsBefore := (← get).cuts.size
      modify fun st => { st with active := st.active.insert key (), steps := st.steps + 1 }
      let (byTok, others) ← match (← get).reach[s]? with
        | some r => pure r
        | none =>
          let (byTok, others) := (reachable A g s).foldl (fun (byTok, others) k =>
            match (g.prods[k]?.map (·.2)).bind (·[0]?) with
            | some (ASym.tok t) => (byTok.insert t ((byTok.getD t #[]).push k), others)
            | _ => (byTok, others.push k))
            (({} : Std.HashMap String (Array Nat)), (#[] : Array Nat))
          modify fun st => { st with reach := st.reach.insert s (byTok, others) }
          pure (byTok, others)
      let known := s != "*" && !isTyVar s
      let mut out : Array (Reading × String) := #[]
      -- Every production is tried, even after two readings: a reading found
      -- again can be of another sort, which a hole's binding may need.
      let cands := byTok.getD (ts.getD i "") #[] ++ others
      for k in cands do
        if excl == some k then continue
        let some (pr, body) := g.prods[k]? | continue
        if pr.coercion then continue
        if pr.prec < p then continue
        -- A body that starts or ends with a token must match it.
        if let some (ASym.tok t) := body[0]? then
          if ts.getD i "" != t then continue
        if let some (ASym.tok t) := body.back? then
          if ts.getD (j - 1) "" != t then continue
        for (cs, env) in ← seq A g ts fuel s!"p{k}" body 0 #[] i j do
          -- The sort of the reading: the production's, under its bindings.
          let so := A.expected env pr.sort
          if !A.compat so s then continue
          out ← keep2M (·.1.text) (·.2) (out.push (mkReading pr.name pr.order cs, if known then s else so))
      -- Coercions are invisible: a reading through one is its argument's, at
      -- the precedence asked for, and its sort is the coercion's, with the
      -- argument's sort bound (`Option.some` of a label is an `Option(Label)`).
      -- An argument of the sort asked for is among the readings above, and
      -- others are read afresh.
      for k in cands do
        let some (pr, body) := g.prods[k]? | continue
        if !pr.coercion then continue
        let some (ASym.hole s' _ _) := body[0]? | continue
        let es' := A.expected #[] s'
        let args ← if es' == s then pure out else expr A g ts fuel es' p none i j
        for (r, so) in args do
          let sort := A.expected (A.bind #[] s' so) pr.sort
          if !A.compat sort s then continue
          out ← keep2M (·.1.text) (·.2) (out.push (r, if known then s else sort))
      -- The emitter's parentheses, and its TeX groups (`{k_{1}}_{x}`), which
      -- do not print.
      if distinct (·.1.text) out < 2 && j - i ≥ 3 && ts.getD i "" == "(" && ts.getD (j - 1) "" == ")" then
        out ← keep2M (·.1.text) (·.2) (out ++ (← expr A g ts fuel s 0 none (i + 1) (j - 1)))
      if distinct (·.1.text) out < 2 && j - i ≥ 3 && ts.getD i "" == "{" && ts.getD (j - 1) "" == "}" then
        out ← keep2M (·.1.text) (·.2) (out ++ (← expr A g ts fuel s p none (i + 1) (j - 1)))
      -- Remembered with the questions, other than this one, cut meanwhile.
      let cuts := (← get).cuts
      let on := (cuts.extract cutsBefore cuts.size).filter (· != key)
      modify fun st => { st with active := st.active.erase key, memo := st.memo.insert key (out, on) }
      if (← get).trace then
        let line := s!"{s} @{p} [{i},{j}) {ts.extract i j}: {out.map fun (r, so) => (r.text, so)}"
        modify fun st => { st with log := st.log.push line }
      return out

  /-- Readings of `ts[i:j]` as a bound variable's name. -/
  def var (g : Grammar) (ts : Array String) : Nat → Nat → Nat → CountM (Array Reading)
    | 0, _, _ => do modify fun st => { st with over := true }; return #[]
    | _ + 1, i, j => do
      for (pr, body) in g.prods do
        if pr.isVar && body.size == j - i &&
            (List.range body.size).all (fun d => body[d]? == some (ASym.tok (ts.getD (i + d) ""))) then
          return #[.node pr.name []]
      return #[]

  /-- Readings of `ts[i:j]` as `body[pos:]` (of production or list `id`)
  under bindings `env`: the readings of its holes, variables and lists, and
  the bindings after them. -/
  def seq (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Array ASym → Nat → Env → Nat → Nat → CountM (Array (Array Reading × Env))
    | 0, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, id, body, pos, env, i, j => do
      if (← get).steps > budget then
        modify fun st => { st with over := true }
        return #[]
      if pos == body.size then return if i == j then #[(#[], env)] else #[]
      let key := (id, pos, env, i, j)
      if let some (n, on) := (← get).memoSeq[key]? then
        if on.all (← get).active.contains then return n
      let cutsBefore := (← get).cuts.size
      modify fun st => { st with steps := st.steps + 1 }
      let n ← match body[pos]? with
        | some (.tok t) =>
          if i < j && ts.getD i "" == t then seq A g ts fuel id body (pos + 1) env (i + 1) j else pure #[]
        | some (.hole s p x) =>
          split A g ts fuel (fun env a b => do
              return (← expr A g ts fuel (A.expected env s) p x a b).map fun (r, so) => (#[r], A.bind env s so))
            id body pos env i j
        | some .var =>
          split A g ts fuel (fun env a b => do return (← var g ts fuel a b).map (#[·], env)) id body pos env i j
        | some (.tail l r) => split A g ts fuel (fun env a b => tail A g ts fuel l r env a b) id body pos env i j
        | none => pure #[]
      -- Remembered with the questions cut meanwhile.
      let cuts := (← get).cuts
      modify fun st => { st with memoSeq := st.memoSeq.insert key (n, cuts.extract cutsBefore cuts.size) }
      return n

  /-- Readings of `ts[i:j]` as a nonterminal then `body[pos+1:]`. The
  nonterminal ends where what follows can still fit, and, if that is a
  token, where it stands. -/
  def split (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → (Env → Nat → Nat → CountM (Array (Array Reading × Env))) → String →
      Array ASym → Nat → Env → Nat → Nat → CountM (Array (Array Reading × Env))
    | 0, _, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, nt, id, body, pos, env, i, j => do
      if pos + 1 == body.size then return ← nt env i j
      let mut out : Array (Array Reading × Env) := #[]
      let next : Option String := match body[pos + 1]? with
        | some (.tok t) => some t
        | _ => none
      -- Only the rest of a list can be empty.
      let start := match body[pos]? with
        | some (.tail ..) => i
        | _ => i + 1
      let last := j - minLenFrom body (pos + 1)
      for m in [start:last + 1] do
        if let some t := next then
          if ts[m]? != some t then continue
        for (as, env₁) in ← nt env i m do
          for (rest, env₂) in ← seq A g ts fuel id body (pos + 1) env₁ m j do
            out ← keep2M (fun (cs, _) => readingsKey cs) (fun (_, e) => envKey e) (out.push (as ++ rest, env₂)) (top := "#[]")
      return out

  /-- Readings of `ts[i:j]` as the rest of list `l`, `r` more required. -/
  def tail (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → Nat → Nat → Env → Nat → Nat → CountM (Array (Array Reading × Env))
    | 0, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, l, r, env, i, j => do
      let some (elem, sep) := g.lists[l]? | return #[]
      let mut out : Array (Array Reading × Env) := if r == 0 && i == j then #[(#[], env)] else #[]
      if i < j then
        let more := sep ++ elem ++ #[ASym.tail l (r - 1)]
        out ← keep2M (fun (cs, _) => readingsKey cs) (fun (_, e) => envKey e)
          (out ++ (← seq A g ts fuel s!"t{l}.{r}" more 0 env i j)) (top := "#[]")
      return out
end

/-- The fuel: more than the depth any reading of `ts` can have. -/
def fuelFor (ts : Array String) : Nat := 8 * ts.size + 256

/-- The readings of a whole formula as sort `s`: at most two. -/
def readings (A : SortAlgebra) (g : Grammar) (ts : Array String) (s : String) : CountM (Array Reading) := do
  let rs := (← expr A g ts (fuelFor ts) s 0 none 0 ts.size).map (·.1)
  return rs.foldl (fun acc r => if acc.any (· == r) then acc else acc.push r) #[]

/-- Where the reader gave up, if it did. -/
structure Flags where
  /-- The work budget, or the fuel, ran out. -/
  over : Bool
  /-- A variant of a reading was dropped past the cap. -/
  pruned : Bool
  deriving Inhabited, Repr

/-- The flags of a state after reading. -/
def CState.flags (st : CState) : Flags :=
  { over := st.over || st.steps > budget, pruned := st.pruned }

/-- Whether any flag is set: the reading is not to be trusted. -/
def Flags.any (f : Flags) : Bool := f.over || f.pruned

/-- The readings (at most two) of a token sequence as an expression of sort
`s`, and where the reader gave up. -/
def readBackWith (A : SortAlgebra) (g : Grammar) (ts : Array String) (s : String) :
    Array Reading × Flags :=
  let (rs, st) := (readings A g ts s).run {}
  (rs, st.flags)

/-- `readBackWith`, with a log of what was read where. -/
def readBackLogWith (A : SortAlgebra) (g : Grammar) (ts : Array String) (s : String) :
    Array Reading × Array String :=
  let (rs, st) := (readings A g ts s).run { trace := true }
  (rs, st.log)

end Imprimatur.Validate
