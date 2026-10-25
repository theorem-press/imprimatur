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
fuel), `pruned` (a third reading of a question, or a variant of a reading
past the cap, dropped), `cut` (a question asked again while being asked,
which only a production whose body is a hole and nothing else brings
about). A formula with a flag set is not validated.

**Coercions** are invisible, and chain: a reading through one may be a
reading through another. A chain applies each coercion once, which the
question records (`used`), so chains are finite and a question is never
asked again through a cycle of coercions.
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
  deriving Inhabited, Repr, DecidableEq, Hashable

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

/-- A question of an expression: its sort, precedence, the production it is
not made by, the coercions already on the chain it is the argument of, and
its span. -/
abbrev ExprKey := String × Nat × Option Nat × List Nat × Nat × Nat

/-- What the reader remembers. -/
structure CState where
  /-- Readings of a nonterminal, with their sorts, by question. -/
  memo : Std.HashMap ExprKey (Array (Reading × String)) := {}
  /-- Readings of a nonterminal not through a coercion of its own (by the
  productions, in parentheses, in a group), by the question less its chain
  of coercions, which they do not depend on. -/
  memoD : Std.HashMap (String × Nat × Option Nat × Nat × Nat) (Array (Reading × String)) := {}
  /-- Readings of a suffix of a body: its children's readings, and the
  type variables bound, by body, position, bindings and span. -/
  memoSeq : Std.HashMap (Array ASym × Nat × Env × Nat × Nat) (Array (Array Reading × Env)) := {}
  /-- Questions being asked. -/
  active : Std.HashMap ExprKey Unit := {}
  /-- Work done, against a budget. -/
  steps : Nat := 0
  /-- The budget, or the fuel, ran out. -/
  over : Bool := false
  /-- A reading was dropped: a third one, or a variant past the cap. -/
  pruned : Bool := false
  /-- A question was cut, being already asked: a production whose body is a
  hole and nothing else brings it about, and what it reads is then not
  validated. -/
  cut : Bool := false
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

/-- `keep`, onto `out`, with the readings' keys seen so far. -/
def keepGo {α : Type} [BEq α] (key : α → String) :
    List α → Array α → Array String → Bool → Array α × Bool
  | [], out, _, pruned => (out, pruned)
  | x :: xs, out, keys, pruned =>
    let k := key x
    if !keys.contains k && keys.size ≥ 2 then keepGo key xs out keys true
    else
      let keys := if keys.contains k then keys else keys.push k
      if out.contains x then keepGo key xs out keys pruned
      else if (out.filter (key · == k)).size ≥ variantCap then keepGo key xs out keys true
      else keepGo key xs (out.push x) keys pruned

/-- The readings to keep of a list: at most two different readings (by
`key`; two readings that are written the same are the same reading), each
with up to `variantCap` different sorts or bindings, since a reading can be
of several sorts (an atom, or the same atom through a coercion), kept once
each. A third reading, or a variant past the cap, is dropped and noted:
what remains may then be short of what a question above needs. -/
def keep {α : Type} [BEq α] (key : α → String) (xs : Array α) : Array α × Bool :=
  keepGo key xs.toList #[] #[] false

/-- `keep`, noting a dropped reading in the state. -/
def keepM {α : Type} [BEq α] (key : α → String) (xs : Array α) : CountM (Array α) := do
  let (out, pruned) := keep key xs
  if pruned then modify fun st => { st with pruned := true }
  return out

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

/-- Whether each list of the grammar takes at least a token per element, as
every notation's do (an element is a hole): the parser looks for a list's
rest only where its elements fit, which is complete only then. -/
def listsWF (g : Grammar) : Bool := g.lists.all fun (elem, sep) => 1 ≤ minLenFrom (sep ++ elem) 0

/-- The productions that can make an expression of sort `s`: those of a
compatible sort, coercions included. A bound variable's name is not an
expression, so is not among them. -/
def reachable (A : SortAlgebra) (g : Grammar) (s : String) : Array Nat :=
  (List.range g.prods.size).foldl (fun out i =>
    match g.prods[i]? with
    | some (p, _) => if !p.isVar && A.compat p.sort s then out.push i else out
    | none => out) #[]

/-- `reachable`, split into the productions that start with a token, by the
token, and the others. -/
def reachSplit (A : SortAlgebra) (g : Grammar) (s : String) :
    Std.HashMap String (Array Nat) × Array Nat :=
  (reachable A g s).foldl (fun (byTok, others) k =>
    match (g.prods[k]?.map (·.2)).bind (·[0]?) with
    | some (ASym.tok t) => (byTok.insert t ((byTok.getD t #[]).push k), others)
    | _ => (byTok, others.push k))
    (({} : Std.HashMap String (Array Nat)), (#[] : Array Nat))

/-- The text of readings, as a key. -/
def readingsKey (cs : Array Reading) : String := Reading.text (.node "" cs.toList)

/-- The chain of coercions with `k` added, kept sorted: a question is the
same whatever order its chain was made in. -/
def chainWith (k : Nat) : List Nat → List Nat
  | [] => [k]
  | k' :: ks => if k < k' then k :: k' :: ks else k' :: chainWith k ks

/-- Whether production `k` is tried for sort `s` at precedence `p` on
`ts[i:j]`: not the excluded one, not a coercion, at or above `p`, and, if
its body starts or ends with a token, that token where it stands. -/
def tried (g : Grammar) (ts : Array String) (p : Nat) (excl : Option Nat) (i j k : Nat) : Bool :=
  match g.prods[k]? with
  | none => false
  | some (pr, body) =>
    excl != some k && !pr.coercion && p ≤ pr.prec &&
      (match body[0]? with | some (ASym.tok t) => ts[i]? == some t | _ => true) &&
      (match body.back? with | some (ASym.tok t) => ts[j - 1]? == some t | _ => true)

/-- The readings of production `pr`, from the readings of its body, onto
`out`: each at the production's sort under its bindings, when that is
compatible with the sort asked for. -/
def addProds (A : SortAlgebra) (s : String) (pr : Prod) :
    List (Array Reading × Env) → Array (Reading × String) → CountM (Array (Reading × String))
  | [], out => pure out
  | (cs, env) :: rest, out => do
    let so := A.expected env pr.sort
    if !A.compat so s then addProds A s pr rest out
    else addProds A s pr rest (← keepM (·.1.text) (out.push (mkReading pr.name pr.order cs, so)))

/-- The readings through coercion `pr` of hole sort `s'`, from its
argument's readings, onto `out`: each at the coercion's sort under the
bindings `env₀` the sort asked for gives and the argument's sort adds, when
that is compatible with the sort asked for. -/
def addCoes (A : SortAlgebra) (s : String) (pr : Prod) (s' : String) (env₀ : Env) :
    List (Reading × String) → Array (Reading × String) → CountM (Array (Reading × String))
  | [], out => pure out
  | (r, so) :: rest, out => do
    let sort := A.expected (A.bind env₀ s' so) pr.sort
    if !A.compat sort s then addCoes A s pr s' env₀ rest out
    else addCoes A s pr s' env₀ rest (← keepM (·.1.text) (out.push (r, sort)))

/-- The readings of a nonterminal, each followed by the readings of the rest
of the body, onto `out`. -/
def joinRests (as : Array Reading × Env) : List (Array Reading × Env) →
    Array (Array Reading × Env) → CountM (Array (Array Reading × Env))
  | [], out => pure out
  | (rest, env₂) :: more, out => do
    joinRests as more (← keepM (fun (cs, _) => readingsKey cs)
      (out.push (as.1 ++ rest, env₂)))

/-- The name of a bound variable that `ts[i:j]` is, if it is one: the first
atom production of a variable whose tokens they are. -/
def varOf (g : Grammar) (ts : Array String) (i j : Nat) : List (Prod × Array ASym) → Option Reading
  | [] => none
  | (pr, body) :: rest =>
    if pr.isVar && 0 < body.size && body.size == j - i &&
        (List.range body.size).all (fun d => body[d]? == some (ASym.tok (ts.getD (i + d) ""))) then
      some (.node pr.name [])
    else varOf g ts i j rest

mutual
  /-- Readings of `ts[i:j]` as an expression of sort `s` at precedence `p`,
  not made by production `excl`, not through the coercions `used` again,
  with their sorts: at most two. -/
  def expr (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Nat → Option Nat → List Nat → Nat → Nat → CountM (Array (Reading × String))
    | 0, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, s, p, excl, used, i, j => do
      if i ≥ j then return #[]
      let key : ExprKey := (s, p, excl, used, i, j)
      if let some n := (← get).memo[key]? then return n
      exprFresh A g ts fuel s p excl used i j

  /-- `expr`, when the question is not remembered: cut if it is being
  asked, else asked, and remembered. -/
  def exprFresh (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Nat → Option Nat → List Nat → Nat → Nat → CountM (Array (Reading × String))
    | 0, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, s, p, excl, used, i, j => do
      let key : ExprKey := (s, p, excl, used, i, j)
      if (← get).active.contains key then
        modify fun st => { st with cut := true }
        return #[]
      modify fun st => { st with active := st.active.insert key (), steps := st.steps + 1 }
      let r ← match (← get).reach[s]? with
        | some r => pure r
        | none =>
          let r := reachSplit A g s
          modify fun st => { st with reach := st.reach.insert s r }
          pure r
      exprRead A g ts fuel s p excl used i j r

  /-- `expr`, asked: the readings not through a coercion of its own, and
  through each coercion (`r`: the candidate productions, those that start
  with a token by the token, and the others); then remembered. -/
  def exprRead (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Nat → Option Nat → List Nat → Nat → Nat →
      Std.HashMap String (Array Nat) × Array Nat → CountM (Array (Reading × String))
    | 0, _, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, s, p, excl, used, i, j, (byTok, others) => do
      let key : ExprKey := (s, p, excl, used, i, j)
      let direct ← exprDirect A g ts fuel s p excl i j (byTok, others)
      let cands := (byTok.getD (ts.getD i "") #[] ++ others).toList
      let out ← coes A g ts fuel s p excl used i j cands direct
      modify fun st => { st with active := st.active.erase key, memo := st.memo.insert key out }
      if (← get).trace then
        let line := s!"{s} @{p} [{i},{j}) {ts.extract i j}: {out.map fun (r, so) => (r.text, so)}"
        modify fun st => { st with log := st.log.push line }
      return out

  /-- The readings not through a coercion of the question's own: by each
  candidate production (every one is tried, even after two readings, since
  a reading found again can be of another sort, which a hole's binding may
  need), in the emitter's parentheses and in a TeX group. They do not
  depend on the chain of coercions, so are remembered by the question less
  it. -/
  def exprDirect (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Nat → Option Nat → Nat → Nat →
      Std.HashMap String (Array Nat) × Array Nat → CountM (Array (Reading × String))
    | 0, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, s, p, excl, i, j, (byTok, others) => do
      let key := (s, p, excl, i, j)
      if let some n := (← get).memoD[key]? then return n
      let cands := (byTok.getD (ts.getD i "") #[] ++ others).toList
      let out ← prods A g ts fuel s p excl i j cands #[]
      let out ← parens A g ts fuel s p excl i j out
      let out ← groups A g ts fuel s p excl i j out
      modify fun st => { st with memoD := st.memoD.insert key out }
      return out

  /-- The readings in the emitter's parentheses, which do not print, onto
  `out`. -/
  def parens (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Nat → Option Nat → Nat → Nat → Array (Reading × String) → CountM (Array (Reading × String))
    | 0, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, s, _, _, i, j, out => do
      if j - i ≥ 3 && ts[i]? == some "(" && ts[j - 1]? == some ")" then
        keepM (·.1.text) (out ++ (← expr A g ts fuel s 0 none [] (i + 1) (j - 1)))
      else pure out

  /-- The readings in a TeX group (`{k_{1}}_{x}`), which does not print,
  onto `out`. -/
  def groups (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Nat → Option Nat → Nat → Nat → Array (Reading × String) → CountM (Array (Reading × String))
    | 0, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, s, p, _, i, j, out => do
      if j - i ≥ 3 && ts[i]? == some "{" && ts[j - 1]? == some "}" then
        keepM (·.1.text) (out ++ (← expr A g ts fuel s p none [] (i + 1) (j - 1)))
      else pure out

  /-- The readings by each production tried, onto `out`. The sort asked for
  binds the production's type variables first (`List(Char)` asked of
  `_ :: _ : List(?α)` makes `?α` `Char`), so its holes are asked at the sorts
  the context gives them. -/
  def prods (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Nat → Option Nat → Nat → Nat → List Nat → Array (Reading × String) →
      CountM (Array (Reading × String))
    | 0, _, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | _, _, _, _, _, _, [], out => pure out
    | fuel + 1, s, p, excl, i, j, k :: ks, out => do
      if !tried g ts p excl i j k then prods A g ts fuel s p excl i j ks out
      else
        let some (pr, body) := g.prods[k]? | prods A g ts fuel s p excl i j ks out
        let rs ← seq A g ts fuel body 0 (A.bind #[] pr.sort s) i j
        let out ← addProds A s pr rs.toList out
        prods A g ts fuel s p excl i j ks out

  /-- The readings through each coercion not on the chain already, onto
  `out`: its argument read, at the precedence asked for and under the same
  exclusion, with the coercion on the chain (`chainWith`). Coercions are invisible: a
  reading through one is its argument's, and its sort is the coercion's,
  with the argument's sort bound (`Option.some` of a label is an
  `Option(Label)`). -/
  def coes (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → String → Nat → Option Nat → List Nat → Nat → Nat → List Nat → Array (Reading × String) →
      CountM (Array (Reading × String))
    | 0, _, _, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | _, _, _, _, _, _, _, [], out => pure out
    | fuel + 1, s, p, excl, used, i, j, k :: ks, out => do
      let some (pr, body) := g.prods[k]? | coes A g ts fuel s p excl used i j ks out
      if !pr.coercion || used.contains k then coes A g ts fuel s p excl used i j ks out
      else
        let some (ASym.hole s' _ _) := body[0]? | coes A g ts fuel s p excl used i j ks out
        let env₀ := A.bind #[] pr.sort s
        let args ← expr A g ts fuel (A.expected env₀ s') p excl (chainWith k used) i j
        let out ← addCoes A s pr s' env₀ args.toList out
        coes A g ts fuel s p excl used i j ks out

  /-- Readings of `ts[i:j]` as `body[pos:]` under bindings `env`: the readings of its holes, variables and lists, and
  the bindings after them. -/
  def seq (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → Array ASym → Nat → Env → Nat → Nat → CountM (Array (Array Reading × Env))
    | 0, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, body, pos, env, i, j => do
      if (← get).steps > budget then
        modify fun st => { st with over := true }
        return #[]
      if pos == body.size then return if i == j then #[(#[], env)] else #[]
      let key := (body, pos, env, i, j)
      if let some n := (← get).memoSeq[key]? then return n
      seqFresh A g ts fuel body pos env i j

  /-- `seq`, when the question is not remembered: asked, and remembered. -/
  def seqFresh (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → Array ASym → Nat → Env → Nat → Nat → CountM (Array (Array Reading × Env))
    | 0, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, body, pos, env, i, j => do
      let key := (body, pos, env, i, j)
      modify fun st => { st with steps := st.steps + 1 }
      let n ← match body[pos]? with
        | some (.tok t) =>
          if i < j && ts[i]? == some t then seq A g ts fuel body (pos + 1) env (i + 1) j else pure #[]
        | some (.hole s p x) =>
          split A g ts fuel (fun env a b => do
              return (← expr A g ts fuel (A.expected env s) p x [] a b).map fun (r, so) => (#[r], A.bind env s so))
            body pos env i j
        | some .var =>
          split A g ts fuel (fun env a b => pure ((varOf g ts a b g.prods.toList).toArray.map (#[·], env)))
            body pos env i j
        | some (.tail l r) => split A g ts fuel (fun env a b => tail A g ts fuel l r env a b) body pos env i j
        | none => pure #[]
      modify fun st => { st with memoSeq := st.memoSeq.insert key n }
      return n

  /-- Readings of `ts[i:j]` as a nonterminal then `body[pos+1:]`. The
  nonterminal ends where what follows can still fit, and, if that is a
  token, where it stands. -/
  def split (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → (Env → Nat → Nat → CountM (Array (Array Reading × Env))) →
      Array ASym → Nat → Env → Nat → Nat → CountM (Array (Array Reading × Env))
    | 0, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, nt, body, pos, env, i, j => do
      if pos + 1 == body.size then return ← nt env i j
      let next : Option String := match body[pos + 1]? with
        | some (.tok t) => some t
        | _ => none
      -- Only the rest of a list can be empty.
      let start := match body[pos]? with
        | some (.tail ..) => i
        | _ => i + 1
      let last := j - minLenFrom body (pos + 1)
      splitAt A g ts fuel nt body pos env i j next (List.range' start (last + 1 - start)) #[]

  /-- The readings with the nonterminal ending at each of `ms`, onto `out`. -/
  def splitAt (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → (Env → Nat → Nat → CountM (Array (Array Reading × Env))) →
      Array ASym → Nat → Env → Nat → Nat → Option String → List Nat → Array (Array Reading × Env) →
      CountM (Array (Array Reading × Env))
    | 0, _, _, _, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | _, _, _, _, _, _, _, _, [], out => pure out
    | fuel + 1, nt, body, pos, env, i, j, next, m :: ms, out => do
      if (match next with | some t => ts[m]? != some t | none => false) then
        splitAt A g ts fuel nt body pos env i j next ms out
      else
        let as ← nt env i m
        let out ← splitRests A g ts fuel body pos m j as.toList out
        splitAt A g ts fuel nt body pos env i j next ms out

  /-- The readings with each reading of the nonterminal, then the rest of
  the body from `m`, onto `out`. -/
  def splitRests (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → Array ASym → Nat → Nat → Nat → List (Array Reading × Env) → Array (Array Reading × Env) →
      CountM (Array (Array Reading × Env))
    | 0, _, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | _, _, _, _, _, [], out => pure out
    | fuel + 1, body, pos, m, j, a :: more, out => do
      let rests ← seq A g ts fuel body (pos + 1) a.2 m j
      let out ← joinRests a rests.toList out
      splitRests A g ts fuel body pos m j more out

  /-- Readings of `ts[i:j]` as the rest of list `l`, `r` more required. -/
  def tail (A : SortAlgebra) (g : Grammar) (ts : Array String) :
      Nat → Nat → Nat → Env → Nat → Nat → CountM (Array (Array Reading × Env))
    | 0, _, _, _, _, _ => do modify fun st => { st with over := true }; return #[]
    | fuel + 1, l, r, env, i, j => do
      let out : Array (Array Reading × Env) := if r == 0 && i == j then #[(#[], env)] else #[]
      let some (elem, sep) := g.lists[l]? | return out
      if i < j then
        let more := sep ++ elem ++ #[ASym.tail l (r - 1)]
        keepM (fun (cs, _) => readingsKey cs) (out ++ (← seq A g ts fuel more 0 env i j))
      else pure out
end

/-- The fuel: more than any reading of `ts` consumes, each call and each
step of a loop taking one. -/
def fuelFor (g : Grammar) (ts : Array String) : Nat :=
  (3 * ts.size + 16) * (g.prods.size + 2 * variantCap * ts.size + 600)

/-- The readings of a whole formula as sort `s`: at most two. -/
def readings (A : SortAlgebra) (g : Grammar) (ts : Array String) (s : String) : CountM (Array Reading) := do
  let rs := (← expr A g ts (fuelFor g ts) s 0 none [] 0 ts.size).map (·.1)
  return rs.foldl (fun acc r => if acc.any (· == r) then acc else acc.push r) #[]

/-- Where the reader gave up, if it did. -/
structure Flags where
  /-- The work budget, or the fuel, ran out. -/
  over : Bool
  /-- A reading was dropped: a third one, or a variant past the cap. -/
  pruned : Bool
  /-- A question was cut, being already asked. -/
  cut : Bool
  /-- A list of the grammar takes no token per element (`listsWF`). -/
  lists : Bool
  deriving Inhabited, Repr

/-- The flags of a state after reading in grammar `g`. -/
def CState.flags (st : CState) (g : Grammar) : Flags :=
  { over := st.over || st.steps > budget, pruned := st.pruned, cut := st.cut, lists := !listsWF g }

/-- Whether the reading is not to be trusted: it gave up, dropped a
reading, cut a question, or the grammar has a list that takes no token. -/
def Flags.any (f : Flags) : Bool := f.over || f.pruned || f.cut || f.lists

/-- The readings (at most two) of a token sequence as an expression of sort
`s`, and where the reader gave up. -/
def readBackWith (A : SortAlgebra) (g : Grammar) (ts : Array String) (s : String) :
    Array Reading × Flags :=
  let p := (readings A g ts s).run {}
  (p.1, p.2.flags g)

/-- `readBackWith`, with a log of what was read where. -/
def readBackLogWith (A : SortAlgebra) (g : Grammar) (ts : Array String) (s : String) :
    Array Reading × Array String :=
  let p := (readings A g ts s).run { trace := true }
  (p.1, p.2.log)

end Imprimatur.Validate
