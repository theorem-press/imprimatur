/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Imprimatur.TeX

/-!
# The `lean` view

The declaration's signature as Lean prints it (DESIGN §7.3), with every token
wrapped in a semantic macro defined in `imprimatur.sty`, in the manner of
`agda.sty`:

| Macro | Token |
|---|---|
| `\LeanKeyword` | `theorem`, `def`, `fun`, … |
| `\LeanSort` | `Type`, `Prop`, `Sort` |
| `\LeanConst` | a name that resolves to a constant |
| `\LeanBound` | a bound variable or universe parameter |
| `\LeanNumber`, `\LeanString` | literals |

The whole is `\LeanCode{…}`, with lines separated by `\LeanNewline` and
indented with `\LeanIndent{n}`. There is no verbatim environment, so the
output works inside macro arguments.

The signature comes from `ppSignature`, so it reads exactly as Lean prints
it. Tokens are then classified by looking at the text and the environment
rather than the delaborator's internal structures, which keeps this stable
across toolchains.
-/

namespace Imprimatur.Views

open Lean Meta

/-- A token of printed Lean. -/
inductive Tok where
  /-- An identifier, possibly dotted. -/
  | ident (s : String)
  /-- A numeric literal. -/
  | num (s : String)
  /-- A string or character literal, with its quotes. -/
  | str (s : String)
  /-- Anything else, one character at a time. -/
  | sym (s : String)
  /-- A run of spaces. -/
  | space (n : Nat)
  deriving Repr, BEq, Inhabited

/-- Split one line of printed Lean into tokens. -/
def tokenize (line : String) : Array Tok := Id.run do
  let cs := line.toList.toArray
  let n := cs.size
  let mut out : Array Tok := #[]
  let mut i := 0
  while i < n do
    let c := cs[i]!
    if c == ' ' then
      let mut j := i
      while j < n && cs[j]! == ' ' do j := j + 1
      out := out.push (.space (j - i))
      i := j
    else if c == '«' then
      let mut j := i
      while j < n && cs[j]! != '»' do j := j + 1
      j := min n (j + 1)
      out := out.push (.ident (String.ofList (cs.extract i j).toList))
      i := j
    else if isIdFirst c then
      let mut j := i + 1
      let mut more := true
      while more do
        while j < n && isIdRest cs[j]! do j := j + 1
        -- A dot followed by the start of another component continues the name.
        if j + 1 < n && cs[j]! == '.' && isIdFirst cs[j + 1]! then j := j + 1
        else more := false
      out := out.push (.ident (String.ofList (cs.extract i j).toList))
      i := j
    else if c.isDigit then
      let mut j := i + 1
      while j < n && (cs[j]!.isAlphanum || cs[j]! == '_') do j := j + 1
      out := out.push (.num (String.ofList (cs.extract i j).toList))
      i := j
    else if c == '"' then
      let mut j := i + 1
      while j < n && cs[j]! != '"' do
        j := j + (if cs[j]! == '\\' then 2 else 1)
      j := min n (j + 1)
      out := out.push (.str (String.ofList (cs.extract i j).toList))
      i := j
    else
      out := out.push (.sym c.toString)
      i := i + 1
  return out

/-- Words printed as keywords. -/
def keywords : List String :=
  ["fun", "let", "have", "show", "from", "if", "then", "else", "match", "with", "do", "by",
   "at", "in", "where", "theorem", "def", "instance", "axiom", "opaque", "inductive",
   "structure", "class", "abbrev"]

/-- Words printed as sorts. -/
def sorts : List String := ["Type", "Prop", "Sort"]

/-- The names bound anywhere in an expression, and its universe parameters. -/
partial def boundNames (e : Expr) (acc : Array String := #[]) : Array String :=
  match e with
  | .forallE n t b _ | .lam n t b _ =>
    boundNames b (boundNames t (acc.push n.eraseMacroScopes.toString))
  | .letE n t v b _ => boundNames b (boundNames v (boundNames t (acc.push n.eraseMacroScopes.toString)))
  | .app f a => boundNames a (boundNames f acc)
  | .mdata _ b => boundNames b acc
  | .proj _ _ b => boundNames b acc
  | _ => acc

/-- What the `lean` view of a declaration needs to know about its context. -/
structure LeanCtx where
  /-- The environment. -/
  env : Environment
  /-- Namespaces treated as open when resolving names. -/
  openDecls : List OpenDecl
  /-- Names bound in the signature. -/
  bound : Array String

/-- Whether a printed identifier names a constant. -/
def LeanCtx.isConst (ctx : LeanCtx) (s : String) : Bool :=
  let n := s.splitOn "." |>.foldl (fun n c => Name.mkStr n c) .anonymous
  (ResolveName.resolveGlobalName ctx.env {} .anonymous ctx.openDecls n).any (·.2.isEmpty)

/-- Render one identifier. -/
def renderIdent (ctx : LeanCtx) (s : String) : String :=
  if sorts.contains s then s!"\\LeanSort\{{TeX.escape s}}"
  else if keywords.contains s then s!"\\LeanKeyword\{{TeX.escape s}}"
  else if ctx.bound.contains s then s!"\\LeanBound\{{TeX.escape s}}"
  else if ctx.isConst s then s!"\\LeanConst\{{TeX.escape s}}"
  else
    -- `p.fst` where `p` is bound: a projection out of a bound variable.
    match s.splitOn "." with
    | first :: rest@(_ :: _) =>
      if ctx.bound.contains first then
        s!"\\LeanBound\{{TeX.escape first}}" ++ TeX.escape ("." ++ ".".intercalate rest)
      else TeX.escape s
    | _ => TeX.escape s

/-- Render printed Lean as TeX. `declName` is the text the printer used for
the declaration's own name, which is replaced by `displayName`. -/
def renderLines (ctx : LeanCtx) (text declName displayName : String) : String := Id.run do
  let mut lines : Array String := #[]
  let mut first := true
  for line in text.splitOn "\n" do
    let toks := tokenize line
    let mut out := ""
    let mut leading := true
    for t in toks do
      match t with
      | .space k =>
        if leading then out := out ++ s!"\\LeanIndent\{{k}}"
        else if k == 1 then out := out ++ " "
        else out := out ++ s!"\\LeanSpace\{{k}}"
      | .ident s =>
        if first && s == declName then
          out := out ++ s!"\\LeanConst\{{TeX.escape displayName}}"
        else out := out ++ renderIdent ctx s
        first := false
      | .num s => out := out ++ s!"\\LeanNumber\{{TeX.escape s}}"
      | .str s => out := out ++ s!"\\LeanString\{{TeX.escape s}}"
      | .sym s => out := out ++ TeX.escape s
      leading := leading && (match t with | .space _ => true | _ => false)
    lines := lines.push out
  return "\\LeanCode{%\n" ++ "\\LeanNewline\n".intercalate lines.toList ++ "}"

/-- The keyword for a declaration. -/
def declKeyword (env : Environment) (c : ConstantInfo) : Option String :=
  match c with
  | .thmInfo _ => some "theorem"
  | .axiomInfo _ => some "axiom"
  | .opaqueInfo _ => some "opaque"
  | .defnInfo _ => some (if isInstanceCore env c.name then "instance" else "def")
  | .inductInfo _ => some (if isStructure env c.name then "structure" else "inductive")
  | _ => none

/-- Drop the longest of `namespaces` that prefixes `n`. -/
def stripName (namespaces : Array Name) (n : Name) : Name :=
  let best := namespaces.foldl (fun (b : Option Name) ns =>
    if ns.isPrefixOf n && ns != n then
      match b with
      | some b' => if b'.getNumParts < ns.getNumParts then some ns else some b'
      | none => some ns
    else b) none
  match best with
  | some ns => n.replacePrefix ns .anonymous
  | none => n

/-- The `lean` view of a constant. -/
def leanView (c : ConstantInfo) (strip : Array Name) (width : Nat) : MetaM String := do
  let env ← getEnv
  let openDecls := strip.toList.map (OpenDecl.simple · [])
  let fmt ← withTheReader Core.Context (fun ctx => { ctx with openDecls }) do
    PrettyPrinter.ppSignature c.name
  let text := fmt.fmt.pretty width
  if (← (IO.getEnv "IMPRIMATUR_TRACE" : IO _)) == some "1" then
    IO.eprintln s!"imprimatur-export: {c.name}: printed {text.length} characters"
  let bound := boundNames c.type (c.levelParams.toArray.map (·.toString))
  let ctx : LeanCtx := { env, openDecls, bound }
  -- The printer writes the declaration's own name first; find how.
  let declText := match (tokenize text).find? (fun t => match t with | .ident _ => true | _ => false) with
    | some (.ident s) => s
    | _ => c.name.toString
  let body := renderLines ctx text declText (stripName strip c.name).toString
  return match declKeyword env c with
    | some kw => body.replace "\\LeanCode{%\n" s!"\\LeanCode\{%\n\\LeanKeyword\{{kw}} "
    | none => body

end Imprimatur.Views
