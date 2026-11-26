/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Imprimatur.Notation
import Imprimatur.Commands
import Imprimatur.Validate

/-!
# What a reading denotes

DESIGN §18.4. A reading of a formula's TeX (`Validate.Reading`) is a tree:
the shapes of the notation rules' patterns, the built-in forms, and atoms.
Its *denotation* is the Lean term a reader who knows the notation takes it
for:

- a rule's node is its pattern instantiated at its children's denotations,
  with a fresh metavariable at every position the notation does not write
  (implicit and instance arguments, universe levels, hidden arguments and
  proofs);
- a built-in form is the binder, arrow or application it is;
- an atom is the variable, constant or literal it names, a numeral at a
  type to be found;
- and where a type does not fit, Lean's own coercion is inserted
  (`Meta.coerce?`), as a reader inserts it; the operands of a rule whose
  holes share a type are first brought to one type, as `binop%` does.

A reading is *well typed* when its denotation type-checks at the formula's
type, its instances found. `Render.validate` then asks that exactly one
reading be well typed, and that its denotation be definitionally equal, at
reducible transparency, to the expression rendered.

A λ over a pattern and a `case` analysis are not rebuilt: each denotes a
fresh metavariable, which takes whatever the formula has there, so the rest
of the formula is still checked. A form the denotation does not cover
otherwise raises an error, and the formula is reported as not validated.
-/

namespace Imprimatur

open Lean Meta

/-- An atom of a formula: what the formula's text names directly. -/
structure Atom where
  /-- Its TeX. -/
  tex : String
  /-- Its sort (`Validate`). -/
  sort : String
  /-- A bound variable's name, at its binder. -/
  isVar : Bool := false
  /-- The variable it is, if it is one. -/
  fvar : Option FVarId := none
  /-- The variable's name. -/
  name : String := ""
  /-- What it denotes (`Denote`): the variable, constant or literal it is;
  none for a bound variable's name at its binder. -/
  expr : Option Expr := none

namespace Denote

open Validate

/-- What the denotation of a formula's readings has to go on. -/
structure Ctx where
  /-- The notation rules in scope. -/
  rules : Array NotationRule
  /-- The coercion rules among them: a template that is one variable. -/
  coercions : Array NotationRule
  /-- The formula's atoms. -/
  atoms : Array Atom
  /-- The instance metavariables made so far. -/
  insts : IO.Ref (Array MVarId)
  /-- The coercions Lean inserted: each result with its argument, so that a
  skeleton can see through them (`skeleton`). -/
  coerced : IO.Ref (Array (Expr × Expr))
  /-- The fits put off until a sibling fixes a type (`fit`,
  `resolvePostponed`): a placeholder, the term it stands for, the depth of
  the fit, and whether it waits past the end of its node (`late`). -/
  postponed : IO.Ref (Array (Expr × Expr × Nat × Bool))
  /-- Whether `fit` may put a fit off; not while the postponed are resolved. -/
  postpone : Bool := true
  /-- Whether a fit put off for an open type expected waits past its node:
  the elements of a list literal do, since the list's type comes from where
  the list is. -/
  late : Bool := false

/-- Denotation: `MetaM` with the context. Errors are readings the
denotation does not cover, or ill-typed ones. -/
abbrev DenoteM := ReaderT Ctx MetaM

/-- The variables a rule shows, in pattern order: those its template
mentions and it does not hide. -/
def shownVars (r : NotationRule) : Array Name :=
  let inTemplate : Array String := match splitTemplate r.template (r.pat.vars.map (·.toString)) with
    | .ok parts => parts.filterMap fun | .inr v => some v | _ => none
    | .error _ => r.pat.vars.map (·.toString)
  r.pat.vars.filter fun v => inTemplate.contains v.toString && !(r.hides.any (·.1 == v))

/-- The variables of a pattern under one of its binders. -/
partial def underBinder : Pat → Array Name
  | .app _ args => args.foldl (· ++ underBinder ·) #[]
  | .constrained p _ => underBinder p
  | .lam _ b => b.vars
  | .pi _ d b => d.vars ++ b.vars
  | .arrow d c => underBinder d ++ underBinder c
  | _ => #[]

/-- Whether a rule's production is a coercion: it shows one variable and
nothing else. -/
def isCoercion (r : NotationRule) : Bool :=
  (Validate.ofRule r).any (·.coercion)

/-- Whether an instance problem is ready to be solved: its arguments other
than the class's out-parameters are known. Searching with an open argument
(`AddCommMonoid ?β`) would try every instance there is. -/
def readyToSynth (t : Expr) : MetaM Bool := do
  let t ← instantiateMVars t
  let .const cls _ := t.getAppFn | return !t.hasExprMVar
  let outs := (getOutParamPositions? (← getEnv) cls).getD #[]
  let args := t.getAppArgs
  for i in [0:args.size] do
    unless outs.contains i do
      if args[i]!.hasExprMVar then return false
  return true

/-- Find the instances made so far whose problems are ready; a stuck one
waits. As Lean's elaborator does, this fixes the out-parameters (`HAdd ℕ ℕ
?γ` gives `?γ := ℕ`), so that types are known when the next operand is fit. -/
def synthPendingInsts : DenoteM Unit := do
  -- An attempt rolled back leaves its metavariables behind in the list.
  let mctx ← getMCtx
  (← read).insts.modify (·.filter fun m => (mctx.findDecl? m).isSome)
  for m in ← (← read).insts.get do
    if ← m.isAssigned then continue
    let t ← instantiateMVars (← m.getType)
    unless ← readyToSynth t do continue
    match ← (observing? (synthInstance? t) : MetaM (Option (Option Expr))) with
    | some (some v) => discard <| isDefEq (mkMVar m) v
    | _ => pure ()

/-- IMPRIMATUR_DENOTE_TRACE=1 prints each step of a denotation, to see
where one that exhausts its budget was. -/
def trace (msg : MetaM String) : MetaM Unit := do
  if (← (IO.getEnv "IMPRIMATUR_DENOTE_TRACE" : IO _)) == some "1" then IO.eprintln s!"denote: {← msg}"

/-- The head constant of a function's result type, if it has one: what a
coercion rule can turn its argument into. -/
def resultHead (c : Name) : MetaM (Option Name) := do
  let some ci := (← getEnv).find? c | return none
  let mut ty := ci.type
  while ty.isForall do ty := ty.bindingBody!
  return ty.getAppFn.constName?

/-- A fresh metavariable for a binder the notation does not write. -/
def implicitMVar (d : Expr) (bi : BinderInfo) : DenoteM Expr := do
  let m ← mkFreshExprMVar d
  if bi.isInstImplicit then (← read).insts.modify (·.push m.mvarId!)
  pure m

/-- Whether `d` is a proposition: a proof is never written, so a binder
over one is filled by a metavariable. -/
def isPropDomain (d : Expr) : DenoteM Bool := do
  try isProp d catch _ => pure false

mutual
  /-- `a` where `d` is expected: as it is when its type unifies with `d`; as
  `fun h : c => a` where a function from a proof is expected, a branch of
  `if` being written as its value; else through the coercion Lean finds,
  else (if `coerce`) through a coercion rule of the notation whose result
  fits. -/
  partial def fit (a d : Expr) (depth : Nat := 3) : DenoteM Expr := do
    trace do return s!"fit {← ppExpr a} : {← ppExpr (← inferType a)} to {← ppExpr d}"
    let ta ← inferType a
    -- A value where a function from a proof is expected, before `ta`, which
    -- may be open, is unified with the function type.
    if let .forallE _ dom body _ := ← whnf d then
      if !body.hasLooseBVars && !(← whnf ta).isForall && (← isPropDomain dom) then
        if ← isDefEq ta body then return .lam `h dom a .default
    -- A fit a sibling may decide is put off (`resolvePostponed`), a
    -- placeholder standing in: an operand of known type where the type
    -- expected is still open (`"and" :: y`, where `y` fixes the element
    -- type, and `"and"` is then coerced to it); and an operand of open type
    -- (a bound variable at its first use) where a constructor the notation
    -- hides could take it to the type expected (`stmt(k) = S` for
    -- `W.stmt k = some S`, with `S` a statement by its next use). Unifying
    -- at once would fix the type the wrong way round.
    if (← read).postpone then
      let ta ← instantiateMVars ta
      let d' ← instantiateMVars d
      let hides ← match d'.getAppFn.constName? with
        | some h => (← read).coercions.anyM fun c => do return (← resultHead c.pat.head) == some h
        | none => pure false
      -- The first waits for the rest of its node's arguments, the second
      -- for the rest of the binder's scope.
      let byNode := d'.isMVar && !ta.hasExprMVar
      let byScope := ta.isMVar && !d'.isMVar && hides
      if byNode || byScope then
        let m ← mkFreshExprMVar d'
        (← read).postponed.modify (·.push (m, a, depth, byScope || (← read).late))
        trace do return s!"put off {← ppExpr a} : {← ppExpr ta} where {← ppExpr d'} is expected"
        return m
    if ← isDefEq ta d then return a
    -- A λ where a function type is expected: its binder takes the domain
    -- and its body is fit to the codomain, so that a coercion the notation
    -- hides in the body is found there (`λ r.\,r` for `fun r => ↑r`, the
    -- binder's type being open until now).
    if let .lam x t b bi := a then
      if let .forallE _ dom cod _ := ← whnf d then
        let s ← (saveState : MetaM Meta.SavedState)
        try
          unless ← isDefEq t dom do throwError "the binder's type does not match"
          return ← withLocalDecl x bi dom fun fv => do
            mkLambdaFVars #[fv] (← fit (b.instantiate1 fv) (cod.instantiate1 fv) depth)
        catch ex =>
          (restoreState s : MetaM Unit)
          -- The body may need a type that the node's result decides (the
          -- domain `?d.rows.El`, with `d` implicit and fixed by where the
          -- application goes): the λ is put off until then.
          if (← read).postpone && (← instantiateMVars d).hasExprMVar then
            let m ← mkFreshExprMVar d
            (← read).postponed.modify (·.push (m, a, depth, true))
            trace do return s!"put off {← ppExpr a} where {← ppExpr d} is expected, until its types are known"
            return m
          throw ex
    -- A pair where a pair type is expected: each component fit, so that a
    -- coercion the notation hides inside `(C, V)` is found there.
    if a.isAppOfArity ``Prod.mk 4 then
      if let .app (.app (.const `Prod _) α) β := ← whnf d then
        let x ← fit (a.getArg! 2) α depth
        let y ← fit (a.getArg! 3) β depth
        return ← mkAppOptM ``Prod.mk #[some α, some β, some x, some y]
    -- Coercions nest (`some (C, V)` with `V` itself coerced), to a depth.
    if depth == 0 then throwError "{← ppExpr a} : {← ppExpr ta} where {← ppExpr d} is expected"
    -- The notation's coercion rules first, those whose result can be `d`
    -- by its head; Lean's own search, which is costly, last, and only on
    -- closed types.
    let d ← instantiateMVars d
    let dHead := d.getAppFn.constName?
    for c in (← read).coercions do
      if let some h := dHead then
        if let some h' ← resultHead c.pat.head then
          if h != h' then continue
      let s ← (saveState : MetaM Meta.SavedState)
      let before ← (← read).insts.get
      try
        -- The coercion's result is `d` first, so that its argument is fit
        -- knowing what it must be (`some (c, v, i)` against an `Option` of
        -- a product with `v` coerced inside).
        let bare := match c.pat with
          | .app _ #[.var _] | .constrained (.app _ #[.var _]) _ => true
          | _ => false
        let a' ← if bare then do
            let f ← fillImplicits (← mkConstWithFreshMVarLevels c.pat.head)
            if let .forallE _ _ b _ := ← whnf (← inferType f) then
              if !b.hasLooseBVars then discard <| isDefEq b d
            applyArgs f [a] (coerced := true) (depth := depth - 1)
          else do
            -- A coercion whose pattern has fixed parts (`List.cons h List.nil`
            -- written `#h`, a one-element list as its element): the head
            -- applied to `a` and to the fixed parts, which must be constants.
            let strip : Pat → Pat := fun | .constrained q _ => q | q => q
            let .app _ pargs := strip c.pat | throwError "a coercion that is not an application"
            let args ← pargs.toList.mapM fun q => match strip q with
              | .var _ => pure a
              | .lit e => pure e
              | .app k #[] => do fillImplicits (← mkConstWithFreshMVarLevels k)
              | _ => throwError "a coercion with a part that is not a constant"
            let f ← fillImplicits (← mkConstWithFreshMVarLevels c.pat.head)
            applyArgs f args (coerced := true) (depth := depth - 1)
        if ← isDefEq (← inferType a') d then
          -- The coercion's instances must exist: `Int.cast` into `ℕ` does not.
          synthPendingInsts
          let mut ok := true
          for m in ← (← read).insts.get do
            if before.contains m then continue
            unless ← m.isAssigned do ok := false
          if ok then return a'
          trace do return s!"coercion {c.pat.head}: an instance is missing"
        else trace do return s!"coercion {c.pat.head}: {← ppExpr (← inferType a')} is not {← ppExpr d}"
      catch ex => trace do return s!"coercion {c.pat.head}: {← ex.toMessageData.toString}"
      (restoreState s : MetaM Unit)
    if !ta.hasExprMVar && !d.hasExprMVar then
      match ← coerce? a d with
      | .some a' =>
        (← read).coerced.modify (·.push (a', a))
        return a'
      | _ => pure ()
    throwError "{← ppExpr a} : {← ppExpr ta} where {← ppExpr d} is expected"

  /-- Fill the leading binders of `f` the notation does not write, up to its
  first explicit one that is not a proof. -/
  partial def fillImplicits (f : Expr) : DenoteM Expr := do
    let ty ← whnf (← inferType f)
    match ty with
    | .forallE _ d _ bi =>
      if bi.isExplicit && !(← isPropDomain d) then synthPendingInsts; pure f
      else fillImplicits (mkApp f (← implicitMVar d bi))
    | _ => synthPendingInsts; pure f

  /-- Apply `f` to the explicit arguments the text shows, in order: implicit
  and instance binders are filled by metavariables, and so are proof binders
  when `skipProofs` (the text never shows a proof; a pattern's arguments
  stand for every explicit binder); a function that is not one by its type
  is coerced to one, by Lean's coercion or by a coercion rule of the
  notation (once: `coerced`). -/
  partial def applyArgs (f : Expr) (args : List Expr) (coerced : Bool := false)
      (skipProofs : Bool := true) (depth : Nat := 3) : DenoteM Expr := do
    trace do return s!"apply {← ppExpr f} to {args.length} arguments"
    match args with
    | [] => fillImplicits f
    | a :: rest =>
      let ty ← whnf (← inferType f)
      match ty with
      | .forallE _ d _ bi =>
        if bi.isExplicit && !(skipProofs && (← isPropDomain d)) then
          let f' := mkApp f (← fit a d depth)
          synthPendingInsts
          applyArgs f' rest coerced skipProofs depth
        else applyArgs (mkApp f (← implicitMVar d bi)) args coerced skipProofs depth
      | .mvar _ =>
        -- Anything applied is a function of anything.
        let α ← mkFreshTypeMVar
        let β ← mkFreshTypeMVar
        unless ← isDefEq ty (← mkArrow α β) do throwError "{← ppExpr f} is applied, but is not a function"
        applyArgs f args coerced skipProofs depth
      | _ =>
        if let some f' ← coerceToFunction? f then return ← applyArgs f' args coerced skipProofs depth
        if coerced then throwError "{← ppExpr f} is applied, but is not a function"
        for c in (← read).coercions do
          let s ← (saveState : MetaM Meta.SavedState)
          try
            let f' ← applyArgs (← mkConstWithFreshMVarLevels c.pat.head) [f] (coerced := true)
            if (← whnf (← inferType f')).isForall then
              return ← applyArgs f' args (coerced := true) skipProofs
          catch _ => pure ()
          (restoreState s : MetaM Unit)
        throwError "{← ppExpr f} is applied, but is not a function"
end

/-- Resolve the fits put off (`fit`), at the end of a node: each whose
types are now known, each that waited for this node's arguments, and, when
`force`, each that `may` be forced, is fit as it stands, through a coercion
where one is needed; the rest wait on. The instances the types decide are
then found, as after any argument. Placeholders of attempts rolled back are
dropped. -/
def resolvePostponed (force : Bool) (may : MVarId → Bool := fun _ => true) : DenoteM Unit := do
  let ref := (← read).postponed
  let mctx ← getMCtx
  let mut pending := (← ref.get).filter fun (m, _, _, _) => (mctx.findDecl? m.mvarId!).isSome
  ref.set #[]
  let mut keep := #[]
  let mut resolved := false
  -- A variable of open type used at several types, each able to hide a
  -- constructor (`qs` in `ctors(S) = qs ∧ … print*(qs)`, for `some qs` and
  -- `qs`): its type is the one of its uses at which the others fit, through
  -- the constructors they hide. The first use would otherwise decide.
  if force then
    let mut solved : Array MVarId := #[]
    for (_, a, _, late) in pending do
      let group := pending.filter fun (m', a', _, _) => a' == a && !solved.contains m'.mvarId!
      if group.size < 2 || !late then continue
      let ta ← instantiateMVars (← inferType a)
      unless ta.isMVar do continue
      for (mc, _, _, _) in group do
        let st ← (saveState : MetaM Meta.SavedState)
        let ok ← try
            let dc ← instantiateMVars (← inferType mc)
            unless ← isDefEq ta dc do throwError "no"
            for (m, a, depth, _) in group do
              let d ← instantiateMVars (← inferType m)
              let a' ← withReader (fun c => { c with postpone := false }) (fit a d depth)
              unless ← isDefEq m a' do throwError "no"
            pure true
          catch _ => pure false
        if ok then
          trace do return s!"{← ppExpr a} is of the type {← ppExpr (← instantiateMVars (← inferType mc))}"
          solved := solved ++ group.map (·.1.mvarId!)
          resolved := true
          break
        else (restoreState st : MetaM Unit)
    pending := pending.filter fun (m, _, _, _) => !solved.contains m.mvarId!
  for (m, a, depth, late) in pending do
    if ← m.mvarId!.isAssigned then continue
    let ta ← instantiateMVars (← inferType a)
    let d ← instantiateMVars (← inferType m)
    -- A λ put off waits while the function type expected has open parts.
    let lamOpen := a.isLambda && d.hasExprMVar
    if ((d.isMVar || ta.isMVar) && late || lamOpen) && !(force && may m.mvarId!) then
      keep := keep.push (m, a, depth, late)
      continue
    trace do return s!"resolve {← ppExpr a} : {← ppExpr ta} where {← ppExpr d} is expected"
    let a' ← withReader (fun c => { c with postpone := false }) (fit a d depth)
    unless ← isDefEq m a' do throwError "{← ppExpr a'} is not of the type {← ppExpr d}"
    resolved := true
  ref.modify (keep ++ ·)
  if resolved then synthPendingInsts

/-- A computation under a binder: the fits put off inside it are resolved
before the binder closes, since they may mention its variable. -/
def inScope (x : DenoteM Expr) : DenoteM Expr := do
  let before := (← (← read).postponed.get).map (·.1.mvarId!)
  let e ← x
  resolvePostponed (force := true) (may := fun m => !before.contains m)
  instantiateMVars e

/-- A variable's denotation, to be computed when the binder it is under has
its type: the body of `fun i => f` is read with `i`'s type known. -/
abbrev Thunks := Array (Name × DenoteM Expr)

mutual
  /-- The term a pattern stands for, with `bs` for its variables and `lazy`
  for those read on demand: a variable neither binds, and a wildcard, is a
  fresh metavariable; a literal is itself; a binder's variable is the local
  `bs` gives it, typed by `expected` when that is a function type. -/
  partial def ofPat (p : Pat) (bs : Array (Name × Expr)) (lazy : Thunks := #[])
      (expected : Option Expr := none) : DenoteM Expr := do
    match p with
    | .var n =>
      match bs.find? (·.1 == n) with
      | some (_, e) => pure e
      | none =>
        match lazy.find? (·.1 == n) with
        | some (_, k) => k
        | none => mkFreshExprMVar none
    | .wild => mkFreshExprMVar none
    | .lit e => pure e
    | .constrained q cs =>
      let e ← ofPat q bs lazy expected
      let args := e.getAppArgs
      for (i, c) in cs do
        let some a := args[i]? | throwError "a constrained argument is missing"
        let ce ← ofPat c bs lazy
        unless ← isDefEq a ce do throwError "a constrained argument does not match"
      pure e
    | .app h ps => applyPats (← mkConstWithFreshMVarLevels h) ps.toList bs lazy
    | .lam x body =>
      -- A binder the rule's node did not bind (one inside a constraint,
      -- `(fun _ => ENNReal)`) is a local of its own.
      let some (_, fv) := bs.find? (·.1 == x)
        | withLocalDeclD x (← mkFreshTypeMVar) fun fv => do
            mkLambdaFVars #[fv] (← inScope (ofPat body (bs.push (x, fv)) lazy))
      if let some d := expected then
        if let .forallE _ dom _ _ := ← whnf d then discard <| isDefEq (← inferType fv) dom
      mkLambdaFVars #[fv] (← ofPat body bs lazy)
    | .pi x dom body =>
      let d ← ofPat dom bs lazy
      let some (_, fv) := bs.find? (·.1 == x)
        | withLocalDeclD x d fun fv => do mkForallFVars #[fv] (← inScope (ofPat body (bs.push (x, fv)) lazy))
      unless ← isDefEq (← inferType fv) d do throwError "the binder's type does not match"
      mkForallFVars #[fv] (← ofPat body bs lazy)
    | .arrow dom cod => mkArrow (← ofPat dom bs lazy) (← ofPat cod bs lazy)

  /-- Apply `f` to the patterns of a rule's explicit arguments, each read
  where its binder's type is known. -/
  partial def applyPats (f : Expr) (ps : List Pat) (bs : Array (Name × Expr)) (lazy : Thunks) :
      DenoteM Expr := do
    match ps with
    | [] => fillImplicits f
    | p :: rest =>
      let ty ← whnf (← inferType f)
      match ty with
      | .forallE _ d _ bi =>
        if bi.isExplicit then
          let a ← ofPat p bs lazy (some d)
          let f' := mkApp f (← fit a d)
          synthPendingInsts
          applyPats f' rest bs lazy
        else applyPats (mkApp f (← implicitMVar d bi)) ps bs lazy
      | _ =>
        let a ← ofPat p bs lazy
        applyPats (← applyArgs f [a] (skipProofs := false)) rest bs lazy
end

/-- Bindings for a rule's hidden variables: the pattern each must match,
instantiated (`hide ρ := Fin.elim0` gives that constant; `hide h := _` a
metavariable). -/
def hiddenBindings (r : NotationRule) : DenoteM (Array (Name × Expr)) :=
  r.hides.mapM fun (x, p) => do pure (x, ← ofPat p #[])

/-- A numeral: `OfNat.ofNat` at a type to be found. -/
def numeral (n : Nat) : DenoteM Expr := do
  let u ← mkFreshLevelMVar
  let α ← mkFreshExprMVar (mkSort (mkLevelSucc u))
  let inst ← mkFreshExprMVar (mkApp2 (mkConst ``OfNat [u]) α (mkRawNatLit n))
  (← read).insts.modify (·.push inst.mvarId!)
  pure (mkApp3 (mkConst ``OfNat.ofNat [u]) α (mkRawNatLit n) inst)

/-- The variables of a rule's pattern that a default instance of its head's
class makes of one type, as `binop%` does for `a ++ b`: `HAppend.hAppend a
b` has `a : α` and `b : β`, and the default `HAppend α α α` ties them.
Empty when the head has no class with a default instance, or the pattern
is not the head at variables. -/
def defaultGroup (r : NotationRule) : MetaM (Array Name) := do
  let .app h args := r.pat | return #[]
  let some ci := (← getEnv).find? h | return #[]
  let (ms, bis, _) ← forallMetaTelescope ci.type
  let some i := bis.findIdx? (·.isInstImplicit) | return #[]
  let ty ← instantiateMVars (← inferType ms[i]!)
  let some cls := ty.getAppFn.constName? | return #[]
  let params := ty.getAppArgs
  for (inst, _) in ← getDefaultInstances cls do
    let (_, _, ity) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels inst))
    let cargs := ity.getAppArgs
    if cargs.size != params.size then continue
    -- The parameters the default instance makes one: those at positions
    -- whose arguments are the same metavariable as the first's.
    let tied := (List.range cargs.size).filter fun k => cargs[k]! == cargs[0]!
    if tied.length < 2 then continue
    let tiedParams := tied.map fun k => params[k]!
    -- The explicit binders typed by one of them, and the pattern's
    -- variables at those binders.
    let mut vars := #[]
    let mut e := 0
    for j in [0:bis.size] do
      unless bis[j]!.isExplicit do continue
      let d ← instantiateMVars (← inferType ms[j]!)
      if tiedParams.any (· == d) then
        if let some (Pat.var v) := args[e]? then vars := vars.push v
      e := e + 1
    if vars.size ≥ 2 then return vars
  return #[]

/-- Bring the operands of a rule whose holes share a type variable to one
type, as `binop%` does: when their types differ, the first type every
operand fits, through a coercion where needed. -/
def homogenise (r : NotationRule) (bs : Array (Name × Expr)) : DenoteM (Array (Name × Expr)) := do
  let mut bs := bs
  let mut groups : Array (String × Array Name) := r.holeSorts.foldl (init := #[]) fun acc (v, s) =>
    if !isTyVar s || s.any (· == '(') then acc
    else match acc.findIdx? (·.1 == s) with
      | some i => acc.modify i fun (s, vs) => (s, vs.push v)
      | none => acc.push (s, #[v])
  -- Holes of their own type variables that the head's default instance
  -- ties (`a ++ b`).
  if groups.all (·.2.size < 2) then
    let tied ← defaultGroup r
    if tied.size ≥ 2 then groups := groups.push ("default", tied)
  for (_, vs) in groups do
    let members := vs.filterMap fun v => bs.find? (·.1 == v)
    if members.size < 2 then continue
    let tys ← members.mapM fun (_, e) => do instantiateMVars (← inferType e)
    let concrete := tys.filter fun t => !t.hasExprMVar
    let some t₀ := concrete[0]? | continue
    let mut same := true
    for t in concrete do
      unless ← isDefEq t t₀ do same := false
    if same then
      -- An operand whose type is open takes the others', or is coerced to
      -- it (`Subtype.mk a` beside `a`, through `Subtype.val`).
      for ((v, e), t) in members.zip tys do
        if t.hasExprMVar then
          try
            let e' ← fit e t₀
            bs := bs.map fun (v', e'') => if v' == v then (v, e') else (v', e'')
          catch _ => pure ()
      continue
    let mut chosen : Option Expr := none
    let ctx ← read
    for t in concrete do
      if chosen.isSome then break
      let test : MetaM Bool := withoutModifyingState do
        try
          for (_, e) in members do discard <| (fit e t).run { ctx with postpone := false }
          pure true
        catch _ => pure false
      if ← test then chosen := some t
    if let some t := chosen then
      for (v, e) in members do
        let e' ← fit e t
        bs := bs.map fun (v', e'') => if v' == v then (v, e') else (v', e'')
  pure bs

mutual
  /-- What a reading denotes, under the bound variables in scope. -/
  partial def denote (r : Reading) (bound : List (String × Expr)) : DenoteM Expr := do
    trace do return s!"reading {r.text}"
    match r with
    | .node name [] => leaf name bound
    | .node name kids =>
      let e ← node name kids bound
      resolvePostponed (force := false)
      pure e

  /-- A leaf: a bound variable, an atom, or a rule that shows no variable. -/
  partial def leaf (name : String) (bound : List (String × Expr)) : DenoteM Expr := do
    if let some (_, e) := bound.find? (·.1 == name) then return e
    if let some a := (← read).atoms.find? fun a => a.tex == name && !a.isVar then
      match a.expr with
      | some (.lit (.natVal n)) => numeral n
      | some (.const c _) => fillImplicits (← mkConstWithFreshMVarLevels c)
      | some e => pure e
      | none => throwError "the atom {name} denotes nothing"
    else ruleNode name [] bound

  /-- A node: a built-in form, or a rule's. -/
  partial def node (name : String) (kids : List Reading) (bound : List (String × Expr)) :
      DenoteM Expr := do
    match name, kids with
    | "app", f :: args =>
      let f ← denote f bound
      let args ← args.mapM (denote · bound)
      applyArgs f args
    | "implication", [a, b] | "function type", [a, b] =>
      mkArrow (← denote a bound) (← denote b bound)
    | "∀", [.node v [], t, body] =>
      let ty ← denote t bound
      withLocalDeclD (Name.mkSimple v) ty fun x =>
        do mkForallFVars #[x] (← inScope (denote body ((v, x) :: bound)))
    | "bounded ∀", [.node v [], s, body] =>
      let s ← denote s bound
      withLocalDeclD (Name.mkSimple v) (← mkFreshTypeMVar) fun x => do
        let mem ← applyArgs (← mkConstWithFreshMVarLevels ``Membership.mem) [s, x]
        mkForallFVars #[x] (← inScope do mkArrow mem (← denote body ((v, x) :: bound)))
    | "∃", [.node v [], body] =>
      withLocalDeclD (Name.mkSimple v) (← mkFreshTypeMVar) fun x => do
        let p ← mkLambdaFVars #[x] (← inScope (denote body ((v, x) :: bound)))
        applyArgs (← mkConstWithFreshMVarLevels ``Exists) [p]
    | "bounded ∃", [.node v [], s, body] =>
      let s ← denote s bound
      withLocalDeclD (Name.mkSimple v) (← mkFreshTypeMVar) fun x => do
        let mem ← applyArgs (← mkConstWithFreshMVarLevels ``Membership.mem) [s, x]
        let p ← mkLambdaFVars #[x] (← inScope do return mkAnd mem (← denote body ((v, x) :: bound)))
        applyArgs (← mkConstWithFreshMVarLevels ``Exists) [p]
    | "λ", [.node v [], body] =>
      withLocalDeclD (Name.mkSimple v) (← mkFreshTypeMVar) fun x =>
        do mkLambdaFVars #[x] (← inScope (denote body ((v, x) :: bound)))
    -- A λ over a pattern and a case analysis stand for any subterm: the
    -- metavariable takes what the formula has there (#41's remaining gap).
    | "λ", _ => mkFreshExprMVar none
    | "case", _ => mkFreshExprMVar none
    | "list", elems =>
      let es ← elems.mapM (denote · bound)
      let u ← mkFreshLevelMVar
      let α ← mkFreshExprMVar (mkSort (mkLevelSucc u))
      let nil := mkApp (mkConst ``List.nil [u]) α
      -- The elements wait for the list's type, which comes from where the
      -- list is: `[" be types"]` where tokens are expected.
      withReader (fun c => { c with late := true }) do
        es.foldrM (init := nil) fun e acc => do
          pure (mkApp3 (mkConst ``List.cons [u]) α (← fit e α) acc)
    | _, _ => ruleNode name kids bound

  /-- A rule's node: the rules whose pattern has this shape, tried in turn. -/
  partial def ruleNode (name : String) (kids : List Reading) (bound : List (String × Expr)) :
      DenoteM Expr := do
    -- A synonym's pattern reads nothing by itself; a reading rewritten to
    -- its shape (`Render.rewriteSynonyms`) is denoted by it.
    let all := (← read).rules
    let rules := all.filter fun r => !r.synonym && r.pat.shape == name
    let rules := if rules.isEmpty then all.filter fun r => r.synonym && r.pat.shape == name else rules
    if rules.isEmpty then throwError "no rule reads as {name}"
    let mut last : Option Exception := none
    for r in rules do
      let s ← (saveState : MetaM Meta.SavedState)
      try
        return ← ruleWith r kids bound
      catch ex =>
        (restoreState s : MetaM Unit)
        last := some ex
    match last with
    | some ex => throw ex
    | none => throwError "no rule reads as {name}"

  /-- A node of rule `r`: a chain, folded binders, or the pattern at its
  shown variables, with any further children applied as arguments. -/
  partial def ruleWith (r : NotationRule) (kids : List Reading) (bound : List (String × Expr)) :
      DenoteM Expr := do
    trace do return s!"rule {r.pat.head} with {kids.length} parts"
    let vars := shownVars r
    if r.flatten then
      if let some (x, p) := r.pat.binder? then
        unless vars == #[x, p] do throwError "a folded binder with other variables"
        let some body := kids.getLast? | throwError "a fold without a body"
        let names ← kids.dropLast.mapM fun
          | .node v [] => pure v
          | _ => throwError "a folded binder that is not a name"
        if names.isEmpty then throwError "a fold without variables"
        return ← foldBinders r x p names body bound
      else
        let ops ← kids.mapM (denote · bound)
        let #[a, b] := vars | throwError "a chain of a rule without two variables"
        if ops.length < 2 then throwError "a chain with one operand"
        let hidden ← hiddenBindings r
        let step (l rt : Expr) : DenoteM Expr := do
          let bs ← homogenise r #[(a, l), (b, rt)]
          ofPat r.pat (hidden ++ bs)
        -- Bracketed as the rule's associativity has it; where the types
        -- decide otherwise (`(a, b, c)` nests to the right), the other way.
        let leftward : DenoteM Expr := ops.tail!.foldlM (init := ops.head!) step
        let rightward : DenoteM Expr := do
          let rev := ops.reverse
          rev.tail!.foldlM (init := rev.head!) fun acc o => step o acc
        -- Operands of different types (`(a, b, c)`, where the holes have
        -- their own type variables) nest to the right, as Lean's notations do.
        let heterogeneous := (r.holeSorts.filterMap fun (v, so) =>
          if v == a || v == b then some so else none).toList.eraseDups.length > 1
        let (first, second) :=
          if r.assoc == "right" || heterogeneous then (rightward, leftward) else (leftward, rightward)
        let s ← (saveState : MetaM Meta.SavedState)
        try
          return ← first
        catch _ =>
          (restoreState s : MetaM Unit)
          return ← second
    if kids.length < vars.size then throwError "too few parts for the rule"
    let mine := kids.take vars.size
    let extra := kids.drop vars.size
    let binders := r.pat.binderVars
    let pairs := (vars.toList.zip mine)
    -- A binder that is a pattern (`λ (a, b). e`) makes the node stand for
    -- any subterm, as the built-in λ does.
    if pairs.any fun (v, k) => binders.contains v && (match k with | .node _ [] => false | _ => true) then
      return ← mkFreshExprMVar none
    let binderPairs ← pairs.filterMapM fun (v, k) =>
      if binders.contains v then
        match k with
        | .node n [] => pure (some (v, some n))
        | _ => throwError "a binder that is not a name"
      else pure none
    -- A binder the template does not show (`fun _ => t` in a rule for `if`)
    -- is a local with no name in the text.
    let hidden := binders.filter (!vars.contains ·)
    let binderPairs := binderPairs ++ (hidden.map fun v => (v, none)).toList
    -- A variable under a binder is read when the binder's type is known.
    let under := underBinder r.pat
    -- A rule with binders is a scope: what is put off under them is
    -- resolved before they close.
    let scope (x : DenoteM Expr) : DenoteM Expr := if binderPairs.isEmpty then x else inScope x
    withBinders binderPairs #[] bound fun bs0 bound' => scope do
      let mut bs := bs0
      let mut lazy : Thunks := #[]
      for (v, k) in pairs do
        unless binders.contains v do
          if under.contains v then lazy := lazy.push (v, denote k bound')
          else bs := bs.push (v, ← denote k bound')
      trace do return "homogenise"
      let bs' ← homogenise r bs
      trace do return "pattern"
      let e ← ofPat r.pat ((← hiddenBindings r) ++ bs') lazy
      trace do return "extra"

      applyArgs e (← extra.mapM (denote · bound'))

  /-- Locals for a rule's binder variables, each named as the text names it. -/
  partial def withBinders (binders : List (Name × Option String)) (acc : Array (Name × Expr))
      (bound : List (String × Expr))
      (k : Array (Name × Expr) → List (String × Expr) → DenoteM Expr) : DenoteM Expr := do
    match binders with
    | [] => k acc bound
    | (v, some n) :: rest =>
      withLocalDeclD (Name.mkSimple n) (← mkFreshTypeMVar) fun fv =>
        withBinders rest (acc.push (v, fv)) ((n, fv) :: bound) k
    | (v, none) :: rest =>
      withLocalDeclD v (← mkFreshTypeMVar) fun fv =>
        withBinders rest (acc.push (v, fv)) bound k

  /-- Folded binders, `∃ x y, p`: the rule once for each variable, from the inside. -/
  partial def foldBinders (r : NotationRule) (x p : Name) (names : List String) (body : Reading)
      (bound : List (String × Expr)) : DenoteM Expr := do
    match names with
    | [] => denote body bound
    | n :: rest =>
      withLocalDeclD (Name.mkSimple n) (← mkFreshTypeMVar) fun fv => inScope do
        let inner ← foldBinders r x p rest body ((n, fv) :: bound)
        ofPat r.pat ((← hiddenBindings r) ++ #[(x, fv), (p, inner)])
end

/-- With room to unfold: Lean's own elaborator is given more than its
default recursion depth for a statement over a large library. -/
def withDepth {α : Type} (x : MetaM α) : MetaM α :=
  withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 2048 }) x

/-- A reading's denotation: its term, the instance metavariables made for
it, and the coercions Lean inserted in it. -/
structure Denotation where
  /-- The term. -/
  term : Expr
  /-- The instance metavariables. -/
  insts : Array MVarId
  /-- Each coercion inserted, with its argument. -/
  coerced : Array (Expr × Expr)
  deriving Inhabited

/-- The denotation of a reading; or why the denotation does not cover it,
the metavariable context then as it was. -/
def run (rules : Array NotationRule) (atoms : Array Atom) (r : Reading) (τ : Option Expr := none) :
    MetaM (Except String Denotation) := do
  let insts ← IO.mkRef #[]
  let coerced ← IO.mkRef #[]
  let postponed : IO.Ref (Array (Expr × Expr × Nat × Bool)) ← IO.mkRef #[]
  let coercions := rules.filter isCoercion
  trace do return s!"coercions: {coercions.map (·.pat.head)}"
  let s ← saveState
  try
    -- With the elaborator's approximations: a binder's type is found from
    -- a use inside the binder's scope. The whole is fit to the type
    -- expected, as an argument is: a variable `x` written for `Tm.var x`
    -- goes through the coercion rule that hides the constructor.
    let e ← withDepth <| approxDefEq <| (do
      let e ← denote r []
      let e ← match τ with
        | some τ => fit e τ
        | none => pure e
      resolvePostponed (force := true)
      instantiateMVars e).run { rules, coercions, atoms, insts, coerced, postponed }
    return .ok { term := e, insts := ← insts.get, coerced := ← coerced.get }
  catch ex =>
    let msg ← ex.toMessageData.toString
    restoreState s
    return .error msg

/-! ## Skeletons

What a reader sees of a term: its heads and explicit arguments, with the
implicit arguments, instances, universe levels, binder types, proofs,
invisible coercions and the types of numerals left out. Two terms with the
same skeleton say the same thing up to what the notation does not write. -/

/-- A skeleton. -/
inductive Skel where
  /-- A node: a head, and its explicit arguments. -/
  | node (head : String) (kids : List Skel)
  /-- A metavariable, which stands for anything. -/
  | any
  deriving Inhabited, Repr

mutual
  /-- Skeletons equal, `any` for anything. -/
  partial def Skel.eq : Skel → Skel → Bool
    | .any, _ | _, .any => true
    | .node h ks, .node h' ks' => h == h' && Skel.eqList ks ks'
  /-- See `Skel.eq`. -/
  partial def Skel.eqList : List Skel → List Skel → Bool
    | [], [] => true
    | k :: ks, k' :: ks' => Skel.eq k k' && Skel.eqList ks ks'
    | _, _ => false
end

/-- The operands of a chain of a flattening rule, however it is bracketed. -/
partial def chainOperands (r : NotationRule) (e : Expr) : MetaM (Array Expr) := do
  match ← r.tryMatch e with
  | some bs =>
    let vs := r.pat.vars
    match vs[0]?.bind (fun v => bs.find? (·.1 == v)), vs[1]?.bind (fun v => bs.find? (·.1 == v)) with
    | some (_, a), some (_, b) => return (← chainOperands r a) ++ (← chainOperands r b)
    | _, _ => return #[e]
  | none => return #[e]

/-- The rules that flatten a chain, which the notation declares associative. -/
def chainRules (rules : Array NotationRule) : Array NotationRule :=
  rules.filter fun r => r.flatten && r.pat.binder?.isNone && !r.synonym

/-- The skeleton of a term, under the notation's coercion rules, its chain
rules and the coercions `coerced` inserted. Bound variables are de Bruijn
indices, so skeletons are equal up to renaming; a chain is flat, however
it was bracketed. -/
partial def skeleton (coercions : Array NotationRule) (e : Expr) (coerced : Array (Expr × Expr) := #[])
    (chains : Array NotationRule := #[]) : MetaM Skel := do
  let e := e.consumeMData
  -- A coercion Lean inserted is its argument.
  for (c, a) in coerced do
    if (← instantiateMVars c) == e then return ← skeleton coercions (← instantiateMVars a) coerced chains
  -- A chain is its operands, flat.
  if !e.hasLooseBVars then
    for r in chains do
      if (← r.tryMatch e).isSome then
        let ops ← chainOperands r e
        if ops.size ≥ 3 then
          return .node s!"chain {r.pat.head}" (← ops.toList.mapM (skeleton coercions · coerced chains))
  match e with
  | .mvar _ => return .any
  | .bvar i => return .node s!"#{i}" []
  | .fvar f => return .node s!"{f.name}" []
  | .sort _ => return .node "Sort" []
  | .lit (.natVal n) => return .node s!"{n}" []
  | .lit (.strVal v) => return .node s!"\"{v}\"" []
  | .const c _ => return .node c.toString []
  | .lam _ t b _ =>
    -- A λ over a proof is its body, as the renderer writes it: the proof
    -- is not written where the body uses it either, so a reading has a
    -- metavariable there, which is left out of the skeleton as proofs are.
    if !t.hasLooseBVars && (← (try Meta.isProp t catch _ => pure false)) then
      return ← skeleton coercions b coerced chains
    return .node "λ" [← skeleton coercions b coerced chains]
  | .forallE _ t b _ => return .node "∀" [← skeleton coercions t, ← skeleton coercions b coerced chains]
  | .letE _ _ v b _ => skeleton coercions (b.instantiate1 v) coerced chains
  | .proj _ i x => return .node s!".{i}" [← skeleton coercions x coerced chains]
  | .app .. =>
    let f := e.getAppFn
    if let .mvar _ := f then return .any
    -- A numeral is its value.
    if e.isAppOfArity ``OfNat.ofNat 3 then
      if let .lit (.natVal n) := e.getArg! 1 |>.consumeMData then return .node s!"{n}" []
    let shown ← match f with
      | .const h _ =>
        -- An invisible coercion is its argument.
        if coercions.any (·.pat.head == h) then
          if let some (_, #[a]) ← explicitArgsLoose e then return ← skeleton coercions a coerced chains
        -- The explicit arguments that are not proofs, by the binders'
        -- types: a proof the notation hides is a metavariable, which says
        -- nothing of itself.
        match (← getEnv).find? h with
        | some ci =>
          let mut ty := ci.type
          let mut out := #[]
          for a in e.getAppArgs do
            match ty with
            | .forallE _ d b bi =>
              if bi.isExplicit then
                let isProp ← (try Meta.isProp d catch _ => pure false)
                unless isProp do out := out.push a
              ty := b.instantiate1 a
            | _ => out := out.push a
          pure out
        | none => pure e.getAppArgs
      | _ =>
        -- Proofs are not written.
        e.getAppArgs.filterM fun a => do
          if a.hasLooseBVars then pure true else return !(← (try isProof a catch _ => pure false))
    let head ← match f with
      | .const h _ => pure h.toString
      | _ => pure ""
    let kids ← shown.toList.mapM (skeleton coercions · coerced chains)
    let fk ← match f with
      | .const .. => pure []
      | _ => pure [← skeleton coercions f coerced chains]
    return .node head (fk ++ kids)
  | _ => return .node "?" []

/-- Whether two terms have the same skeleton, the second under the
coercions inserted in it. -/
def sameSkeleton (rules : Array NotationRule) (a b : Expr) (coerced : Array (Expr × Expr)) :
    MetaM Bool := do
  let coercions := rules.filter isCoercion
  let chains := chainRules rules
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  return Skel.eq (← skeleton coercions a #[] chains) (← skeleton coercions b coerced chains)

/-- Whether a denotation is well typed at `τ`: it type-checks, its type
unifies with `τ`, and each instance whose type is known is found. The
assignments this makes are kept when it is. -/
def wellTyped (e : Expr) (insts : Array MVarId) (τ : Option Expr) : MetaM Bool := do
  let r ← observing? <| withDepth <| approxDefEq do
    check e
    if let some τ := τ then
      unless ← isDefEq (← inferType e) τ do throwError "not of the type expected"
    let mctx ← getMCtx
    for m in insts do
      if (mctx.findDecl? m).isNone then continue
      if ← m.isAssigned then continue
      let t ← instantiateMVars (← m.getType)
      match ← observing? (synthInstance? t) with
      | some (some v) =>
        unless ← isDefEq (mkMVar m) v do throwError "another instance"
      | _ => if !t.hasMVar then throwError "no instance"
  return r.isSome

/-- Whether the expression rendered and a denotation agree: definitionally
equal at reducible transparency; or, failing that, of the same skeleton,
since the text does not write the coercions and the types of numerals that
tell `(n : ℝ) = m` from `n = m`. -/
def agrees (rules : Array NotationRule) (orig : Expr) (d : Denotation) : MetaM Bool := do
  let r ← observing? <| withDepth <| approxDefEq do
    unless ← withReducible (isDefEq orig d.term) do throwError "differ"
  if r.isSome then return true
  let bySkeleton ← sameSkeleton rules orig d.term d.coerced
  -- IMPRIMATUR_VALIDATE_DEBUG=1 names the formulas the skeleton alone accepts.
  if bySkeleton && (← (IO.getEnv "IMPRIMATUR_VALIDATE_DEBUG" : IO _)) == some "1" then
    IO.eprintln s!"validate: by skeleton: {← ppExpr orig}\n  denoted {← ppExpr (← instantiateMVars d.term)}"
  return bySkeleton

end Denote

end Imprimatur
