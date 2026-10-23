/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice.Toml

/-!
# `imprimatur.toml`

Project wiring (DESIGN §6.1). The splicer reads the keys it needs and checks
that every other key is one the extractor reads, so a misspelt key is an
error rather than silently ignored.
-/

namespace Splice

/-- Slots declared by position (DESIGN §9.5): argument `arg` of each macro
in `macros` is a slot, identified by the text of argument `idArg`. -/
structure SlotSpec where
  /-- The macros, with their backslash (`\entry`). -/
  macros : Array String
  /-- The argument that is the slot (1-based). -/
  arg : Nat
  /-- The argument whose text identifies the slot (1-based). -/
  idArg : Nat
  deriving Repr, BEq

/-- An environment that `scan` treats as a `leanblock` (DESIGN §9.2). -/
structure Alias where
  /-- The environment name. -/
  name : String
  /-- The view it requests. -/
  view : String
  /-- The environment `strip` wraps the content in, if any. -/
  wrap : Option String := none
  /-- Slots declared by position. -/
  slots : Option SlotSpec := none
  /-- A label the splicer writes for each block, from a template over `{key}`
  (the key with spaces as `-`): `thm:{key}`. -/
  label : Option String := none
  /-- What a repeated key's label gets: `-appendix`, then `-appendix2`, … -/
  repeatSuffix : Option String := none
  /-- The content written, from a template over `{content}` (the view's
  text), `{label}`, `{key}` and `{title}`. The default is `{content}`, or
  `\label{{label}}` on a line of its own before it when `label` is set. -/
  template : Option String := none
  /-- A region delimited by comments, `%NAME{key}{title}` … `%ENDNAME`,
  rather than an environment. -/
  comment : Bool := false
  deriving Repr, BEq

/-- The label of a block with key `key`: its `occurrence`-th (from 0) with
this alias and key. -/
def Alias.labelFor (a : Alias) (key : String) (occurrence : Nat) : Option String :=
  a.label.map fun t =>
    let base := t.replace "{key}" (key.replace " " "-")
    match occurrence, a.repeatSuffix with
    | 0, _ | _, none => base
    | 1, some suffix => base ++ suffix
    | n, some suffix => base ++ suffix ++ toString n

/-- The content of a block from the view's text. -/
def Alias.fill (a : Alias) (content key title : String) (label : Option String) : String :=
  let t := a.template.getD (if a.label.isSome then "\\label{{label}}\n{content}" else "{content}")
  -- The placeholders are the template's: generated text that contains one
  -- (a field named `key`, say) is not rewritten.
  let part (s : String) := ((s.replace "{label}" (label.getD "")).replace "{key}" key).replace "{title}" title
  content.intercalate ((t.splitOn "{content}").map part)

/-- How `\leanref` and the `meta` view refer to source code (DESIGN §11). -/
inductive SourceLinks where
  /-- A path relative to the Lean project, with a line number. -/
  | relative
  /-- A URL built from a template. -/
  | url (template : String)
  /-- No locations. -/
  | none
  deriving Repr, BEq

/-- The splicer's configuration. -/
structure Config where
  /-- The main `.tex` file, relative to the directory of `imprimatur.toml`. -/
  main : String
  /-- Environments treated as `leanblock`, including `leanblock` itself. -/
  aliases : Array Alias := #[{ name := "leanblock", view := "lean" }]
  /-- Profiles by name. -/
  profiles : Array (String × SourceLinks) :=
    #[("relative", .relative), ("none", .none)]
  /-- The profile used when none is given. -/
  defaultProfile : String := "relative"
  /-- Axioms a result may depend on without being reported (DESIGN §7.7). -/
  allowedAxioms : Array String := #["propext", "Classical.choice", "Quot.sound"]
  /-- Environments whose contents are not scanned. -/
  verbatimEnvs : Array String :=
    #["verbatim", "verbatim*", "Verbatim", "lstlisting", "minted", "comment", "alltt"]
  /-- Whether to read blueprint `\lean{…}` as check-only references. -/
  blueprint : Bool := false
  /-- The Lean project, relative to the configuration's directory. -/
  leanProject : String := "."
  /-- How the extractor runs (DESIGN §6.3). -/
  mode : String := "in-project"
  /-- Modules the extractor imports. -/
  imports : Array String := #[]
  /-- Namespaces whose scoped notation the `lean` view uses. -/
  openScoped : Array String := #[]
  /-- Namespaces left out of rendered names. -/
  stripNamespaces : Array String := #[]
  /-- Module prefixes whose declarations end a dependency cone (DESIGN §7.7). -/
  trustedPrefixes : Array String := #["Mathlib", "Std", "Batteries", "Lean", "Init"]
  /-- Comparator manifests: paths, with `*` allowed in the file name. -/
  comparator : Array String := #[]
  /-- Notation packs (DESIGN §7.5); `none` means the extractor's default. -/
  notationPacks : Option (Array String) := none
  /-- Notation modules, as files, for external mode (DESIGN §6.2, §6.3 A). -/
  notationFiles : Array String := #[]
  /-- The line width of rendered views, if not the extractor's default. -/
  width : Option Nat := none
  /-- Whether the extractor reads rendered formulas back (DESIGN §18.4);
  `none` means its default, which is to. -/
  validate : Option Bool := none
  /-- Macros that packages the paper loads define, so that generated content
  may use them (`known_macros`; DESIGN §10.3), with their backslashes. -/
  knownMacros : Array String := #[]
  deriving Repr

/-- The alias for an environment name, if any. -/
def Config.alias? (c : Config) (env : String) : Option Alias :=
  c.aliases.find? (·.name == env)

/-- The source-link setting of a profile. -/
def Config.profile? (c : Config) (name : String) : Option SourceLinks :=
  (c.profiles.find? (·.1 == name)).map (·.2)

/-- Keys that only the extractor reads. The splicer passes them on in
`requests.json`, or (for later milestones) accepts and ignores them. -/
private def extractorKeys : List String :=
  ["lean_project", "mode", "imports", "notation", "strip_namespaces", "open_scoped",
   "notation_packs", "width", "validate"]

private def expectStr (where_ : String) : Toml → Except String String
  | .str s => .ok s
  | v => .error s!"{where_} must be a string, not {v.typeName}"

private def expectBool (where_ : String) : Toml → Except String Bool
  | .bool b => .ok b
  | v => .error s!"{where_} must be a boolean, not {v.typeName}"

private def expectStrs (where_ : String) : Toml → Except String (Array String)
  | .arr xs => xs.mapM (expectStr s!"each element of {where_}")
  | v => .error s!"{where_} must be an array of strings, not {v.typeName}"

private def expectTable (where_ : String) : Toml → Except String (Array (String × Toml))
  | .tbl kvs => .ok kvs
  | v => .error s!"{where_} must be a table, not {v.typeName}"

private def checkKeys (where_ : String) (kvs : Array (String × Toml)) (known : List String) :
    Except String Unit := do
  for (k, _) in kvs do
    unless known.contains k do
      throw s!"unknown key '{k}' in {where_}; expected one of {", ".intercalate known}"

private def argNumber (where_ : String) : Toml → Except String Nat
  | .int n => if n ≥ 1 then .ok n.toNat else .error s!"{where_} must be at least 1"
  | .str s =>
    match (s.dropPrefix? "arg").bind (fun r => r.toString.toNat?) with
    | some n => if n ≥ 1 then .ok n else .error s!"{where_} must be at least 1"
    | none => .error s!"{where_} must be a number or \"argN\", not {repr s}"
  | v => .error s!"{where_} must be a number or \"argN\", not {v.typeName}"

private def parseSlots (where_ : String) (v : Toml) : Except String SlotSpec := do
  let kvs ← expectTable where_ v
  checkKeys where_ kvs ["macros", "arg", "id"]
  let macros ← expectStrs s!"{where_}.macros" ((v.find? "macros").getD (.arr #[]))
  if macros.isEmpty then throw s!"{where_}.macros must list at least one macro"
  for m in macros do
    unless m.startsWith "\\" do throw s!"{where_}.macros: {repr m} must start with a backslash"
  let arg ← argNumber s!"{where_}.arg" ((v.find? "arg").getD (.int 2))
  let idArg ← argNumber s!"{where_}.id" ((v.find? "id").getD (.int 1))
  if arg == idArg then throw s!"{where_}: the slot and its id must be different arguments"
  return { macros, arg, idArg }

private def parseAlias (name : String) (v : Toml) : Except String Alias := do
  let where_ := s!"[aliases].{name}"
  let kvs ← expectTable where_ v
  checkKeys where_ kvs ["view", "wrap", "slots", "label", "repeat_suffix", "template", "comment"]
  let some view := v.find? "view" | throw s!"{where_} needs a view"
  let view ← expectStr s!"{where_}.view" view
  let wrap ← (v.find? "wrap").mapM (expectStr s!"{where_}.wrap")
  let slots ← (v.find? "slots").mapM (parseSlots s!"{where_}.slots")
  let label ← (v.find? "label").mapM (expectStr s!"{where_}.label")
  let repeatSuffix ← (v.find? "repeat_suffix").mapM (expectStr s!"{where_}.repeat_suffix")
  if repeatSuffix.isSome && label.isNone then throw s!"{where_}: repeat_suffix needs label"
  let template ← (v.find? "template").mapM (expectStr s!"{where_}.template")
  if let some t := template then
    unless (t.splitOn "{content}").length > 1 do throw s!"{where_}.template must contain \{content}"
  let comment ← (v.find? "comment").mapM (expectBool s!"{where_}.comment")
  return { name, view, wrap, slots, label, repeatSuffix, template, comment := comment.getD false }

private def parseProfile (name : String) (v : Toml) : Except String SourceLinks := do
  let where_ := s!"[profile.{name}]"
  let kvs ← expectTable where_ v
  checkKeys where_ kvs ["source_links", "url_template"]
  let links ← expectStr s!"{where_}.source_links" ((v.find? "source_links").getD (.str "relative"))
  match links with
  | "relative" => return .relative
  | "none" => return .none
  | "url" =>
    let some t := v.find? "url_template" | throw s!"{where_}: source_links = \"url\" needs url_template"
    return .url (← expectStr s!"{where_}.url_template" t)
  | other => throw s!"{where_}.source_links must be relative, url or none, not {repr other}"

/-- Read a configuration from the text of `imprimatur.toml`. -/
def Config.parse (text : String) : Except String Config := do
  let root ← parseToml text
  let kvs ← expectTable "the file" root
  checkKeys "the top-level table" kvs (["schema", "main", "default_profile", "profile", "aliases",
    "trust", "manifests", "verbatim_envs", "known_macros"] ++ extractorKeys)
  match root.find? "schema" with
  | some (.int 1) => pure ()
  | some v => throw s!"schema must be 1, not {repr v}"
  | none => throw "schema = 1 is missing"
  let some main := root.find? "main" | throw "main (the main .tex file) is missing"
  let main ← expectStr "main" main
  let mut cfg : Config := { main }
  if let some p := root.find? "profile" then
    for (name, v) in ← expectTable "[profile]" p do
      cfg := { cfg with profiles := (cfg.profiles.filter (·.1 != name)).push (name, ← parseProfile name v) }
  if let some d := root.find? "default_profile" then
    let d ← expectStr "default_profile" d
    if (cfg.profile? d).isNone then throw s!"default_profile {repr d} is not a profile"
    cfg := { cfg with defaultProfile := d }
  if let some a := root.find? "aliases" then
    for (name, v) in ← expectTable "[aliases]" a do
      if name == "leanblock" then throw "[aliases] cannot redefine leanblock"
      cfg := { cfg with aliases := cfg.aliases.push (← parseAlias name v) }
  if let some t := root.find? "trust" then
    let tk ← expectTable "[trust]" t
    checkKeys "[trust]" tk ["allowed_axioms", "trusted_prefixes"]
    if let some ax := t.find? "allowed_axioms" then
      cfg := { cfg with allowedAxioms := ← expectStrs "[trust].allowed_axioms" ax }
    if let some tp := t.find? "trusted_prefixes" then
      cfg := { cfg with trustedPrefixes := ← expectStrs "[trust].trusted_prefixes" tp }
  if let some m := root.find? "manifests" then
    let mk ← expectTable "[manifests]" m
    checkKeys "[manifests]" mk ["comparator", "blueprint"]
    if let some c := m.find? "comparator" then
      cfg := { cfg with comparator := ← expectStrs "[manifests].comparator" c }
    if let some b := m.find? "blueprint" then
      cfg := { cfg with blueprint := ← expectBool "[manifests].blueprint" b }
  if let some v := root.find? "known_macros" then
    let ms ← expectStrs "known_macros" v
    cfg := { cfg with knownMacros := ms.map fun m => if m.startsWith "\\" then m else "\\" ++ m }
  if let some v := root.find? "verbatim_envs" then
    cfg := { cfg with verbatimEnvs := cfg.verbatimEnvs ++ (← expectStrs "verbatim_envs" v) }
  for k in extractorKeys do
    if let some v := root.find? k then
      match k with
      | "width" =>
        match v with
        | .int n => if n ≥ 20 then cfg := { cfg with width := some n.toNat } else throw "width must be at least 20"
        | _ => throw s!"width must be a number, not {v.typeName}"
      | "validate" => cfg := { cfg with validate := some (← expectBool k v) }
      | "lean_project" => cfg := { cfg with leanProject := ← expectStr k v }
      | "mode" =>
        let m ← expectStr k v
        unless ["in-project", "sidecar", "external"].contains m do
          throw s!"mode must be in-project, sidecar or external, not {repr m}"
        cfg := { cfg with mode := m }
      | "imports" => cfg := { cfg with imports := ← expectStrs k v }
      | "open_scoped" => cfg := { cfg with openScoped := ← expectStrs k v }
      | "strip_namespaces" => cfg := { cfg with stripNamespaces := ← expectStrs k v }
      | "notation_packs" =>
        let ps ← expectStrs k v
        for p in ps do
          unless ["core", "logic", "sets", "order"].contains p do
            throw s!"notation_packs: unknown pack {repr p}; the packs are core, logic, sets and order"
        cfg := { cfg with notationPacks := some ps }
      | "notation" => cfg := { cfg with notationFiles := ← expectStrs k v }
      | _ => discard <| expectStrs k v
  return cfg

end Splice
