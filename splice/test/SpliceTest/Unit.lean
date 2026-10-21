/-
Copyright (c) 2026 The imprimatur authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Splice
import Testkit
import SpliceTest.Golden

/-!
# Unit tests of the splicer
-/

open Testkit Splice

namespace SpliceTest.Unit

/-- Whether `needle` occurs in `haystack`. -/
def contains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- Whether an `Except` succeeded. -/
def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- The TOML subset parser. -/
def testToml : TestM Unit := group "toml" do
  let doc := "# comment\nschema = 1\nmain = \"p.tex\" # trailing\n\
    lit = 'C:\\path'\nesc = \"a\\tb\\u00e9\"\nneg = -3\nflag = true\n\
    arr = [\n  \"x\", # c\n  \"y\",\n]\n\
    [aliases]\nleanlemma = { view = \"math\", slots = { macros = [\"\\\\entry\"], arg = 2 } }\n\
    [profile.camera-ready]\nsource_links = \"url\"\n\"quoted key\" = 1\na.b = 2\n"
  match parseToml doc with
  | .error e => fail "splice/toml/parses" e
  | .ok t =>
    pass
    checkEq "splice/toml/int" (t.find? "schema") (some (.int 1))
    checkEq "splice/toml/string" (t.find? "main") (some (.str "p.tex"))
    checkEq "splice/toml/literal-string" (t.find? "lit") (some (.str "C:\\path"))
    checkEq "splice/toml/escapes" (t.find? "esc") (some (.str "a\tbé"))
    checkEq "splice/toml/negative" (t.find? "neg") (some (.int (-3)))
    checkEq "splice/toml/bool" (t.find? "flag") (some (.bool true))
    checkEq "splice/toml/multiline-array" (t.find? "arr") (some (.arr #[.str "x", .str "y"]))
    let alias := (t.find? "aliases").bind (·.find? "leanlemma")
    checkEq "splice/toml/inline-table" ((alias.bind (·.find? "slots")).bind (·.find? "macros"))
      (some (.arr #[.str "\\entry"]))
    let prof := (t.find? "profile").bind (·.find? "camera-ready")
    checkEq "splice/toml/dotted-table" (prof.bind (·.find? "source_links")) (some (.str "url"))
    checkEq "splice/toml/quoted-key" (prof.bind (·.find? "quoted key")) (some (.int 1))
    checkEq "splice/toml/dotted-key" ((prof.bind (·.find? "a")).bind (·.find? "b")) (some (.int 2))
  checkError "splice/toml/duplicate-key" (parseToml "a = 1\na = 2\n") "defined twice"
  checkError "splice/toml/unterminated" (parseToml "a = \"x\n") "line 1"
  checkError "splice/toml/array-of-tables" (parseToml "[[x]]\n") "not supported"
  checkError "splice/toml/float" (parseToml "a = 1.5\n") "not supported"
  checkError "splice/toml/junk-after-value" (parseToml "a = 1 2\n") "after value"
  checkError "splice/toml/error-line" (parseToml "a = 1\n\nb = \n") "line 3"

/-- Reading `imprimatur.toml`. -/
def testConfig : TestM Unit := group "config" do
  let ok := "schema = 1\nmain = \"paper.tex\"\nlean_project = \"lean\"\n\
    default_profile = \"submission\"\n\
    [profile.submission]\nsource_links = \"relative\"\n\
    [aliases]\nleangrammar = { view = \"grammar\", slots = { macros = [\"\\\\entry\"], arg = 2, id = \"arg1\" } }\n\
    [trust]\nallowed_axioms = [\"propext\"]\n"
  match Config.parse ok with
  | .error e => fail "splice/config/parses" e
  | .ok c =>
    pass
    checkEq "splice/config/main" c.main "paper.tex"
    checkEq "splice/config/default-profile" c.defaultProfile "submission"
    checkEq "splice/config/alias-slots" ((c.alias? "leangrammar").bind (·.slots))
      (some { macros := #["\\entry"], arg := 2, idArg := 1 })
    check "splice/config/leanblock-builtin" (c.alias? "leanblock").isSome
    checkEq "splice/config/allowed-axioms" c.allowedAxioms #["propext"]
  checkError "splice/config/unknown-key" (Config.parse "schema = 1\nmain = \"a\"\nmian = 1\n")
    "unknown key 'mian'"
  checkError "splice/config/missing-schema" (Config.parse "main = \"a\"\n") "schema = 1"
  checkError "splice/config/alias-needs-view"
    (Config.parse "schema = 1\nmain = \"a\"\n[aliases]\nx = { wrap = \"y\" }\n") "needs a view"
  checkError "splice/config/slot-macro-backslash"
    (Config.parse "schema = 1\nmain = \"a\"\n[aliases]\nx = { view = \"v\", slots = { macros = [\"entry\"] } }\n")
    "backslash"
  checkError "splice/config/url-needs-template"
    (Config.parse "schema = 1\nmain = \"a\"\n[profile.p]\nsource_links = \"url\"\n") "url_template"
  checkError "splice/config/unknown-profile"
    (Config.parse "schema = 1\nmain = \"a\"\ndefault_profile = \"p\"\n") "not a profile"

/-- Reading bundles. -/
def testBundle : TestM Unit := group "bundle" do
  let b := "{\"schema\": \"imprimatur-bundle/1\", \"producer\": {}, \"entries\": {\
    \"B\": {\"kind\": \"theorem\", \"decl\": \"B\", \"views\": {\"lean\": \"b\"}, \"sorry\": true},\
    \"A\": {\"kind\": \"theorem\", \"decl\": \"A\", \"views\": {\"lean\": \"a\"},\
      \"source\": {\"path\": \"A.lean\", \"line\": 3}, \"axioms\": [\"propext\"],\
      \"cone\": {\"size\": 2, \"untrusted\": [\"X\"]}, \"errors\": {\"math\": \"why\"}, \"future\": 1}}}"
  match Bundle.parse b with
  | .error e => fail "splice/bundle/parses" e
  | .ok bundle =>
    pass
    checkEq "splice/bundle/sorted" (bundle.entries.map (·.key)) #["A", "B"]
    let a := bundle.find? "A"
    checkEq "splice/bundle/view" (a.bind (·.view? "lean")) (some "a")
    checkEq "splice/bundle/error" (a.bind (·.error? "math")) (some "why")
    checkEq "splice/bundle/source" (a.bind (·.source)) (some { path := "A.lean", line := 3 })
    checkEq "splice/bundle/cone" (a.map (·.untrusted)) (some #["X"])
    checkEq "splice/bundle/sorry" ((bundle.find? "B").map (·.usesSorry)) (some true)
  checkError "splice/bundle/schema-version"
    (Bundle.parse "{\"schema\": \"imprimatur-bundle/9\", \"producer\": {}, \"entries\": {}}") "not one"
  checkError "splice/bundle/absolute-path"
    (Bundle.parse "{\"schema\": \"imprimatur-bundle/1\", \"producer\": {}, \"entries\": {\"A\": \
      {\"kind\": \"theorem\", \"decl\": \"A\", \"views\": {}, \"source\": {\"path\": \"C:/x.lean\", \"line\": 1}}}}")
    "must be relative"
  checkError "splice/bundle/missing-views"
    (Bundle.parse "{\"schema\": \"imprimatur-bundle/1\", \"producer\": {}, \"entries\": {\"A\": \
      {\"kind\": \"theorem\", \"decl\": \"A\"}}}") "views"
  checkError "splice/bundle/not-json" (Bundle.parse "{") "not valid JSON"

/-- SHA-256 against published test vectors, and normalisation. -/
def testHash : TestM Unit := group "checksums" do
  checkEq "splice/sha256/empty" (Sha256.hexOf "")
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  checkEq "splice/sha256/abc" (Sha256.hexOf "abc")
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  checkEq "splice/sha256/two-blocks"
    (Sha256.hexOf "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
  checkEq "splice/sha256/base64url" (Sha256.base64url (Sha256.hash "abc".toUTF8))
    "ungWv48Bz-pBQUDeXa4iI7ADYaOWF3qctBD_YfIAFa0"
  checkEq "splice/normalize/crlf-and-trailing" (normalize "\n a  \r\nb\t\r\n\n") " a\nb"
  checkEq "splice/checksum/length" (checksum none "x").length 10
  checkEq "splice/checksum/ignores-slot-text"
    (checksum none "a \\leanslot{s}{one} b") (checksum none "a \\leanslot{s}{two} b")
  check "splice/checksum/sees-slot-id"
    (checksum none "a \\leanslot{s}{one} b" != checksum none "a \\leanslot{t}{one} b")

private def cfgWith (aliases : Array Alias) : Config :=
  { main := "m.tex", aliases := #[{ name := "leanblock", view := "lean" }] ++ aliases }

private def scanItems (cfg : Config) (t : String) : Array Item :=
  match scanText cfg "m.tex" t with
  | .ok r => r.items
  | .error _ => #[]

/-- The scanner. -/
def testScan : TestM Unit := group "scan" do
  let cfg := cfgWith #[{ name := "leanlemma", view := "math" }]
  let t := "x \\begin{leanblock}[view=math, wrap={a,b}]{K.a}{T}%\nbody\n  \\end{leanblock}\n\
    \\leaninline{K.b}{c} \\leanref[x]{K.c}{} \\leancheck{K.d , K.e} \\leanindex\n\
    \\begin{leanlemma}{K.f}{T}\\end{leanlemma}"
  let s := Src.ofString "m.tex" t
  match scanSrc cfg s with
  | .error d => fail "splice/scan/forms" d.render
  | .ok r =>
    checkEq "splice/scan/forms" (r.items.map (·.kind))
      #[.block, .inline, .ref, .check, .index, .block]
    let b := r.items[0]!
    checkEq "splice/scan/key" b.key "K.a"
    checkEq "splice/scan/options" (b.opts.map (fun o => (o.key, o.value)))
      #[("view", "math"), ("wrap", "a,b")]
    checkEq "splice/scan/region-after-comment-line" (s.slice b.regionStart b.regionEnd) "body\n"
    checkEq "splice/scan/check-keys" r.items[3]!.keys #["K.d", "K.e"]
    let one := r.items[5]!
    checkEq "splice/scan/one-line-block" (one.regionStart, one.regionEnd) (one.headerEnd, one.headerEnd)
  checkEq "splice/scan/comment-skipped" (scanItems cfg "% \\leaninline{A}{b}\n").size 0
  checkEq "splice/scan/escaped-percent" (scanItems cfg "50\\% \\leaninline{A}{b}\n").size 1
  checkEq "splice/scan/verb-skipped" (scanItems cfg "\\verb|\\leaninline{A}{b}| \\verb*+x+").size 0
  checkEq "splice/scan/verbatim-skipped"
    (scanItems cfg "\\begin{verbatim}\n\\begin{leanblock}{A}{b}\n\\end{verbatim}\n").size 0
  checkEq "splice/scan/definition-not-a-use" (scanItems cfg "\\newcommand{\\leaninline}[2]{#2}").size 0
  checkEq "splice/scan/inputs"
    ((scanText cfg "m" "\\input{a} \\include{b/c} \\subfile{d.tex} \\input x").map
      (·.inputs.map (·.2.1))).toOption (some #["a", "b/c", "d.tex"])
  let err (t : String) : String := match scanText cfg "m.tex" t with
    | .ok _ => "no error"
    | .error d => d.render
  check "splice/scan/unclosed-block" (contains (err "\n\\begin{leanblock}{A}{b}\nx\n") "m.tex:2:1:")
  check "splice/scan/nested-block"
    (contains (err "\\begin{leanblock}{A}{b}\n\\begin{leanblock}{C}{d}\n") "cannot nest")
  check "splice/scan/unclosed-brace" (contains (err "\\leaninline{A}{b") "never closed")
  check "splice/scan/missing-title" (contains (err "\\begin{leanblock}{A}\n\\end{leanblock}") "a key and a title")

/-- Slots. -/
def testSlots : TestM Unit := group "slots" do
  let spec : SlotSpec := { macros := #["\\entry"], arg := 2, idArg := 1 }
  let t := "\\entry{x}{var}\\\\ \\entry{y}{\\leanslot{Y}{why}} \\leanslot{Z}{zed} \\entry{x}{again}"
  let ss := findSlots spec t
  checkEq "splice/slots/found" (ss.map (fun s => (s.id, s.occ, s.isMacro, s.text t)))
    #[("x", 0, false, "var"), ("Y", 0, true, "why"), ("Z", 0, true, "zed"), ("x", 1, false, "again")]
  checkEq "splice/slots/outer" (ss.map (·.outer)) #[none, some "y", none, none]
  checkEq "splice/slots/no-spec" ((findSlots none t).map (·.id)) #["Y", "Z"]
  checkEq "splice/slots/unwrap" (unwrapSlots "a \\leanslot{i}{b {c}} d") "a b {c} d"
  let (merged, orphans) := mergeSlots {} none "\\leanslot{a}{mine} \\leanslot{gone}{text}"
    "\\leanslot{a}{default} \\leanslot{new}{fresh}"
  checkEq "splice/slots/merge" merged "\\leanslot{a}{mine} \\leanslot{new}{fresh}"
  checkEq "splice/slots/orphans" (orphans.map (·.id)) #["gone"]
  -- Undefined macros (DESIGN §10.3): what a file defines, and what it loads.
  checkEq "splice/macros/defined"
    (definedMacros "\\newcommand{\\a}{1} \\newcommand*\\b{2} \\def\\c#1{3} \\let\\d\\relax \\DeclareMathOperator{\\e}{e} \\use\\f")
    #["\\a", "\\b", "\\c", "\\d", "\\e"]
  checkEq "splice/macros/loaded"
    (loadedFiles "\\usepackage[opt]{a,b} \\RequirePackage{c} \\input{d.tex} \\include{e}")
    #["d.tex", "e", "a", "b", "c"]
  let (renamed, _) := mergeSlots { renames := #[("gone", "new")] } none
    "\\leanslot{gone}{text}" "\\leanslot{new}{fresh}"
  checkEq "splice/slots/rename" renamed "\\leanslot{new}{text}"

/-- Small helpers: paths, diffs, escaping. -/
def testHelpers : TestM Unit := group "helpers" do
  checkEq "splice/paths/normalize" (normPath "./a//b/../c/./d.tex") "a/c/d.tex"
  checkEq "splice/paths/input-candidates" (inputCandidates "paper" "input" "../x/y")
    ["x/y.tex", "x/y"]
  checkEq "splice/paths/include-adds-tex" (inputCandidates "" "include" "ch1") ["ch1.tex"]
  checkEq "splice/diff/lines" (lineDiff "a\nb\nc\n" "a\nB\nc\nd\n")
    #[" a", "-b", "+B", " c", "+d"]
  checkEq "splice/tex-escape" (texEscape "a_b#c%d&e{f}") "a\\_b\\#c\\%d\\&e\\{f\\}"
  checkEq "splice/eol/dominant" (dominantEol "a\r\nb\r\nc\n".toList.toArray) "\r\n"

/-- The golden runner's word splitting. -/
def testWords : TestM Unit := group "golden-runner" do
  checkEq "splice/golden-runner/words"
    (SpliceTest.Golden.splitWords "!replace f.tex \"a \\b\" \"say \\\"hi\\\"\"")
    ["!replace", "f.tex", "a \\b", "say \"hi\""]

/-- All unit tests. -/
def tests : TestM Unit := do
  testToml
  testConfig
  testBundle
  testHash
  testScan
  testSlots
  testHelpers
  testWords

end SpliceTest.Unit
