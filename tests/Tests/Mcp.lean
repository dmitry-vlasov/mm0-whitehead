/-
Tests of the MCP front-end: the JSON module (`Whitehead/Json.lean`), with escapes,
surrogate pairs and malformed texts; the printer of statements in the notation
(`Prove/Show.lean`), by printing every statement of a specification and reading it back,
on the logic fixture and on every pair of the built corpus; and the server
(`Mcp/Server.lean`, `Mcp/Tools.lean`), by a conversation with it on the logic fixture,
the errors of the protocol and of the tools included.
-/
import Whitehead.Mcp.Server
import Tests.Prove.Filter

open Whitehead Whitehead.Mmb Whitehead.Prove Whitehead.Mcp

namespace Tests.Mcp

def jsonTests : TestM Unit := do
  let round (text : String) : String :=
    match Json.parse text with
    | .ok j => j.compress
    | .error e => s!"error {e.pos}: {e.msg}"
  checkEq "json: values" (round " { \"a\" : [1, -2, 3.5e1, true, false, null], \"b\": {} , \"c\": [] } ")
    "{\"a\":[1,-2,3.5e1,true,false,null],\"b\":{},\"c\":[]}"
  checkEq "json: escapes" (round "\"q\\\" b\\\\ s\\/ n\\n t\\t u\\u0041 c\\u0001\"")
    "\"q\\\" b\\\\ s/ n\\n t\\t uA c\\u0001\""
  checkEq "json: a surrogate pair is one character" (round "\"\\ud83d\\ude00\"") "\"😀\""
  checkEq "json: text that is not ASCII" (round "\"→ ⊢\"") "\"→ ⊢\""
  checkEq "json: a big integer" (round "123456789012345678901234567890") "123456789012345678901234567890"
  checkEq "json: an unclosed string" (round "\"abc") "error 4: this string is not closed"
  checkEq "json: a trailing comma" (round "[1,]") "error 3: unexpected `]`"
  checkEq "json: a missing colon" (round "{\"a\" 1}") "error 5: expected `:`"
  checkEq "json: an unknown escape" (round "\"\\q\"") "error 3: unknown escape `\\q`"
  checkEq "json: a lone low surrogate" (round "\"\\udc00\"") "error 7: a low surrogate without its high one"
  checkEq "json: text after the value" (round "1 2") "error 2: expected the end of the text"
  checkEq "json: a control character" (round "\"a\nb\"") "error 3: a control character in a string must be escaped"
  checkEq "json: access" ((Json.parse "{\"n\": 3, \"s\": \"x\"}").toOption.bind (·.get? "n") |>.bind (·.nat?)) (some 3)

/-- Every statement of the specification, printed with its binders' names and read back:
the same expression as in the theorem's task. Returns the statements compared and the
first that differs. -/
def roundTrip (c : Ctx) : Nat × Option String := Id.run do
  let mut n := 0
  for t in [0:c.spec.thms.size] do
    let id := c.spec.thms[t]!
    let decl := c.spec.st.env.thms[t]!
    -- a binder without a name cannot be named back
    if decl.args.any (·.name.isNone) then continue
    let names := c.spec.binderNames id
    let pr := c.spec.printer c.db names
    let task := c.db.task id
    let vars (i : Nat) : Exp := c.db.binderImage id #[] (c.db.asserts[id]!.vars[i]?.getD 0)
    for (e, expected) in (c.db.asserts[id]!.hyps.zip task.premises).push (c.db.asserts[id]!.concl, task.goal) do
      let text := pr.render e fun v => names[v]?.getD s!"?{v}"
      n := n + 1
      match c.spec.formula id vars text 0 freshBase with
      | .ok (back, 0) => if back != expected then return (n, some s!"{decl.name}: {text}")
      | .ok _ => return (n, some s!"{decl.name}: {text} has a hole")
      | .error e => return (n, some s!"{decl.name}: {text}: {e.msg}")
  return (n, none)

def printerTests : TestM Unit := do
  match ← Ctx.load Prove.logicSpecPath Prove.logicPath with
  | .error msg => check "printer: the logic fixture is loaded" false msg
  | .ok c =>
    let id := Prove.thmId c.db
    checkEq "printer: right associative, no parentheses" (c.assertionText (id "ax_1")) "$ ph -> ps -> ph $"
    checkEq "printer: parentheses where the left operand is an implication"
      (c.assertionText (id "ax_2")) "$ (ph -> ps -> ch) -> (ph -> ps) -> ph -> ch $"
    checkEq "printer: a prefix binds tighter" (c.assertionText (id "ax_3")) "$ (~ ph -> ~ ps) -> ps -> ph $"
    checkEq "printer: hypotheses" (c.assertionText (id "ax_mp")) "$ ph $ > $ ph -> ps $ > $ ps $"
    checkEq "printer: a quantifier" (c.assertionText (id "ax_4")) "$ A. x (ph -> ps) -> A. x ph -> A. x ps $"
    let (n, bad) := roundTrip c
    -- 24 assertions, with 14 hypotheses between them
    check "printer: every statement of logic.mm0 reads back the same" (bad.isNone && n == 38) s!"{n}: {bad}"
  -- the pairs of the built corpus
  let corpus : System.FilePath := ".tools/corpus"
  if !(← corpus.isDir) then
    skip "printer: the pairs of .tools/corpus" "run scripts/build-corpus.sh"
    return
  let mut total := 0
  for e in ← corpus.readDir do
    if e.path.extension != some "mmb" then continue
    let mm0 := e.path.withExtension "mm0"
    if !(← mm0.pathExists) then continue
    match ← Ctx.load mm0 e.path with
    | .error _ => pure ()  -- a pair that does not verify (a `sorry`) is the verifier's test
    | .ok c =>
      let (n, bad) := roundTrip c
      total := total + n
      check s!"printer: every statement of {mm0.fileName.getD ""} reads back the same" bad.isNone s!"{bad}"
  check "printer: the corpus has statements" (total > 50000) s!"{total}"
  IO.println s!"printer: {total} statements of the corpus printed and read back"

/-- A request to the server, and the text of its answer. -/
def ask (c : Ctx) (st : IO.Ref State) (id : Nat) (method : String) (params : Json) : IO Json := do
  let msg := Json.obj #[("jsonrpc", "2.0"), ("id", Json.ofNat id), ("method", Json.str method), ("params", params)]
  return (← handle c st msg).getD .null

/-- The result of a tool, read back from its text, and whether it is an error. -/
def callTool (c : Ctx) (st : IO.Ref State) (id : Nat) (name : String) (args : Json) : IO (Json × Bool) := do
  let r ← ask c st id "tools/call" (.obj #[("name", Json.str name), ("arguments", args)])
  let some result := r.get? "result" | return (r, true)
  let isError := ((result.get? "isError").bind (·.bool?)).getD false
  let text := ((result.get? "content").bind (·.arr?) |>.bind (·[0]?) |>.bind (·.get? "text") |>.bind (·.str?)).getD ""
  if isError then return (Json.str text, true)
  return ((Json.parse text).toOption.getD .null, false)

def serverTests : TestM Unit := do
  let some c := (← Ctx.load Prove.logicSpecPath Prove.logicPath).toOption
    | check "server: the logic fixture is loaded" false; return
  let st ← IO.mkRef ({} : State)
  let init ← ask c st 1 "initialize" (.obj #[("protocolVersion", "2025-06-18"), ("capabilities", .obj #[])])
  checkEq "server: initialize" (((init.get? "result").bind (·.get? "protocolVersion")).bind (·.str?)) (some "2025-06-18")
  let old ← ask c st 2 "initialize" (.obj #[("protocolVersion", "1999-01-01")])
  checkEq "server: an unknown version gets the latest"
    (((old.get? "result").bind (·.get? "protocolVersion")).bind (·.str?)) (some protocolVersions[0]!)
  checkEq "server: a notification has no answer"
    ((← handle c st (.obj #[("jsonrpc", "2.0"), ("method", "notifications/initialized")])).isSome) false
  let list ← ask c st 3 "tools/list" (.obj #[])
  checkEq "server: the tools" ((((list.get? "result").bind (·.get? "tools")).bind (·.arr?)).map (·.size)) (some tools.size)
  let unknown ← ask c st 4 "resources/list" (.obj #[])
  checkEq "server: an unknown method" (((unknown.get? "error").bind (·.get? "code")).map (·.compress)) (some "-32601")
  -- a conversation: mpd from an intermediate goal, by choices
  let (found, _) ← callTool c st 5 "find" (.obj #[("name", "a2*")])
  checkEq "server: find" ((found.get? "count").bind (·.nat?)) (some 2)
  let (started, err) ← callTool c st 6 "start" (.obj #[("theorem", "mpd")])
  check "server: start" (!err && (started.get? "session").bind (·.nat?) == some 0 &&
    ((started.get? "goal").bind (·.get? "statement")).bind (·.str?) == some "ph -> ch") started.compress
  let (vs, _) ← callTool c st 7 "variants" (.obj #[("session", Json.ofNat 0), ("node", Json.ofNat 0),
    ("filter", "name(ax_mp)")])
  let mp := ((vs.get? "sample").bind (·.arr?) |>.bind (·[0]?) |>.bind (·.get? "variant") |>.bind (·.nat?)).getD 0
  checkEq "server: the new goals of a variant, the rule's own variables named"
    ((vs.get? "sample").bind (·.arr?) |>.bind (·[0]?) |>.bind (·.get? "new_goals") |>.map (·.compress))
    (some "[\"?ph\",\"?ph -> ph -> ch\"]")
  let (chosen, err) ← callTool c st 8 "choose" (.obj #[("session", Json.ofNat 0), ("node", Json.ofNat 0),
    ("variants", .arr #[Json.ofNat mp])])
  check "server: choose" (!err && ((chosen.get? "proved").bind (·.bool?)) == some false) chosen.compress
  -- the minor premise ?0 is proved for instances: the premises
  let newGoals := (chosen.get? "chosen").bind (·.arr?) |>.bind (·[0]?) |>.bind (·.get? "new_goals") |>.bind (·.arr?)
  let minor := (newGoals.bind (·[0]?)).getD .null
  let major := ((newGoals.bind (·[1]?)).bind (·.get? "node") |>.bind (·.nat?)).getD 0
  check "server: a goal with a variable shows the instances it is proved for"
    (((minor.get? "proofs").bind (·.nat?)).any (· ≥ 1) &&
      ((minor.get? "proved_as").map (·.compress)).any (contains · "ph -> ps")) minor.compress
  -- a closer shows what it puts for the variable: ax_1 at ?0 -> ph -> ch proves ch -> ph -> ch
  let (vs, _) ← callTool c st 81 "variants" (.obj #[("session", Json.ofNat 0), ("node", Json.ofNat major),
    ("filter", "name(ax_1)")])
  checkEq "server: what a closing step proves"
    ((vs.get? "sample").bind (·.arr?) |>.bind (·[0]?) |>.bind (·.get? "proves") |>.bind (·.str?)) (some "ch -> ph -> ch")
  let (vs, _) ← callTool c st 82 "variants" (.obj #[("session", Json.ofNat 0), ("node", Json.ofNat major),
    ("filter", "name(ax_1)"), ("compact", .bool true)])
  check "server: a compact line per variant"
    (((vs.get? "sample").bind (·.arr?) |>.bind (·[0]?) |>.bind (·.str?)).any fun line =>
      contains line "ax_1" && contains line "closes => ch -> ph -> ch") vs.compress
  let (g, err) ← callTool c st 9 "goal" (.obj #[("session", Json.ofNat 0), ("statement", "(ph -> ps) -> ph -> ch")])
  let h := ((g.get? "goal").bind (·.get? "node") |>.bind (·.nat?)).getD 0
  check "server: an intermediate goal" (!err && h > 0) g.compress
  let (vs, _) ← callTool c st 10 "variants" (.obj #[("session", Json.ofNat 0), ("node", Json.ofNat h),
    ("filter", "name(a2i)")])
  let a2i := ((vs.get? "sample").bind (·.arr?) |>.bind (·[0]?) |>.bind (·.get? "variant") |>.bind (·.nat?)).getD 0
  let (chosen, _) ← callTool c st 11 "choose" (.obj #[("session", Json.ofNat 0), ("node", Json.ofNat h),
    ("variants", .arr #[Json.ofNat a2i])])
  checkEq "server: proved" ((chosen.get? "proved").bind (·.bool?)) (some true)
  let (pf, _) ← callTool c st 12 "proof" (.obj #[("session", Json.ofNat 0)])
  checkEq "server: the proof, by steps" ((pf.get? "steps").map (·.compress))
    (some "[\"1: hypothesis 0 |- ph -> ps\",\"2: hypothesis 1 |- ph -> ps -> ch\",\"3: a2i 2 |- (ph -> ps) -> ph -> ch\",\"4: ax_mp 1, 3 |- ph -> ch\"]")
  checkEq "server: verified" ((pf.get? "verified").bind (·.bool?)) (some true)
  -- a run, in a second session
  let _ ← callTool c st 13 "start" (.obj #[("theorem", "syl")])
  let (ran, _) ← callTool c st 14 "run" (.obj #[("session", Json.ofNat 1), ("tactic", "limited(bfs, depth=3)"),
    ("nodes", Json.ofNat 100000)])
  checkEq "server: run" ((ran.get? "ending").bind (·.str?)) (some "proved")
  check "server: run says what it closed" (((ran.get? "closed_count").bind (·.nat?)).any (· ≥ 1) &&
    ((ran.get? "open_before").bind (·.nat?)).isSome) ran.compress
  let _ ← callTool c st 141 "start" (.obj #[("theorem", "syl")])
  let (ran, err) ← callTool c st 142 "run" (.obj #[("session", Json.ofNat 2), ("tactic", "limited(bfs, depth=3)"),
    ("node", Json.ofNat 0), ("nodes", Json.ofNat 100000)])
  check "server: run in the subtree of a node" (!err && (ran.get? "ending").bind (·.str?) == some "proved") ran.compress
  checkEq "server: run at a node that is not one"
    (← callTool c st 143 "run" (.obj #[("session", Json.ofNat 2), ("tactic", "bfs"), ("node", Json.ofNat 100000)])).2 true
  -- the errors of the tools are results for the agent
  let errText (r : Json × Bool) : String := if r.2 then (r.1.str?).getD "" else "not an error"
  checkEq "server: no such session" (errText (← callTool c st 15 "goals" (.obj #[("session", Json.ofNat 9)])))
    "there is no session 9"
  checkEq "server: a missing argument" (errText (← callTool c st 16 "variants" (.obj #[("session", Json.ofNat 0)])))
    "`node` is missing"
  check "server: a filter with an error shows where"
    (contains (errText (← callTool c st 17 "variants" (.obj #[("session", Json.ofNat 0), ("node", Json.ofNat 0),
      ("filter", "nmae(x)")]))) "unknown filter `nmae`")
  checkEq "server: an axiom is not a theorem" (errText (← callTool c st 18 "start" (.obj #[("theorem", "ax_1")])))
    "`ax_1` is an axiom: there is nothing to prove"
  checkEq "server: no such tool" (errText (← callTool c st 19 "prove" (.obj #[]))) "there is no tool `prove`"
  checkEq "server: an argument the tool does not take"
    (errText (← callTool c st 191 "find" (.obj #[("pattern", "a*")]))) "`find` has no argument `pattern`; it takes `name`, `limit`"
  -- after an error the sessions are still there
  let (gs, err) ← callTool c st 20 "goals" (.obj #[("session", Json.ofNat 0)])
  check "server: the session after the errors" (!err && (gs.get? "proved").bind (·.bool?) == some true) gs.compress
  let (_, err) ← callTool c st 21 "close" (.obj #[("session", Json.ofNat 0)])
  check "server: close" (!err && (← callTool c st 22 "goals" (.obj #[("session", Json.ofNat 0)])).2)
  -- anonymous: the assertions are A and their number, but for `start`
  let some a := (← Ctx.load Prove.logicSpecPath Prove.logicPath (anonymous := true)).toOption
    | check "server: the anonymous fixture is loaded" false; return
  let st ← IO.mkRef ({} : State)
  let (found, _) ← callTool a st 1 "find" (.obj #[("name", "ax_*")])
  checkEq "server: anonymous, no assertion has its name" ((found.get? "count").bind (·.nat?)) (some 0)
  let (found, _) ← callTool a st 2 "find" (.obj #[("name", "A3")])
  checkEq "server: anonymous, by number" ((found.get? "assertions").map (·.compress))
    (some "[{\"name\":\"A3\",\"kind\":\"axiom\",\"statement\":\"$ ph $ > $ ph -> ps $ > $ ps $\"}]")
  let (_, err) ← callTool a st 3 "start" (.obj #[("theorem", "syl")])
  let (ran, _) ← callTool a st 4 "run" (.obj #[("session", Json.ofNat 0), ("tactic", "limited(bfs, depth=3)")])
  let (pf, _) ← callTool a st 5 "proof" (.obj #[("session", Json.ofNat 0)])
  check "server: anonymous, a session by the theorem's name, and a proof by numbers"
    (!err && (ran.get? "ending").bind (·.str?) == some "proved" &&
      ((pf.get? "steps").map (·.compress)).any fun t => contains t "A6" && !contains t "mpd") pf.compress

end Tests.Mcp
