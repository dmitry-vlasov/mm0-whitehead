/-
The tools of the MCP front-end (`docs/DESIGN.md`, "Phase 4", "The session",
"Front-ends"): the session operations, for an agent, over one proof file and its
specification.

Statements are read and printed in the notation of the specification. An agent sees goal
nodes, their variants and the facts, by number, and chooses among them. It never gives a
substitution: the engine unifies. A variable that the engine made is printed `?` and a
number. A variable of a variant's rule that its unifier leaves free is printed `?` and
the name of the rule's binder.

Every result says what it cost: the time it took, and the size of the tree. A sample is
drawn from a seed, and a run limited by nodes rather than time is deterministic, so a
session can be replayed.
-/
import Whitehead.Json
import Whitehead.Prove.Show
import Whitehead.Prove.Session
import Whitehead.Mm0.Load

namespace Whitehead.Mcp

open Whitehead.Prove Whitehead.Mmb

/-- A proof file and its specification, loaded once. -/
structure Ctx where
  db : Db
  index : Index Nat
  hypIndexes : HypIndexes
  vc : Verify.Ctx
  spec : Notation
  /-- How often each assertion is used in the proofs of the file (`Uses.lean`). -/
  uses : Uses

/-- A session, with how to print its statements. -/
structure Open where
  session : Session
  thm : Nat
  printer : Printer

structure State where
  sessions : Array (Option Open) := #[]
  deriving Inhabited

/-- Loads `mm0` and `mmb`, checks that the proof file proves the specification, and names
the assertions by the specification. -/
def Ctx.load (mm0 mmb : System.FilePath) : IO (Except String Ctx) := do
  let spec ← match ← Mm0.load mm0 with
    | .error e => return .error e.format
    | .ok spec => pure spec
  let st ← match Mm0.elaborateState spec with
    | .error e => return .error e.format
    | .ok st => pure st
  let file ← match MmbFile.parse (← IO.FS.readBinFile mmb) with
    | .error e => return .error (e.format mmb.toString)
    | .ok f => pure f
  if let .error e := Verify.matchSpec st.env file then
    return .error s!"{mmb} does not prove {mm0}: {e.msg}"
  let db ← match Db.ofFile file with
    | .error msg => return .error msg
    | .ok db => pure db
  let nt := Notation.ofSpec st file
  let db := nt.names.foldl (init := db) fun db (i, name) =>
    if i < db.asserts.size then { db with asserts := db.asserts.modify i fun a => { a with name } } else db
  return .ok { db, index := db.index, hypIndexes := db.hypIndexes, vc := Verify.Ctx.ofFile file, spec := nt,
               uses := Uses.ofFile file db.asserts.size }

/-! ### Arguments -/

def argStr (args : Json) (key : String) : Except String String :=
  match args.get? key with
  | some (.str s) => .ok s
  | some _ => .error s!"`{key}` is a string"
  | none => .error s!"`{key}` is missing"

def argStrD (args : Json) (key dflt : String) : Except String String :=
  match args.get? key with
  | some (.str s) => .ok s
  | some _ => .error s!"`{key}` is a string"
  | none => .ok dflt

def argNat (args : Json) (key : String) : Except String Nat :=
  match args.get? key with
  | some j => match j.nat? with
    | some n => .ok n
    | none => .error s!"`{key}` is a number of 0 or more"
  | none => .error s!"`{key}` is missing"

def argNatD (args : Json) (key : String) (dflt : Nat) : Except String Nat :=
  if (args.get? key).isNone then .ok dflt else argNat args key

def argBoolD (args : Json) (key : String) (dflt : Bool) : Except String Bool :=
  match args.get? key with
  | some (.bool b) => .ok b
  | some _ => .error s!"`{key}` is true or false"
  | none => .ok dflt

def argNats (args : Json) (key : String) : Except String (Array Nat) :=
  match args.get? key with
  | some (.arr xs) => xs.mapM fun x => match x.nat? with
    | some n => .ok n
    | none => .error s!"`{key}` is a list of numbers"
  | some _ => .error s!"`{key}` is a list of numbers"
  | none => .error s!"`{key}` is missing"

/-! ### Printing -/

/-- A variable of the tree, as printed: one the engine made is `?` and a number. -/
def freshName (v : Nat) : String :=
  if v ≥ freshBase then s!"?{v - freshBase}" else s!"?v{v}"

/-- An assertion's statement, with its binders' names, as `.mm0` writes it:
`$ hyp $ > $ hyp $ > $ concl $`. -/
def Ctx.assertionText (c : Ctx) (id : Nat) : String :=
  let a := c.db.asserts[id]!
  let names := c.spec.binderNames id
  let pr := c.spec.printer c.db
  let say (e : Exp) : String := "$ " ++ pr.render e (fun v => names[v]?.getD (freshName v)) ++ " $"
  " > ".intercalate ((a.hyps.map say).push (say a.concl)).toList

def Open.render (o : Open) (e : Exp) : String := o.printer.render e freshName

/-- A statement with the variables of a variant's rule named by the rule's binders. -/
def Open.showForRule (o : Open) (c : Ctx) (step : Step) (e : Exp) : String :=
  let names := match step with
    | .assertion id => c.spec.binderNames id
    | .conv .. => #[]
  o.printer.render e fun v => if v < freshBase then s!"?{names[v]?.getD s!"v{v}"}" else freshName v

/-- The number of the theorem named `name` in the proof file. -/
def Ctx.theorem (c : Ctx) (name : String) : Except String Nat := do
  let some id := (Array.range c.db.asserts.size).find? (c.db.asserts[·]!.name == name)
    | throw s!"no assertion is named `{name}`"
  let isThm := c.db.file.stmts.any fun s => s.index == id && match s.kind with | .thm _ => true | _ => false
  if !isThm then throw s!"`{name}` is an axiom: there is nothing to prove"
  return id

/-! ### The tools -/

/-- What a tool returns: a JSON object, or an error for the agent. -/
abbrev ToolM := StateT State (ExceptT String IO)

def liftE {α : Type} (r : Except String α) : ToolM α :=
  match r with
  | .ok a => pure a
  | .error e => throw e

def getOpen (args : Json) : ToolM (Nat × Open) := do
  let k ← liftE (argNat args "session")
  let some (some o) := (← get).sessions[k]? | throw s!"there is no session {k}"
  return (k, o)

def putOpen (k : Nat) (o : Open) : ToolM Unit :=
  modify fun st => { st with sessions := st.sessions.set! k (some o) }

/-- What a goal node is: its number, its statement, its variants, and whether it is proved. -/
def goalJson (o : Open) (h : Nat) : Json :=
  let hyp := o.session.env.hyps[h]!
  .obj #[("node", Json.ofNat h), ("statement", o.render hyp.expr), ("variants", Json.ofNat hyp.children.size),
         ("proved", .bool !hyp.proofs.isEmpty)]

/-- The state of a session after a step: proved or not, and the size of the tree. -/
def statusJson (o : Open) (start now : Nat) : Array (String × Json) :=
  #[("proved", .bool o.session.found.isSome), ("nodes", Json.ofNat o.session.env.props.size),
    ("ms", Json.ofNat (now - start))]

def find (c : Ctx) (args : Json) : ToolM Json := do
  let glob ← liftE (argStrD args "name" "*")
  let limit ← liftE (argNatD args "limit" 20)
  let found := (Array.range c.db.asserts.size).filter fun i =>
    i < c.db.file.thms.size && globMatch glob c.db.asserts[i]!.name
  let items := (found.extract 0 limit).map fun i =>
    let isThm := c.db.file.stmts.any fun s => s.index == i && match s.kind with | .thm _ => true | _ => false
    Json.obj #[("name", c.db.asserts[i]!.name), ("kind", if isThm then "theorem" else "axiom"),
               ("statement", c.assertionText i)]
  return .obj #[("count", Json.ofNat found.size), ("assertions", .arr items)]

def start (c : Ctx) (args : Json) : ToolM Json := do
  let t0 ← IO.monoMsNow
  let thm ← liftE (c.theorem (← liftE (argStr args "theorem")))
  let forward ← liftE (argBoolD args "forward" false)
  let maxFacts ← liftE (argNatD args "max_facts" 512)
  let env := { Env.init c.db c.index (c.db.task thm) c.hypIndexes with uses := c.uses }
  let session ← Session.startFor c.vc env forward { maxFacts }
  let o : Open := { session, thm, printer := c.spec.printer c.db (c.spec.binderNames thm) }
  let k := (← get).sessions.size
  modify fun st => { st with sessions := st.sessions.push (some o) }
  return .obj (#[("session", Json.ofNat k), ("goal", goalJson o 0),
    ("premises", .arr (env.task.premises.map fun e => Json.str (o.render e))),
    ("facts", Json.ofNat (o.session.facts.size))] ++ statusJson o t0 (← IO.monoMsNow))

def goals (args : Json) : ToolM Json := do
  let (_, o) ← getOpen args
  let n ← liftE (argNatD args "n" 20)
  let opens := o.session.openGoals
  return .obj #[("open", Json.ofNat opens.size), ("goals", .arr ((opens.extract 0 n).map (goalJson o))),
    ("intermediate", .arr (o.session.hints.map (goalJson o))),
    ("proved", .bool o.session.found.isSome), ("nodes", Json.ofNat o.session.env.props.size)]

def readFilter (c : Ctx) (o : Open) (args : Json) : ToolM Filter := do
  let text ← liftE (argStrD args "filter" "all")
  match Dsl.parseFilter (o.session.dslCtx (some c.spec)) text with
  | .ok f => return f
  | .error e => throw (Dsl.ParseError.show text e)

def variants (c : Ctx) (args : Json) : ToolM Json := do
  let t0 ← IO.monoMsNow
  let (_, o) ← getOpen args
  let node ← liftE (argNat args "node")
  let f ← readFilter c o args
  let n ← liftE (argNatD args "n" 5)
  let seed ← liftE (argNatD args "seed" 0)
  let byUses ← match ← liftE (argStrD args "order" "random") with
    | "random" => pure false
    | "used" => pure true
    | o => throw s!"`order` is random or used, not `{o}`"
  let (count, sample) ← liftE (o.session.select node f n seed byUses)
  let items := sample.map fun v =>
    let view := o.session.env.propView v.prop
    Json.obj #[("variant", Json.ofNat v.prop), ("name", v.name), ("premises", Json.ofNat view.premises),
      ("used", Json.ofNat view.uses), ("expanded", .bool v.expanded),
      ("new_goals", .arr (view.goals.get.map fun e => Json.str (o.showForRule c v.step e)))]
  return .obj #[("node", Json.ofNat node), ("count", Json.ofNat count), ("sample", .arr items),
    ("ms", Json.ofNat ((← IO.monoMsNow) - t0))]

def choose (args : Json) : ToolM Json := do
  let t0 ← IO.monoMsNow
  let (k, o) ← getOpen args
  let node ← liftE (argNat args "node")
  let chosen ← liftE (argNats args "variants")
  let session ← match ← o.session.choose node chosen with
    | .ok s => pure s
    | .error e => throw e
  let o := { o with session }
  putOpen k o
  let items := chosen.map fun p =>
    Json.obj #[("variant", Json.ofNat p),
      ("new_goals", .arr (session.env.props[p]!.children.map (goalJson o)))]
  return .obj (#[("chosen", .arr items)] ++ statusJson o t0 (← IO.monoMsNow))

def run (c : Ctx) (args : Json) : ToolM Json := do
  let t0 ← IO.monoMsNow
  let (k, o) ← getOpen args
  let text ← liftE (argStr args "tactic")
  let ms ← liftE (argNatD args "ms" 1000)
  let nodes ← liftE (argNatD args "nodes" 1000000)
  let result ← match Dsl.parseTactic (o.session.dslCtx (some c.spec)) text with
    | .ok t => o.session.run t.strategy { maxProps := nodes, maxMs := ms }
    | .error e => throw (Dsl.ParseError.show text e)
  let (session, ending, stop) ← liftE result
  let o := { o with session }
  putOpen k o
  let endText := match ending with
    | .proved => "proved"
    | .exhausted => "done"
    | .limit => "limit"
  let stopText := match stop with
    | some .time => "time" | some .nodes => "nodes" | some .tuples => "tuples" | some .work => "work"
    | some .memory => "memory" | none => ""
  return .obj (#[("ending", endText), ("limit", stopText)] ++ statusJson o t0 (← IO.monoMsNow))

def goal (c : Ctx) (args : Json) : ToolM Json := do
  let t0 ← IO.monoMsNow
  let (k, o) ← getOpen args
  let text ← liftE (argStr args "statement")
  let (session, h) ← match ← o.session.goalText c.spec text with
    | .ok r => pure r
    | .error e => throw e
  let o := { o with session }
  putOpen k o
  return .obj (#[("goal", goalJson o h)] ++ statusJson o t0 (← IO.monoMsNow))

/-- A fact: its number, its statement, what made it, and whether it is on the front. -/
def factJson (o : Open) (f : Nat) : Json :=
  let env := o.session.env
  let made := match env.factView? f with
    | some v => v.name
    | none => if (o.session.hintFacts.contains f) then "intermediate goal" else "premise or axiom"
  .obj #[("fact", Json.ofNat f), ("statement", o.render env.hyps[f]!.expr), ("made_by", made),
         ("on_front", .bool (o.session.front.contains f))]

def facts (c : Ctx) (args : Json) : ToolM Json := do
  let (_, o) ← getOpen args
  let n ← liftE (argNatD args "n" 10)
  let seed ← liftE (argNatD args "seed" 0)
  let text ← liftE (argStrD args "filter" "all")
  let all := o.session.facts
  let (count, sample) ←
    if text == "all" then pure (all.size, Session.sample all n seed)
    else pure (o.session.selectFacts all (← readFilter c o args) n seed)
  return .obj #[("count", Json.ofNat count), ("front", Json.ofNat o.session.front.size),
    ("sample", .arr (sample.map (factJson o)))]

def deduce (c : Ctx) (args : Json) : ToolM Json := do
  let t0 ← IO.monoMsNow
  let (k, o) ← getOpen args
  let chosen ← liftE (argNats args "facts")
  let n ← liftE (argNatD args "n" 10)
  let seed ← liftE (argNatD args "seed" 0)
  let f ← readFilter c o args
  let (session, made) ← match ← o.session.deduce chosen with
    | .ok r => pure r
    | .error e => throw e
  let o := { o with session }
  putOpen k o
  let (count, sample) := session.selectFacts made f n seed
  return .obj (#[("made", Json.ofNat made.size), ("count", Json.ofNat count),
    ("sample", .arr (sample.map (factJson o)))] ++ statusJson o t0 (← IO.monoMsNow))

def proof (c : Ctx) (args : Json) : ToolM Json := do
  let (_, o) ← getOpen args
  match o.session.found with
  | none => return .obj #[("proved", .bool false)]
  | some f =>
    let lines := f.proof.lines c.db o.printer o.session.env.task.premises
    return .obj #[("proved", .bool true), ("verified", .bool (f.body.size > 0)),
      ("steps", .arr (lines.map Json.str))]

def close (args : Json) : ToolM Json := do
  let (k, _) ← getOpen args
  modify fun st => { st with sessions := st.sessions.set! k none }
  return .obj #[("closed", Json.ofNat k)]

/-! ### The list of tools -/

/-- A property of a tool's input: its name, JSON type, and description. -/
def prop (name type desc : String) : String × Json :=
  (name, .obj #[("type", Json.str type), ("description", Json.str desc)])

def schema (props : Array (String × Json)) (required : Array String) : Json :=
  .obj #[("type", "object"), ("properties", .obj props), ("required", .arr (required.map Json.str))]

def sessionProp : String × Json := prop "session" "integer" "the session, as `start` returned it"

def filterProp : String × Json :=
  prop "filter" "string" "a filter of the language (see `language`), such as `and(name(ax_*), premises(max=1))` or `goal($ _ -> _ $)`; `all` by default"

structure Tool where
  name : String
  description : String
  input : Json

def tools : Array Tool := #[
  ⟨"language", "The tactics and filters of the language, with what each does.", schema #[] #[]⟩,
  ⟨"find", "The assertions of the file whose names match a pattern (`*` for any characters), with their statements in the notation of the specification.",
    schema #[prop "name" "string" "the pattern of the name; `*` by default",
             prop "limit" "integer" "how many to list; 20 by default"] #[]⟩,
  ⟨"start", "Starts a session to prove a theorem of the file from the assertions before it. Returns the session, the goal (node 0) and the premises. With `forward`, the premises and the axioms without hypotheses are facts of a forward front.",
    schema #[prop "theorem" "string" "the theorem's name", prop "forward" "boolean" "seed a forward front; false by default",
             prop "max_facts" "integer" "the limit of facts of the forward front; 512 by default"] #["theorem"]⟩,
  ⟨"goals", "The open goal nodes of a session, with their statements and how many variants each has, and the intermediate goals.",
    schema #[sessionProp, prop "n" "integer" "how many open goals to list; 20 by default"] #["session"]⟩,
  ⟨"variants", "The variants of a goal node that pass a filter: how many, and a sample, each with the new goals it would make. Tighten the filter until a few are left, loosen it if none are; then `choose`.",
    schema #[sessionProp, prop "node" "integer" "the goal node", filterProp,
             prop "n" "integer" "the size of the sample; 5 by default",
             prop "seed" "integer" "the seed of the sample; 0 by default",
             prop "order" "string" "`random`, a sample drawn from the seed (the default), or `used`: those whose assertions the most proofs before the theorem use, first"] #["session", "node"]⟩,
  ⟨"choose", "Expands chosen variants of a goal node. Their new goals become goal nodes; proofs are carried down by the engine. The variants not chosen stay, and a tactic may still expand them.",
    schema #[sessionProp, prop "node" "integer" "the goal node",
             ("variants", .obj #[("type", "array"), ("items", .obj #[("type", "integer")]),
               ("description", "the variants to expand, as `variants` numbered them")])] #["session", "node", "variants"]⟩,
  ⟨"run", "Runs a tactic of the language on the tree as it is, within a time and a size. Limited by `nodes` and not by time, a run is deterministic.",
    schema #[sessionProp, prop "tactic" "string" "a tactic, such as `limited(bfs, depth=3)` or `filter(scope(ax_mp, syl), bfs)`",
             prop "ms" "integer" "the time allowed, in milliseconds; 1000 by default",
             prop "nodes" "integer" "the largest number of assertion nodes of the tree; 1000000 by default"] #["session", "tactic"]⟩,
  ⟨"goal", "Offers an intermediate goal: a statement, in the notation of the specification, that may help. It gets a goal node of its own; once it is proved, by choices, runs or deductions, it is a fact that proves the subgoals it fits and can be deduced from. `_` in it is a metavariable that its proof finds.",
    schema #[sessionProp, prop "statement" "string" "the statement, without the `$`s"] #["session", "statement"]⟩,
  ⟨"facts", "The facts of the forward front of a session: their statements, what made them, and whether they are on the front.",
    schema #[sessionProp, filterProp, prop "n" "integer" "the size of the sample; 10 by default",
             prop "seed" "integer" "the seed of the sample; 0 by default"] #["session"]⟩,
  ⟨"deduce", "Makes every deduction from chosen facts, at least one of them on the front: each application of an assertion whose hypotheses the chosen facts fill. Returns the new facts that pass a filter.",
    schema #[sessionProp, ("facts", .obj #[("type", "array"), ("items", .obj #[("type", "integer")]),
               ("description", "the facts to deduce from")]), filterProp,
             prop "n" "integer" "the size of the sample; 10 by default",
             prop "seed" "integer" "the seed of the sample; 0 by default"] #["session", "facts"]⟩,
  ⟨"proof", "The proof found, if there is one: its steps, each with the steps it uses and its statement, checked by the verifier.",
    schema #[sessionProp] #["session"]⟩,
  ⟨"close", "Ends a session and frees its tree.", schema #[sessionProp] #["session"]⟩
]

/-- Calls a tool. -/
def call (c : Ctx) (name : String) (args : Json) : ToolM Json :=
  match name with
  | "language" => return .obj #[("language", Json.str Dsl.help)]
  | "find" => find c args
  | "start" => start c args
  | "goals" => goals args
  | "variants" => variants c args
  | "choose" => choose args
  | "run" => run c args
  | "goal" => goal c args
  | "facts" => facts c args
  | "deduce" => deduce c args
  | "proof" => proof c args
  | "close" => close args
  | _ => throw s!"there is no tool `{name}`"

end Whitehead.Mcp
