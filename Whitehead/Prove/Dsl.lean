/-
The language of tactics and filters (`docs/DESIGN.md`, "Phase 4", "One DSL for tactics
and filters"): the grammar of Russell's tactic DSL (`russell-flow/docs/tactics-language.md`,
`src/ru/prover/tactics/dsl.flow`), with formulas in the notation of the specification.

    term   ::= name ( '(' arg ( ',' arg )* ')' )? | '@' name
    arg    ::= name '=' value | value
    value  ::= number | '$' formula '$' | term

A name is made of letters, digits and `_ - . * '`; a name of digits only is a number. A
formula is read by the `.mm0` parser, with `_` as a hole (`Prove/Pattern.lean`). Every
parameter can be given by position or by name. `--` starts a comment, to the end of the
line.

There are four sorts, each using only those before it (`docs/DESIGN.md`, "Composable
tactics"): a *filter* says which variants are kept; a *guide* where the proof fragments
for a goal come from; a *cost* the order of the leaves; a *tactic* is a strategy.

A *definition* is a composition with parameters, `name(p, q=default, ...) = body`, one
to a file `tactics/name.tac` (Russell's derived tactics, `russell-flow/tactics/*.tac`).
In its body `@p` stands for what the parameter is given. A call of it is its body, with
the arguments put in. `help` lists every component, and the definitions.
-/
import Whitehead.Prove.Rails

namespace Whitehead.Prove.Dsl

open Whitehead.Mm0 (ParseError)

/-- A term of the language, with the position of each part in the text. -/
inductive Ast where
  | num (n : Nat) (pos : Nat)
  /-- A formula: the text between the `$`s, and the position of the first `$`. -/
  | math (text : String) (pos : Nat)
  | call (name : String) (pos : Nat) (args : Array (Option String × Ast))
  /-- A parameter in the body of a definition, `@name`. -/
  | param (name : String) (pos : Nat)
  deriving Inhabited, Repr

def Ast.pos : Ast → Nat
  | .num _ p | .math _ p | .call _ p _ | .param _ p => p

/-- The text of a term. -/
partial def Ast.render : Ast → String
  | .num n _ => s!"{n}"
  | .math t _ => s!"${t}$"
  | .param n _ => s!"@{n}"
  | .call n _ args =>
    if args.isEmpty then n
    else
      let arg (a : Option String × Ast) : String := match a with
        | (some k, v) => s!"{k}={v.render}"
        | (none, v) => v.render
      n ++ "(" ++ ", ".intercalate (args.toList.map arg) ++ ")"

/-- A term with its parameters put in, by `vals`, and every other part at `pos`: an
error in the body of a definition is shown at its call. -/
partial def Ast.subst (vals : Std.HashMap String Ast) (pos : Nat) : Ast → Ast
  | .num n _ => .num n pos
  | .math t _ => .math t pos
  | .param n p => vals[n]?.getD (.param n p)
  | .call n _ args => .call n pos (args.map fun (k, v) => (k, v.subst vals pos))

/-- The parameters that a term names, with their positions. -/
partial def Ast.params : Ast → Array (String × Nat)
  | .param n p => #[(n, p)]
  | .call _ _ args => args.foldl (init := #[]) fun acc (_, v) => acc ++ v.params
  | _ => #[]

/-! ### Reading -/

inductive Token where
  | name (s : String)
  | math (s : String)
  | sym (c : Char)
  | param (s : String)
  deriving BEq, Inhabited

def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.' || c == '*' || c == '\''

/-- The tokens of `text`, each with its position (in characters). -/
def tokenize (text : String) : Except ParseError (Array (Token × Nat)) := do
  let cs := text.toList.toArray
  let mut out := #[]
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c.isWhitespace then
      i := i + 1
    else if c == '-' && cs[i + 1]? == some '-' then
      while i < cs.size && cs[i]! != '\n' do i := i + 1
    else if c == '@' then
      let start := i
      i := i + 1
      let mut s := ""
      while i < cs.size && isNameChar cs[i]! do
        s := s.push cs[i]!
        i := i + 1
      if s.isEmpty then throw ⟨start, "expected the name of a parameter after `@`"⟩
      out := out.push (.param s, start)
    else if c == '(' || c == ')' || c == ',' || c == '=' then
      out := out.push (.sym c, i)
      i := i + 1
    else if c == '$' then
      let start := i
      i := i + 1
      let mut body := ""
      while i < cs.size && cs[i]! != '$' do
        body := body.push cs[i]!
        i := i + 1
      if i ≥ cs.size then throw ⟨start, "this formula has no closing `$`"⟩
      i := i + 1
      out := out.push (.math body, start)
    else if isNameChar c then
      let start := i
      let mut s := ""
      while i < cs.size && isNameChar cs[i]! do
        s := s.push cs[i]!
        i := i + 1
      out := out.push (.name s, start)
    else throw ⟨i, s!"unexpected character `{c}`"⟩
  return out

abbrev ParseM := StateT Nat (Except ParseError)

partial def parseTerm (toks : Array (Token × Nat)) (endPos : Nat) : ParseM Ast := do
  let i ← get
  let some (tok, pos) := toks[i]? | throw ⟨endPos, "expected a term, but the text ends here"⟩
  set (i + 1)
  match tok with
  | .math s => return .math s pos
  | .param s => return .param s pos
  | .sym c => throw ⟨pos, s!"expected a term, found `{c}`"⟩
  | .name s =>
    if s.all Char.isDigit then return .num s.toNat! pos
    if toks[i + 1]?.map (·.1) != some (.sym '(') then return .call s pos #[]
    set (i + 2)
    let mut args := #[]
    repeat
      let j ← get
      -- a named argument: a name, then `=`
      let named : Option String :=
        match toks[j]?, toks[j + 1]? with
        | some (.name n, _), some (.sym '=', _) => some n
        | _, _ => none
      if named.isSome then set (j + 2)
      let v ← parseTerm toks endPos
      args := args.push (named, v)
      let k ← get
      match toks[k]? with
      | some (.sym ',', _) => set (k + 1)
      | some (.sym ')', _) =>
        set (k + 1)
        break
      | some (_, p) => throw ⟨p, "expected `,` or `)`"⟩
      | none => throw ⟨endPos, s!"the arguments of `{s}` are not closed by `)`"⟩
    return .call s pos args

/-- Reads a term of the language. -/
def parse (text : String) : Except ParseError Ast := do
  let toks ← tokenize text
  let endPos := text.length
  let (ast, i) ← (parseTerm toks endPos).run 0
  if let some (_, p) := toks[i]? then throw ⟨p, "expected the end of the text"⟩
  return ast

/-! ### Definitions -/

/-- A definition: a named composition with parameters. -/
structure Def where
  name : String
  /-- The parameters, in order, each with its default, if any. -/
  params : Array (String × Option Ast)
  body : Ast
  /-- Its head, `name(p, q=default, ...)`, for `help`. -/
  signature : String
  /-- The comment lines at the top of its file. -/
  help : String := ""
  deriving Inhabited

abbrev Defs := Std.HashMap String Def

/-! ### Building -/

/-- What building needs: the database, and for patterns the specification and the
theorem whose variables they may name, with what those are in its task. -/
structure Ctx where
  db : Db
  spec : Option Notation := none
  thm : Nat := 0
  vars : Nat → Exp := fun _ => default
  /-- The subproofs of the file, for `follow` (`Rails.lean`): made when first asked for. -/
  rails : Option (Thunk Rails) := none
  /-- The definitions that may be called. -/
  defs : Defs := {}
  /-- How many calls of definitions the term being built is inside. -/
  expansions : Nat := 0
  /-- The learned model that `by=model` ranks by (`Model.lean`), if one is loaded. -/
  model : Option Model := none

/-- A component of the language, for `help` and for the messages. -/
structure Doc where
  name : String
  sort : String
  signature : String
  help : String

def docs : Array Doc := #[
  ⟨"all", "filter", "all", "every variant"⟩,
  ⟨"name", "filter", "name(G)",
    "the step's name matches G, in which * stands for any characters: the assertion's name, or the def's for an unfolding"⟩,
  ⟨"scope", "filter", "scope(a1, a2, ...)", "an assertion among these, by name"⟩,
  ⟨"kind", "filter", "kind(assertion | unfold | fold)", "the kind of step"⟩,
  ⟨"premises", "filter", "premises(N) | premises(min=N, max=N)",
    "the number of premises of the step: of its new goals, backward"⟩,
  ⟨"goal", "filter", "goal($ pattern $)", "backward: one of the new goals matches the pattern; _ is a hole"⟩,
  ⟨"result", "filter", "result($ pattern $)",
    "what the step proves matches the pattern: the goal, backward; the fact deduced, forward"⟩,
  ⟨"used", "filter", "used(N) | used(min=N)",
    "the assertion is used in at least N proofs of the theorems before the one being proved"⟩,
  ⟨"fits", "filter", "fits($ pattern $)",
    "backward: one of the new goals could become the pattern: as goal, but a metavariable of the new goal matches anything"⟩,
  ⟨"proves", "filter", "proves($ pattern $)", "what the step proves, the goal under its unifier, matches the pattern"⟩,
  ⟨"ground", "filter", "ground", "the goal has no metavariable"⟩,
  ⟨"hyp", "filter", "hyp",
    "backward: one of the new goals, not a bare metavariable, unifies with a premise of the theorem, which proves it at once"⟩,
  ⟨"bare", "filter", "bare",
    "backward: one of the new goals is a bare variable, which anything fits, such as the minor premise of ax_mp"⟩,
  ⟨"and", "filter", "and(f1, f2, ...)", "every filter passes"⟩,
  ⟨"or", "filter", "or(f1, f2, ...)", "one of the filters passes"⟩,
  ⟨"not", "filter", "not(f)", "the filter does not pass"⟩,
  ⟨"bfs", "tactic", "bfs(filter=F, size=N, depth=N)",
    "breadth first: every leaf, round by round; the fair strategy of the completeness theorem. With filter, only the variants that pass; size and depth as in limited: bfs(filter=f, size=N, depth=M) is limited(filter(f, bfs), size=N, depth=M)"⟩,
  ⟨"search", "tactic", "search(cost=depth, filter=F, size=N, depth=N)",
    "each round, the unexpanded leaves of the least cost; with depth, breadth-first round for round (on a tree without intermediate goals, whose leaves cost less); filter, size and depth as for bfs"⟩,
  ⟨"follow", "tactic", "follow(guide, at=open, upto=N, ground=false, chain=false)",
    "the guide's fragments put down at goals and followed step by step, and nothing else; at: open (every open goal, each once) or root; upto: only at goals with at most N assertion nodes above them that follow did not expand; ground: only at goals without metavariables; chain: also at the goals that a fragment left open (without it, fragments are not put down on one another without end); a branch that does not fit ends; its nodes are labelled follow; unbounded alone: within limited or a time"⟩,
  ⟨"forward", "tactic", "forward", "the forward front alone, a wave at a time"⟩,
  ⟨"both", "tactic", "both", "a round backward and a wave forward in turn"⟩,
  ⟨"done", "tactic", "done", "does nothing"⟩,
  ⟨"filter", "tactic", "filter(f, t)", "t, expanding only the variants that pass the filter f; the others stay leaves"⟩,
  ⟨"limited", "tactic", "limited(t, size=N, depth=N)",
    "t, until N more assertion nodes are made, and only leaves at depth N or less, counted from the root (0: no limit); the time is a limit of the run"⟩,
  ⟨"seq", "tactic", "seq(t1, t2, ...)", "each tactic in turn, the next when the one before is done"⟩,
  ⟨"first", "tactic", "first(t1, t2, ...)",
    "each round, the first tactic that has something to expand; the others wait: combined by order, where seq combines in time"⟩,
  ⟨"focus", "tactic", "focus(N, t)", "t, only in the subtree of goal node N"⟩,
  ⟨"loop", "tactic", "loop(t, N)", "t again from its start each time it is done, while the tree grows, up to N times"⟩,
  ⟨"depth", "cost", "depth(L1, L2, ..., penalty=N, by=used|recent|model, width=W)",
    "the number of assertion nodes above a leaf's goal; those labelled L1, L2, ... (follow, choose or search: who expanded them) cost nothing, the other variants at a goal where such a node hangs cost the goal's full depth, and a goal that such a node left open costs N more; with by and width, a step costs 1 and its place among the variants of its goal (from 0), by the proofs before the theorem that use its assertion (used: how many; recent: the latest) or by the learned model's score (model, with --model FILE), divided by W"⟩,
  ⟨"subproofs", "guide", "subproofs(count=3, rank=occurrences, min=2, source=earlier, open=N)",
    "subproofs of earlier proofs that fit the goal: count of them; rank occurrences (in the most proofs before the theorem), size (the largest), small, reach (those leaving the fewest hypotheses that no premise fits first), specific (those whose conclusion has the most nodes that are not variables first) or recent (those in the latest proof before the theorem first); open: only those leaving at most N open; min: the fewest steps; source earlier (in a proof before the theorem) or recurring (in two)"⟩,
  ⟨"proof", "guide", "proof", "the theorem's own proof, when it is one of the file: for tests"⟩
]

/-- The list of the components, by sort, and of the definitions. -/
def helpWith (defs : Defs) : String :=
  let section_ (sort : String) : String :=
    (docs.filter (·.sort == sort)).foldl (init := s!"{sort}s:\n") fun acc d =>
      acc ++ s!"  {d.signature}\n      {d.help}\n"
  let ds := defs.toArray.qsort (·.1 < ·.1)
  let definitions := ds.foldl (init := "definitions (tactics/*.tac):\n") fun acc (_, d) =>
    acc ++ s!"  {d.signature}\n      {d.help}\n"
  section_ "tactic" ++ section_ "cost" ++ section_ "guide" ++ section_ "filter" ++
    (if ds.isEmpty then "" else definitions)

def help : String := helpWith {}

def sortOf (name : String) : Option String :=
  (docs.find? (·.name == name)).map (·.sort)

universe u

def fail {α : Type u} (pos : Nat) (msg : String) : Except ParseError α := throw ⟨pos, msg⟩

/-- A result of the filters' universe in that of the tactics, whose state types make
them one universe up (`AnyStrategy`). -/
def up {α : Type} (r : Except ParseError α) : Except ParseError (ULift.{1} α) := r.map ULift.up

/-- The argument named `key`, or else the one at position `idx`. -/
def arg? (args : Array (Option String × Ast)) (key : String) (idx : Nat) : Option Ast :=
  match args.find? (·.1 == some key) with
  | some (_, v) => some v
  | none =>
    let positional := args.filter (·.1.isNone)
    positional[idx]?.map (·.2)

def checkNames (name : String) (args : Array (Option String × Ast)) (keys : Array String) :
    Except ParseError Unit := do
  for (k, v) in args do
    if let some k := k then
      if !keys.contains k then fail v.pos s!"`{name}` has no parameter `{k}`"

def num (name key : String) (pos : Nat) : Option Ast → Except ParseError Nat
  | some (.num n _) => pure n
  | some a => fail a.pos s!"`{key}` of `{name}` is a number"
  | none => fail pos s!"`{name}` needs `{key}`"

def numOr (name key : String) (dflt : Nat) : Option Ast → Except ParseError Nat
  | none => pure dflt
  | a => num name key 0 a

/-- A bare name, as an argument. -/
def word (name key : String) (pos : Nat) : Option Ast → Except ParseError String
  | some (.call w _ #[]) => pure w
  | some (.num n _) => pure s!"{n}"
  | some a => fail a.pos s!"`{key}` of `{name}` is a name"
  | none => fail pos s!"`{name}` needs `{key}`"

/-- A bare name, or `dflt` when the argument is not given. -/
def wordOr (name key dflt : String) : Option Ast → Except ParseError String
  | none => pure dflt
  | a => word name key 0 a

def pattern (c : Ctx) (name : String) (pos : Nat) : Option Ast → Except ParseError Exp
  | some (.math text p) =>
    match c.spec with
    | some n => n.pattern c.thm c.vars text p
    | none => fail p "a pattern needs the specification (.mm0) for its notation"
  | some a => fail a.pos s!"`{name}` takes a formula, `$ ... $`"
  | none => fail pos s!"`{name}` needs a formula, `$ ... $`"

def wrongSort {α : Type u} (name : String) (pos : Nat) (expected : String) : Except ParseError α :=
  match sortOf name with
  | some s => fail pos s!"`{name}` is a {s}; a {expected} is expected here"
  | none => fail pos s!"unknown {expected} `{name}`"

def notHere {α : Type u} (name : String) (pos : Nat) : Except ParseError α :=
  fail pos s!"`@{name}` is a parameter of a definition, outside one"

/-- The body of definition `d` for a call at `pos` with `args`: each parameter given by
name, or else by position, or else its default. -/
def Def.instantiate (d : Def) (pos : Nat) (args : Array (Option String × Ast)) : Except ParseError Ast := do
  for (k, v) in args do
    if let some k := k then
      if !d.params.any (·.1 == k) then fail v.pos s!"`{d.name}` has no parameter `{k}`"
  let positional := args.filter (·.1.isNone)
  if let some (_, v) := positional[d.params.size]? then
    fail v.pos s!"`{d.name}` has {d.params.size} parameters"
  let mut vals : Std.HashMap String Ast := {}
  for i in [0:d.params.size] do
    let (p, dflt) := d.params[i]!
    match arg? args p i, dflt with
    | some v, _ => vals := vals.insert p v
    | none, some v => vals := vals.insert p (v.subst {} pos)
    | none, none => fail pos s!"`{d.name}` needs `{p}`"
  return d.body.subst vals pos

/-- The body of a call of a definition, with the context to build it in; none if
`name` is not a definition. -/
def Ctx.expand? (c : Ctx) (name : String) (pos : Nat) (args : Array (Option String × Ast)) :
    Option (Except ParseError (Ast × Ctx)) :=
  c.defs[name]?.map fun d =>
    if c.expansions ≥ 64 then fail pos s!"`{name}`: the definitions call one another without end"
    else (d.instantiate pos args).map (·, { c with expansions := c.expansions + 1 })

def boolOr (name key : String) (dflt : Bool) : Option Ast → Except ParseError Bool
  | none => pure dflt
  | some a => do
    match ← word name key a.pos (some a) with
    | "true" => pure true
    | "false" => pure false
    | w => fail a.pos s!"`{key}` is true or false, not `{w}`"

def rankOr (name : String) (a : Option Ast) : Except ParseError RailRank := do
  match ← wordOr name "rank" "occurrences" a with
  | "occurrences" => pure .occurrences
  | "size" => pure .size
  | "small" => pure .small
  | "reach" => pure .reach
  | "specific" => pure .specific
  | "recent" => pure .recent
  | w => fail ((a.map (·.pos)).getD 0) s!"`rank` is occurrences, size, small, reach, specific or recent, not `{w}`"

def sourceOr (name : String) (a : Option Ast) : Except ParseError RailSource := do
  match ← wordOr name "source" "earlier" a with
  | "earlier" => pure .earlier
  | "recurring" => pure .recurring
  | w => fail ((a.map (·.pos)).getD 0) s!"`source` is earlier or recurring, not `{w}`"

def seedsOr (name : String) (a : Option Ast) : Except ParseError RailSeeds := do
  match ← wordOr name "at" "open" a with
  | "open" => pure .open
  | "root" => pure .root
  | w => fail ((a.map (·.pos)).getD 0) s!"`at` is open or root, not `{w}`"

def labelOf (name : String) (a : Ast) : Except ParseError Label := do
  match ← word name "a label" a.pos (some a) with
  | "follow" => pure .follow
  | "choose" => pure .choose
  | "search" => pure .search
  | w => fail a.pos s!"a label of `{name}` is follow, choose or search, not `{w}`"

partial def filter (c : Ctx) (a : Ast) : Except ParseError Filter := do
  match a with
  | .num _ p => fail p "a filter is expected here, not a number"
  | .math _ p => fail p "a filter is expected here, not a formula: `goal($ ... $)` or `result($ ... $)`"
  | .param n p => notHere n p
  | .call name pos args =>
    match name with
    | "all" => return .all
    | "name" =>
      checkNames name args #["glob"]
      return .name (← word name "glob" pos (arg? args "glob" 0))
    | "scope" =>
      checkNames name args #[]
      let mut ids := #[]
      for (_, v) in args do
        let n ← word name "an assertion" v.pos (some v)
        let found := (Array.range c.db.asserts.size).filter (c.db.asserts[·]!.name == n)
        if found.isEmpty then fail v.pos s!"no assertion is named `{n}`"
        ids := ids ++ found
      return .scope ids
    | "kind" =>
      checkNames name args #["kind"]
      match ← word name "kind" pos (arg? args "kind" 0) with
      | "assertion" => return .kind .assertion
      | "unfold" => return .kind .unfold
      | "fold" => return .kind .fold
      | k => fail pos s!"`kind` is assertion, unfold or fold, not `{k}`"
    | "premises" =>
      checkNames name args #["min", "max"]
      if let some (Ast.num n _) := (args.find? (·.1.isNone)).map (·.2) then return .premises n n
      let lo ← numOr name "min" 0 (args.find? (·.1 == some "min") |>.map (·.2))
      let hi ← numOr name "max" 0xFFFFFFFF (args.find? (·.1 == some "max") |>.map (·.2))
      return .premises lo hi
    | "goal" =>
      checkNames name args #["pattern"]
      return .goal (← pattern c name pos (arg? args "pattern" 0))
    | "result" =>
      checkNames name args #["pattern"]
      return .result (← pattern c name pos (arg? args "pattern" 0))
    | "fits" =>
      checkNames name args #["pattern"]
      return .fits (← pattern c name pos (arg? args "pattern" 0))
    | "proves" =>
      checkNames name args #["pattern"]
      return .proves (← pattern c name pos (arg? args "pattern" 0))
    | "ground" => return .ground
    | "hyp" => return .hyp
    | "bare" => return .bare
    | "used" =>
      checkNames name args #["min"]
      return .used (← num name "min" pos (arg? args "min" 0))
    | "and" | "or" =>
      checkNames name args #[]
      if args.isEmpty then fail pos s!"`{name}` needs at least one filter"
      let fs ← args.mapM fun (_, v) => filter c v
      return if name == "and" then .and fs else .or fs
    | "not" =>
      checkNames name args #["filter"]
      let some f := arg? args "filter" 0 | fail pos "`not` needs a filter"
      return .not (← filter c f)
    | _ =>
      match c.expand? name pos args with
      | some r =>
        let (body, c') ← r
        filter c' body
      | none => wrongSort name pos "filter"

partial def guide (c : Ctx) (a : Ast) : Except ParseError Guide := do
  match a with
  | .num _ p => fail p "a guide is expected here, not a number"
  | .math _ p => fail p "a guide is expected here, not a formula"
  | .param n p => notHere n p
  | .call name pos args =>
    match name with
    | "subproofs" =>
      checkNames name args #["count", "rank", "min", "source", "open"]
      let count ← numOr name "count" 3 (arg? args "count" 0)
      let rank ← rankOr name (arg? args "rank" 1)
      let minSize ← numOr name "min" 2 (arg? args "min" 2)
      let source ← sourceOr name (arg? args "source" 3)
      let maxOpen ← numOr name "open" 1000000 (arg? args "open" 4)
      return .subproofs { count, rank, minSize, source, maxOpen }
    | "proof" =>
      checkNames name args #[]
      return .proof
    | _ =>
      match c.expand? name pos args with
      | some r =>
        let (body, c') ← r
        guide c' body
      | none => wrongSort name pos "guide"

partial def cost (c : Ctx) (a : Ast) : Except ParseError Cost := do
  match a with
  | .num _ p => fail p "a cost is expected here, not a number"
  | .math _ p => fail p "a cost is expected here, not a formula"
  | .param n p => notHere n p
  | .call name pos args =>
    match name with
    | "depth" =>
      checkNames name args #["penalty", "by", "width"]
      let free ← (args.filter (·.1.isNone)).mapM fun (_, v) => labelOf name v
      let named (k : String) : Option Ast := (args.find? (·.1 == some k)).map (·.2)
      let penalty ← numOr name "penalty" 0 (named "penalty")
      let rank ← match named "by" with
        | none => pure none
        | some a => match ← word name "by" a.pos (some a) with
          | "used" => pure (some VariantRank.used)
          | "recent" => pure (some .recent)
          | "model" =>
            match c.model with
            | some m => pure (some (.learned m))
            | none => fail a.pos "`by=model` needs a model (--model FILE)"
          | w => fail a.pos s!"`by` is used, recent or model, not `{w}`"
      let width ← numOr name "width" 0 (named "width")
      if rank.isSome && width == 0 then fail pos "`depth` with `by` needs a `width`"
      return .depth free penalty rank width
    | _ =>
      match c.expand? name pos args with
      | some r =>
        let (body, c') ← r
        cost c' body
      | none => wrongSort name pos "cost"

/-- `t` with the filter, size and depth that `bfs` and `search` take, from position `i`:
`limited(filter(f, t), size=N, depth=M)`. -/
def withLimits (c : Ctx) (name : String) (args : Array (Option String × Ast)) (i : Nat) (t : AnyStrategy) :
    Except ParseError AnyStrategy := do
  let t ← match arg? args "filter" i with
    | some f => do
      let f ← up (filter c f)
      pure (t.filtered f.down)
    | none => pure t
  let size ← up (numOr name "size" 0 (arg? args "size" (i + 1)))
  let depth ← up (numOr name "depth" 0 (arg? args "depth" (i + 2)))
  return t.limited size.down depth.down

partial def tactic (c : Ctx) (a : Ast) : Except ParseError AnyStrategy := do
  match a with
  | .num _ p => fail p "a tactic is expected here, not a number"
  | .math _ p => fail p "a tactic is expected here, not a formula"
  | .param n p => notHere n p
  | .call name pos args =>
    match name with
    | "bfs" =>
      let _ ← up (checkNames name args #["filter", "size", "depth"])
      withLimits c name args 0 ⟨breadthFirst⟩
    | "search" =>
      let _ ← up (checkNames name args #["cost", "filter", "size", "depth"])
      let k ← up (match arg? args "cost" 0 with
        | some a => cost c a
        | none => pure (Cost.depth))
      withLimits c name args 1 ⟨Strategy.search k.down⟩
    | "follow" =>
      let _ ← up (checkNames name args #["guide", "at", "upto", "ground", "chain"])
      let some r := c.rails | fail pos "`follow` needs the subproofs of the file"
      let some g := arg? args "guide" 0 | fail pos "`follow` needs a guide"
      let g ← up (guide c g)
      let seeds ← up (seedsOr name (arg? args "at" 1))
      let upto ← up (match arg? args "upto" 2 with
        | some a => (num name "upto" pos (some a)).map some
        | none => pure none)
      let ground ← up (boolOr name "ground" false (arg? args "ground" 3))
      let chain ← up (boolOr name "chain" false (arg? args "chain" 4))
      return ⟨Strategy.follow r.get { guide := g.down, seeds := seeds.down, upto := upto.down,
                                      ground := ground.down, chain := chain.down }⟩
    | "first" =>
      let _ ← up (checkNames name args #[])
      let rev := args.reverse
      let some last := rev[0]? | fail pos "`first` needs at least one tactic"
      let mut t ← tactic c last.2
      for (_, v) in rev.extract 1 rev.size do
        t := (← tactic c v).first t
      return t
    | "forward" => return ⟨forwardOnly⟩
    | "both" => return ⟨bidirectional⟩
    | "done" => return ⟨Strategy.done⟩
    | "filter" =>
      let _ ← up (checkNames name args #["filter", "tactic"])
      let some f := arg? args "filter" 0 | fail pos "`filter` needs a filter"
      let some t := arg? args "tactic" 1 | fail pos "`filter` needs a tactic"
      let f ← up (filter c f)
      return (← tactic c t).filtered f.down
    | "limited" =>
      let _ ← up (checkNames name args #["tactic", "size", "depth"])
      let some t := arg? args "tactic" 0 | fail pos "`limited` needs a tactic"
      let size ← up (numOr name "size" 0 (arg? args "size" 1))
      let depth ← up (numOr name "depth" 0 (arg? args "depth" 2))
      return (← tactic c t).limited size.down depth.down
    | "focus" =>
      let _ ← up (checkNames name args #["node", "tactic"])
      let node ← up (num name "node" pos (arg? args "node" 0))
      let some t := arg? args "tactic" 1 | fail pos "`focus` needs a tactic"
      return (← tactic c t).focus node.down
    | "loop" =>
      let _ ← up (checkNames name args #["tactic", "times"])
      let some t := arg? args "tactic" 0 | fail pos "`loop` needs a tactic"
      let n ← up (num name "times" pos (arg? args "times" 1))
      return (← tactic c t).loop n.down
    | "seq" =>
      let _ ← up (checkNames name args #[])
      let some first := args[0]? | fail pos "`seq` needs at least one tactic"
      let mut t ← tactic c first.2
      for (_, v) in args.extract 1 args.size do
        t := t.seq (← tactic c v)
      return t
    | _ =>
      match c.expand? name pos args with
      | some r =>
        let x ← up r
        tactic x.down.2 x.down.1
      | none => wrongSort name pos "tactic"

/-- Reads a filter. -/
def parseFilter (c : Ctx) (text : String) : Except ParseError Filter := do
  filter c (← parse text)

/-- Reads a tactic. -/
def parseTactic (c : Ctx) (text : String) : Except ParseError AnyStrategy := do
  tactic c (← up (parse text)).down

/-- Reads a definition: comment lines `--`, which are its help, then
`name(p, q=default, ...) = body`. -/
def parseDef (text : String) : Except ParseError Def := do
  let toks ← tokenize text
  let endPos := text.length
  let (head, i) ← (parseTerm toks endPos).run 0
  match toks[i]? with
  | some (.sym '=', _) => pure ()
  | some (_, p) => throw ⟨p, "expected `=` after the head of the definition"⟩
  | none => throw ⟨endPos, "expected `=` and the body of the definition"⟩
  let (body, j) ← (parseTerm toks endPos).run (i + 1)
  if let some (_, p) := toks[j]? then throw ⟨p, "expected the end of the definition"⟩
  let .call name _ hargs := head | throw ⟨head.pos, "a definition starts with its name"⟩
  let mut params : Array (String × Option Ast) := #[]
  for (k, v) in hargs do
    let p ← match k, v with
      | none, .call p _ #[] => pure (p, none)
      | some k, v =>
        if let some (n, q) := v.params[0]? then throw ⟨q, s!"a default cannot name a parameter, `@{n}`"⟩
        pure (k, some v)
      | none, v => throw ⟨v.pos, "a parameter is a name, or name=default"⟩
    if params.any (·.1 == p.1) then throw ⟨v.pos, s!"the parameter `{p.1}` is there twice"⟩
    params := params.push p
  for (n, q) in body.params do
    if !params.any (·.1 == n) then throw ⟨q, s!"`@{n}` is not a parameter of `{name}`"⟩
  -- the help: the comment lines before the definition
  let lines := (text.splitOn "\n").map (·.trimAscii.toString)
  let comments := lines.takeWhile fun l => l.isEmpty || l.startsWith "--"
  let help := " ".intercalate (comments.filterMap fun l =>
    if l.startsWith "--" then some (l.drop 2).trimAscii.toString else none)
  return { name, params, body, signature := head.render, help }

/-- Line and column, from 1, of character `pos` of `text`. -/
def lineCol (text : String) (pos : Nat) : Nat × Nat :=
  (text.toList.take pos).foldl (init := (1, 1)) fun (l, c) ch => if ch == '\n' then (l + 1, 1) else (l, c + 1)

/-- The definitions of directory `dir`: each file `name.tac` in it defines `name`. A
definition may not have the name of a component of the language. -/
def loadDefs (dir : System.FilePath) : IO (Except String Defs) := do
  let mut defs : Defs := {}
  let files := ((← dir.readDir).filter (·.path.extension == some "tac")).map (·.path)
  for f in files.qsort (·.toString < ·.toString) do
    let text ← IO.FS.readFile f
    match parseDef text with
    | .error e =>
      let (l, c) := lineCol text e.pos
      return .error s!"{f}:{l}:{c}: {e.msg}"
    | .ok d =>
      if some d.name != f.fileStem then return .error s!"{f}: it defines `{d.name}`, not `{f.fileStem.getD ""}`"
      if (docs.any (·.name == d.name)) then return .error s!"{f}: `{d.name}` is a component of the language"
      defs := defs.insert d.name d
  return .ok defs

/-- Where the definitions are: `given`, else `tactics` in the working directory, else
`tactics` in the repository the program was built in (it is `.lake/build/bin` there). -/
def tacticsDir (given : Option System.FilePath := none) : IO (Option System.FilePath) := do
  if let some d := given then return some d
  if ← System.FilePath.isDir "tactics" then return some "tactics"
  let app ← IO.appPath
  if let some repo := app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent) then
    if ← (repo / "tactics").isDir then return some (repo / "tactics")
  return none

/-- The definitions of `tacticsDir given`; none if there is no such directory. -/
def loadTactics (given : Option System.FilePath := none) : IO (Except String Defs) := do
  match ← tacticsDir given with
  | some dir => loadDefs dir
  | none => return .ok {}

/-- An error with the text and a caret under where it is. -/
def ParseError.show (text : String) (e : ParseError) : String :=
  s!"{text}\n{"".pushn ' ' e.pos}^ {e.msg}"

end Whitehead.Prove.Dsl
