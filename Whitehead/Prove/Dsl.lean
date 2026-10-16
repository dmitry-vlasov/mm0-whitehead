/-
The language of tactics and filters (`docs/DESIGN.md`, "Phase 4", "One DSL for tactics
and filters"): the grammar of Russell's tactic DSL (`russell-flow/docs/tactics-language.md`,
`src/ru/prover/tactics/dsl.flow`), with formulas in the notation of the specification.

    term   ::= name ( '(' arg ( ',' arg )* ')' )?
    arg    ::= name '=' value | value
    value  ::= number | '$' formula '$' | term

A name is made of letters, digits and `_ - . * '`; a name of digits only is a number. A
formula is read by the `.mm0` parser, with `_` as a hole (`Prove/Pattern.lean`). Every
parameter can be given by position or by name.

There are two sorts. A *filter* says which variants are kept; a *tactic* is a strategy.
A tactic may take a filter; a filter never takes a tactic. `help` lists every component.
-/
import Whitehead.Prove.Combinators

namespace Whitehead.Prove.Dsl

open Whitehead.Mm0 (ParseError)

/-- A term of the language, with the position of each part in the text. -/
inductive Ast where
  | num (n : Nat) (pos : Nat)
  /-- A formula: the text between the `$`s, and the position of the first `$`. -/
  | math (text : String) (pos : Nat)
  | call (name : String) (pos : Nat) (args : Array (Option String × Ast))
  deriving Inhabited, Repr

def Ast.pos : Ast → Nat
  | .num _ p | .math _ p | .call _ p _ => p

/-! ### Reading -/

inductive Token where
  | name (s : String)
  | math (s : String)
  | sym (c : Char)
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

/-! ### Building -/

/-- What building needs: the database, and for patterns the specification and the
theorem whose variables they may name, with what those are in its task. -/
structure Ctx where
  db : Db
  spec : Option Notation := none
  thm : Nat := 0
  vars : Nat → Exp := fun _ => default

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
  ⟨"hyp", "filter", "hyp", "backward: one of the new goals unifies with a premise of the theorem, which proves it at once"⟩,
  ⟨"bare", "filter", "bare",
    "backward: one of the new goals is a bare variable, which anything fits, such as the minor premise of ax_mp"⟩,
  ⟨"and", "filter", "and(f1, f2, ...)", "every filter passes"⟩,
  ⟨"or", "filter", "or(f1, f2, ...)", "one of the filters passes"⟩,
  ⟨"not", "filter", "not(f)", "the filter does not pass"⟩,
  ⟨"bfs", "tactic", "bfs", "breadth first: every leaf, round by round; the fair strategy of the completeness theorem"⟩,
  ⟨"forward", "tactic", "forward", "the forward front alone, a wave at a time"⟩,
  ⟨"both", "tactic", "both", "a round backward and a wave forward in turn"⟩,
  ⟨"done", "tactic", "done", "does nothing"⟩,
  ⟨"filter", "tactic", "filter(f, t)", "t, expanding only the variants that pass the filter f; the others stay leaves"⟩,
  ⟨"limited", "tactic", "limited(t, size=N, depth=N)",
    "t, until N more assertion nodes are made, and only leaves at depth N or less, counted from the root (0: no limit); the time is a limit of the run"⟩,
  ⟨"seq", "tactic", "seq(t1, t2, ...)", "each tactic in turn, the next when the one before is done"⟩,
  ⟨"focus", "tactic", "focus(N, t)", "t, only in the subtree of goal node N"⟩
]

/-- The list of the components, by sort. -/
def help : String :=
  let section_ (sort : String) : String :=
    (docs.filter (·.sort == sort)).foldl (init := s!"{sort}s:\n") fun acc d =>
      acc ++ s!"  {d.signature}\n      {d.help}\n"
  section_ "tactic" ++ section_ "filter"

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

partial def filter (c : Ctx) (a : Ast) : Except ParseError Filter := do
  match a with
  | .num _ p => fail p "a filter is expected here, not a number"
  | .math _ p => fail p "a filter is expected here, not a formula: `goal($ ... $)` or `result($ ... $)`"
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
    | _ => wrongSort name pos "filter"

partial def tactic (c : Ctx) (a : Ast) : Except ParseError AnyStrategy := do
  match a with
  | .num _ p => fail p "a tactic is expected here, not a number"
  | .math _ p => fail p "a tactic is expected here, not a formula"
  | .call name pos args =>
    match name with
    | "bfs" => return ⟨breadthFirst⟩
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
    | "seq" =>
      let _ ← up (checkNames name args #[])
      let some first := args[0]? | fail pos "`seq` needs at least one tactic"
      let mut t ← tactic c first.2
      for (_, v) in args.extract 1 args.size do
        t := t.seq (← tactic c v)
      return t
    | _ => wrongSort name pos "tactic"

/-- Reads a filter. -/
def parseFilter (c : Ctx) (text : String) : Except ParseError Filter := do
  filter c (← parse text)

/-- Reads a tactic. -/
def parseTactic (c : Ctx) (text : String) : Except ParseError AnyStrategy := do
  tactic c (← up (parse text)).down

/-- An error with the text and a caret under where it is. -/
def ParseError.show (text : String) (e : ParseError) : String :=
  s!"{text}\n{"".pushn ' ' e.pos}^ {e.msg}"

end Whitehead.Prove.Dsl
