/-
A session: the proof variant tree of one task, kept between the requests of an agent
(`docs/DESIGN.md`, "Phase 4", "The session"). The agent, a human or an AI, sees the goal
nodes (`RuProverExp`, `RuProverRoot`) and their variants (`RuProverProp`). It chooses
variants to expand, and it runs strategies on the tree as it is. The engine does the
rest: unification, the substitutions, and the joins of proofs on the way to the root.
It never asks the agent for a substitution.

Backward, the agent chooses variants of a goal node (`choose`). Forward, it chooses
facts, at least one of them on the front, and the engine makes every deduction from
them (`deduce`). And it offers intermediate goals (`goal`): hints that may lead to a
proof (`Forward.lean`, "Intermediate goals"). Russell's interactive prover drives its backward tree in the same way
(`prove-expand`, `prove-candidates` in `russell-flow/src/ru/prover/commands`).
-/
import Whitehead.Prove.Dsl

namespace Whitehead.Prove

/-- A variant of a goal node: one of its assertion nodes. -/
structure Variant where
  prop : Nat
  step : Step
  /-- The assertion's name, or `unfold t` / `fold t` for an unfolding. -/
  name : String
  expanded : Bool
  /-- The goal nodes it has made, one for each of its premises, once it is expanded. -/
  goals : Array Nat
  deriving Inhabited

structure Session where
  accept : Env → ProofTree → Array Cond → Except String ByteArray
  env : Env
  rej : Rejections := {}
  /-- The first proof accepted. -/
  found : Option Found := none
  /-- Its number among the searches that are running (`runningSizes`). -/
  sid : Nat
  /-- The limit of facts of the forward front (`Limits.maxFacts`). -/
  maxFacts : Nat := 512

namespace Session

/-- A session on the task of `env`: the root is expanded, and nothing else. A goal that is
one of the premises is proved at once. With `forward`, the forward front is seeded
first, from the premises and the assertions without hypotheses (`seedForward`): it must
be there before the root is expanded, so that the subgoals are recorded for the joins.
The forward direction needs `env` to have the indexes of the hypotheses
(`Env.init` with `Db.hypIndexes`). -/
def start (accept : Env → ProofTree → Array Cond → Except String ByteArray) (env : Env)
    (forward : Bool := false) (limits : Limits := {}) : IO Session := do
  let sid ← nextSearch.modifyGet fun n => (n, n + 1)
  let strategy := { breadthFirst with forward }
  let maxFacts := limits.maxFacts
  match ← searchStart accept env strategy limits (← IO.monoMsNow) sid with
  | .finished r => return { accept, env := r.env, rej := r.rejections, found := r.found?, sid, maxFacts }
  | .running env rej => return { accept, env, rej, sid, maxFacts }

/-- `start` for a theorem of the file: a proof counts if the verifier accepts its body. -/
def startFor (vc : Verify.Ctx) (env : Env) (forward : Bool := false) (limits : Limits := {}) : IO Session :=
  start (Prove.accept vc) env forward limits

def variant (s : Session) (p : Nat) : Variant :=
  let prop := s.env.props[p]!
  let name := match prop.step with
    | .assertion id => s.env.db.asserts[id]!.name
    | .conv t _ unfold => s!"{if unfold then "unfold" else "fold"} {s.env.db.terms[t]!.name}"
  { prop := p, step := prop.step, name, expanded := prop.expanded, goals := prop.children }

/-- Is `h` a goal node of a backward tree: of the main goal's, or of an intermediate
goal's? A fact of the forward front is an expression node without a parent, and the
hypotheses of an application forward lead up to a fact, not to a goal. -/
def isGoal (s : Session) (h : Nat) : Bool := Id.run do
  let mut h := h
  for _ in [0:s.env.hyps.size] do
    if h == 0 || s.env.hints.contains h then return true
    match s.env.hyps[h]? with
    | some { parent := some p, .. } => h := s.env.props[p]!.parent
    | _ => return false
  return false

/-- Is `f` a fact of the forward front? -/
def isFact (s : Session) (f : Nat) : Bool :=
  match s.env.hyps[f]? with
  | some hyp => hyp.factProof.isSome
  | none => false

/-- The facts, in the order they were made. -/
def facts (s : Session) : Array Nat :=
  (Array.range s.env.hyps.size).filter s.isFact

/-- The goal nodes of the intermediate goals, in the order they were offered. -/
def hints (s : Session) : Array Nat := s.env.hints

/-- The facts made from the proofs of the intermediate goals. -/
def hintFacts (s : Session) : Array Nat := (s.env.forward.map (·.hintFacts)).getD #[]

/-- The facts on the front: those not expanded forward yet, without a restriction. -/
def front (s : Session) : Array Nat :=
  ((s.env.forward.map (·.front)).getD #[])

/-- The variants of goal node `h`, in the order they were made. -/
def variants (s : Session) (h : Nat) : Except String (Array Variant) :=
  if !s.isGoal h then .error s!"{h} is not a goal node"
  else .ok (s.env.hyps[h]!.children.map s.variant)

/-- `n` of `xs`, chosen by a pseudo-random permutation that `seed` fixes, in the order of
`xs`: a sample that a replay of the session draws again. -/
def sample {α : Type} [Inhabited α] (xs : Array α) (n : Nat) (seed : Nat) : Array α := Id.run do
  let mut idx := Array.range xs.size
  let mut x : UInt64 := seed.toUInt64 * 0x9E3779B97F4A7C15 + 0x2545F4914F6CDD1D
  for i in [0:min n xs.size] do
    x := x ^^^ (x <<< 13)
    x := x ^^^ (x >>> 7)
    x := x ^^^ (x <<< 17)
    let j := i + (x % (xs.size - i).toUInt64).toNat
    idx := idx.swapIfInBounds i j
  return ((idx.extract 0 (min n xs.size)).qsort (· < ·)).map (xs[·]!)

/-- The variants of goal node `h` that pass filter `f`: how many, and `n` of them, drawn
from `seed`; or, with `byUses`, the `n` whose assertions the most proofs before the
theorem use, the first made first among equals. -/
def select (s : Session) (h : Nat) (f : Filter) (n : Nat) (seed : Nat := 0) (byUses : Bool := false) :
    Except String (Nat × Array Variant) := do
  if !s.isGoal h then throw s!"{h} is not a goal node"
  let passing := s.env.hyps[h]!.children.filter fun p => f.eval (s.env.propView p)
  if byUses then
    let uses (p : Nat) : Nat := s.env.stepUses s.env.props[p]!.step
    let ordered := passing.qsort fun a b => uses a > uses b || uses a == uses b && a < b
    return (passing.size, (ordered.extract 0 n).map s.variant)
  return (passing.size, (sample passing n seed).map s.variant)

/-- The facts of `facts` that pass filter `f` as deductions (`Env.factView?`): how many,
and `n` of them. A fact that is not a deduction, such as a premise, does not pass. -/
def selectFacts (s : Session) (facts : Array Nat) (f : Filter) (n : Nat) (seed : Nat := 0) : Nat × Array Nat :=
  let passing := facts.filter fun g => (s.env.factView? g).any f.eval
  (passing.size, sample passing n seed)

/-- What the DSL needs to read filters and tactics for this session: its database, the
specification if there is one, and the variables of its theorem, `metas` being the
binders marked as metavariables in its task (`Db.task`). -/
def dslCtx (s : Session) (spec : Option Notation := none) (metas : Array Nat := #[]) (rails : Option Rails := none) :
    Dsl.Ctx :=
  let db := s.env.db
  let thm := s.env.task.limit
  { db, spec, thm, vars := fun i => db.binderImage thm metas (db.asserts[thm]!.vars[i]?.getD 0), rails }

/-- The goal nodes that have no proof yet. -/
def openGoals (s : Session) : Array Nat :=
  (Array.range s.env.hyps.size).filter fun h => s.isGoal h && s.env.hyps[h]!.proofs.isEmpty

/-- The statement of a node, as an s-expression. -/
def statement (s : Session) (h : Nat) : String :=
  s.env.db.showExp s.env.hyps[h]!.expr

/-- Why `choose h props` cannot be done, if it cannot. The checks read the session only, so
that a front-end can make them before it gives up its hold on the session's tree. -/
def chooseError? (s : Session) (h : Nat) (props : Array Nat) : Option String := Id.run do
  if !s.isGoal h then return some s!"{h} is not a goal node"
  let children := s.env.hyps[h]!.children
  for p in props do
    if !children.contains p then return some s!"{p} is not a variant of goal node {h}"
    if s.env.props[p]!.expanded then return some s!"variant {p} is expanded already"
  if s.env.overBudget then return some "a join of this tree was cut short: it is missing proofs"
  return none

/-- `choose` without its checks: the assertion nodes `props` expanded, and the proofs that
this makes carried down. -/
def expandAll (s : Session) (props : Array Nat) : IO Session := do
  let { accept, env, rej, found, sid, maxFacts } := s
  let mut env := env
  let mut rej := rej
  let mut found := found
  for p in props do
    let (_, env') ← (proveProp p none).run env
    env := ((← takeHints.run env')).2
    if !env.rootProofs.isEmpty then
      let (f, rej', env') := takeFound accept env rej
      env := env'
      rej := rej'
      found := found <|> f
  return { accept, env, rej, found, sid, maxFacts }

/-- The goal nodes of `nodes` that have no variable and no proof, each closed by every one
of its variants without premises: a step that is not a decision, since such a variant
proves the goal itself, and nothing else. -/
def closeGround (s : Session) (nodes : Array Nat) : IO Session := do
  let mut closers := #[]
  for h in nodes do
    let hyp := s.env.hyps[h]!
    if s.isGoal h && !hyp.expr.hasVars && hyp.proofs.isEmpty then
      closers := closers ++ hyp.children.filter fun p =>
        !s.env.props[p]!.expanded && s.env.props[p]!.rule.hyps.isEmpty
  if closers.isEmpty then return s
  s.expandAll closers

/-- Expands the variants `props` of goal node `h`, in that order, and carries the proofs
that this makes down to the root. The variants that are not chosen stay leaves, which a
strategy may still expand: a choice prunes nothing. With `close`, the new goals without
variables are closed by their variants without premises (`closeGround`). -/
def choose (s : Session) (h : Nat) (props : Array Nat) (close : Bool := false) : IO (Except String Session) := do
  if let some e := s.chooseError? h props then return .error e
  let s ← s.expandAll props
  if !close then return .ok s
  let goals := props.foldl (init := #[]) fun acc p => acc ++ s.env.props[p]!.children
  return .ok (← s.closeGround goals)

/-- The deductions from the facts `chosen`, at least one of which is on the front: for
each chosen fact on the front, every application of an assertion in which it fills a
hypothesis and the chosen facts fill the others (`applyForward` with `fillers`). Each
deduction is a new fact, joined with the goal and the subgoals of the backward tree as
any fact is, every join to its end. The chosen facts stay on the front: the
applications with facts that were not chosen are made when they are expanded without a
restriction. Returns the new facts. -/
def deduceError? (s : Session) (chosen : Array Nat) : Option String := Id.run do
  if s.env.forward.isNone then return some "the session has no forward front"
  for f in chosen do
    if !s.isFact f then return some s!"{f} is not a fact"
  if !(chosen.any s.front.contains) then return some "none of the chosen facts is on the front"
  if s.env.overBudget then return some "a join of this tree was cut short: it is missing proofs"
  return none

def deduce (s : Session) (chosen : Array Nat) : IO (Except String (Session × Array Nat)) := do
  if let some e := s.deduceError? chosen then return .error e
  let triggers := chosen.filter s.front.contains
  let { accept, env, rej, found, sid, maxFacts } := s
  let mut env := env
  let mut made : Array Nat := #[]
  for f in triggers do
    for (id, pos) in forwardTriggers env f do
      let (new, env') ← (applyForward f env.db.asserts[id]! pos maxFacts (some chosen)).run env
      env := env'
      for g in new do
        let (targets, env') ← (joinRoot g).run env
        env := env'
        for h in targets do
          env := ((← (joinSubgoal g h).run env)).2
      made := made ++ new
  env := ((← takeHints.run env)).2
  let (f, rej, env') := takeFound accept env rej
  return .ok ({ accept, env := env', rej, found := found <|> f, sid, maxFacts }, made)

/-- The forward front, for a session that started without it: empty, with the subgoals of
the backward tree recorded for the facts to come, as `expandProp` records each new one
when there is a front. -/
def _root_.Whitehead.Prove.Env.withForward (env : Env) : Env := Id.run do
  if env.forward.isSome then return env
  let mut front := env.backwardFront
  for h in [1:env.hyps.size] do
    if env.hyps[h]!.parent.isSome then front := front.insert env.hyps[h]!.expr h
  return { env with forward := some {}, backwardFront := front }

/-- Offers the intermediate goal `expr` (`offerHint`): a goal node of its own, expanded
like the root, and returned. Every proof it gets, by choices, runs and deductions,
becomes a fact, joined with the goal and the subgoals of the main tree. A session
without a forward front gets an empty one. -/
def goal (s : Session) (expr : Exp) (close : Bool := false) : IO (Except String (Session × Nat)) := do
  if s.env.overBudget then return .error "a join of this tree was cut short: it is missing proofs"
  let { accept, env, rej, found, sid, maxFacts } := s
  let (h, env) ← (offerHint expr).run env.withForward
  let (_, env) ← takeHints.run env
  let (f, rej, env) := takeFound accept env rej
  let s : Session := { accept, env, rej, found := found <|> f, sid, maxFacts }
  return .ok (← if close then s.closeGround #[h] else pure s, h)

/-- `goal` for a statement in the notation of the specification, the inside of
`$ ... $`; a hole `_` is a new metavariable. `metas` are the binders of the theorem
marked as metavariables in its task. -/
def readGoal (s : Session) (spec : Notation) (text : String) (metas : Array Nat := #[]) :
    Except String (Exp × Nat) :=
  let ctx := s.dslCtx (some spec) metas
  (spec.formula ctx.thm ctx.vars text 0 s.env.fresh).mapError (Dsl.ParseError.show text)

def goalText (s : Session) (spec : Notation) (text : String) (metas : Array Nat := #[]) (close : Bool := false) :
    IO (Except String (Session × Nat)) := do
  match s.readGoal spec text metas with
  | .error e => return .error e
  | .ok (expr, holes) =>
    let s := { s with env := { s.env with fresh := s.env.fresh + holes } }
    s.goal expr close

/-- Runs a strategy on the tree as it is, from the strategy's initial state, until it
accepts a proof, has nothing more to do, or reaches a limit. The time is counted from
the start of the run; the number of assertion nodes is that of the whole tree. A join is
always run to its end: one that a budget cut short would keep nothing, and the tree
would be missing proofs for the runs after it. The forward direction is not supported
here yet: a wave that a limit stops leaves the facts it had not expanded off the front.
In a session the forward direction is `deduce`. -/
def runError? {σ : Type} (s : Session) (strategy : Strategy σ) : Option String :=
  if strategy.forward then some "the forward direction is not supported in a session"
  else if s.env.overBudget then some "a join of this tree was cut short: it is missing proofs"
  else none

def run {σ : Type} (s : Session) (strategy : Strategy σ) (limits : Limits) :
    IO (Except String (Session × Ending × Option Stop)) := do
  if let some e := s.runError? strategy then return .error e
  let start ← IO.monoMsNow
  let { accept, env, rej, found, sid, maxFacts } := s
  let env := { env.withLimits strategy limits start with
               tupleBudget := 0xFFFFFFFFFFFF, workBudget := 0xFFFFFFFFFFFF, deadline := 0xFFFFFFFFFFFFFFFF }
  let r ← try searchLoop accept env rej strategy limits start sid
          finally runningSizes.modify (·.erase sid)
  let found := found <|> r.found?
  let stop := r.stop
  let ending := r.ending
  return .ok ({ accept, env := r.env, rej := r.rejections, found, sid, maxFacts }, ending, stop)

end Session

end Whitehead.Prove
