/-
A session: the proof variant tree of one task, kept between the requests of an agent
(`docs/DESIGN.md`, "Phase 4", "The session"). The agent, a human or an AI, sees the goal
nodes (`RuProverExp`, `RuProverRoot`) and their variants (`RuProverProp`). It chooses
variants to expand, and it runs strategies on the tree as it is. The engine does the
rest: unification, the substitutions, and the joins of proofs on the way to the root.
It never asks the agent for a substitution.

Only the backward direction is here. Russell's interactive prover drives its tree in the
same way (`prove-expand`, `prove-candidates` in `russell-flow/src/ru/prover/commands`).
-/
import Whitehead.Prove.Prove

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

namespace Session

/-- A session on the task of `env`: the root is expanded, and nothing else. A goal that is
one of the premises is proved at once. -/
def start (accept : Env → ProofTree → Array Cond → Except String ByteArray) (env : Env) : IO Session := do
  let sid ← nextSearch.modifyGet fun n => (n, n + 1)
  match ← searchStart accept env breadthFirst {} (← IO.monoMsNow) sid with
  | .finished r => return { accept, env := r.env, rej := r.rejections, found := r.found?, sid }
  | .running env rej => return { accept, env, rej, sid }

/-- `start` for a theorem of the file: a proof counts if the verifier accepts its body. -/
def startFor (vc : Verify.Ctx) (env : Env) : IO Session :=
  start (Prove.accept vc) env

def variant (s : Session) (p : Nat) : Variant :=
  let prop := s.env.props[p]!
  let name := match prop.step with
    | .assertion id => s.env.db.asserts[id]!.name
    | .conv t _ unfold => s!"{if unfold then "unfold" else "fold"} {s.env.db.terms[t]!.name}"
  { prop := p, step := prop.step, name, expanded := prop.expanded, goals := prop.children }

/-- Is `h` a goal node of the backward tree: the root, or a premise of an assertion
node? (A fact of the forward front is an expression node too, without a parent.) -/
def isGoal (s : Session) (h : Nat) : Bool :=
  match s.env.hyps[h]? with
  | some hyp => h == 0 || hyp.parent.isSome
  | none => false

/-- The variants of goal node `h`, in the order they were made. -/
def variants (s : Session) (h : Nat) : Except String (Array Variant) :=
  if !s.isGoal h then .error s!"{h} is not a goal node"
  else .ok (s.env.hyps[h]!.children.map s.variant)

/-- The goal nodes that have no proof yet. -/
def openGoals (s : Session) : Array Nat :=
  (Array.range s.env.hyps.size).filter fun h => s.isGoal h && s.env.hyps[h]!.proofs.isEmpty

/-- The statement of a node, as an s-expression. -/
def statement (s : Session) (h : Nat) : String :=
  s.env.db.showExp s.env.hyps[h]!.expr

/-- Expands the variants `props` of goal node `h`, in that order, and carries the proofs
that this makes down to the root. The variants that are not chosen stay leaves, which a
strategy may still expand: a choice prunes nothing. -/
def choose (s : Session) (h : Nat) (props : Array Nat) : IO (Except String Session) := do
  if !s.isGoal h then return .error s!"{h} is not a goal node"
  let children := s.env.hyps[h]!.children
  for p in props do
    if !children.contains p then return .error s!"{p} is not a variant of goal node {h}"
    if s.env.props[p]!.expanded then return .error s!"variant {p} is expanded already"
  if s.env.overBudget then return .error "a join of this tree was cut short: it is missing proofs"
  let { accept, env, rej, found, sid } := s
  let mut env := env
  let mut rej := rej
  let mut found := found
  for p in props do
    let (_, env') ← (proveProp p none).run env
    env := env'
    if !env.rootProofs.isEmpty then
      let (f, rej', env') := takeFound accept env rej
      env := env'
      rej := rej'
      found := found <|> f
  return .ok { accept, env := env.dropExpanded, rej, found, sid }

/-- Runs a strategy on the tree as it is, from the strategy's initial state, until it
accepts a proof, has nothing more to do, or reaches a limit. The time is counted from
the start of the run; the number of assertion nodes is that of the whole tree. A join is
always run to its end: one that a budget cut short would keep nothing, and the tree
would be missing proofs for the runs after it. The forward direction is not supported
here yet. -/
def run {σ : Type} (s : Session) (strategy : Strategy σ) (limits : Limits) :
    IO (Except String (Session × Ending × Option Stop)) := do
  if strategy.forward then return .error "the forward direction is not supported in a session"
  if s.env.overBudget then return .error "a join of this tree was cut short: it is missing proofs"
  let start ← IO.monoMsNow
  let { accept, env, rej, found, sid } := s
  let env := { env.withLimits strategy limits start with
               tupleBudget := 0xFFFFFFFFFFFF, workBudget := 0xFFFFFFFFFFFF, deadline := 0xFFFFFFFFFFFFFFFF }
  let r ← try searchLoop accept env rej strategy limits start sid
          finally runningSizes.modify (·.erase sid)
  let found := found <|> r.found?
  let stop := r.stop
  let ending := r.ending
  return .ok ({ accept, env := r.env, rej := r.rejections, found, sid }, ending, stop)

end Session

end Whitehead.Prove
