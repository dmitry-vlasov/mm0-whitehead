/-
The state of a proof search: a port of `RuProverEnv`
(`russell-flow/src/ru/prover/core/env.flow`), without the parts of the layers that are
not ported (fragments) and without the replaceable functions `RuProverFuncs`: what a
strategy may restrict is passed to the functions that expand.
-/
import Whitehead.Prove.Tree
import Whitehead.Prove.Uses

namespace Whitehead.Prove

/-- What the expansion of one expression node may use, when a strategy restricts it. -/
inductive Only where
  /-- Only this premise, and no assertion. -/
  | premise (ind : Nat)
  /-- Only this assertion, and no premise. -/
  | assertion (id : Nat)
  deriving Inhabited

/-- The restriction of an expansion to the step of a known proof. -/
def Skeleton.only : Skeleton → Only
  | .step t _ => .assertion t
  | .hyp k => .premise k

/-- Who expanded an assertion node: the label that the search loop or the session
writes on it, for the costs to read (`Cost.lean`; `docs/DESIGN.md`, "Composable
tactics"). Atoms share no state: what one did, another reads off the tree. -/
inductive Label where
  /-- A search: `bfs`, `search`, and a strategy that does not say. -/
  | search
  /-- A guide followed: `follow`, a subproof replayed. -/
  | follow
  /-- An agent's choice in a session (`Session.choose`). -/
  | choose
  deriving BEq, Hashable, Inhabited, Repr

/-- Counters of the engine's work, for reports. -/
structure Counters where
  /-- Assertion nodes made and expanded. -/
  props : Nat := 0
  expanded : Nat := 0
  /-- Tuples of proofs tried in `addProof`, and how they ended. -/
  tuples : Nat := 0
  notUnified : Nat := 0
  disjoint : Nat := 0
  inconsistent : Nat := 0
  /-- Proofs of an assertion node not kept: one with the same key is there (`proofKey`). -/
  duplicate : Nat := 0
  /-- The proofs that joins looked at: the work of `addProof`. -/
  work : Nat := 0
  /-- Candidates whose bindings did not make a substitution (`splitProp`): never, unless
  the walk of the index is wrong. -/
  badCandidates : Nat := 0
  /-- Facts made by the forward direction, and joins of a fact with a subgoal or the
  root. -/
  facts : Nat := 0
  joins : Nat := 0
  deriving Inhabited

/-- The limit that ended a search: its time, its number of assertion nodes, the tuples
of proofs joined, the proofs looked at by the joins, or the memory of the process. A
run in rounds asks which, since only a limit that grows is worth trying again. -/
inductive Stop where
  | time
  | nodes
  | tuples
  | work
  | memory
  deriving BEq, Inhabited, Repr

/-- `RuProverForward`: the forward front. Its facts are expression nodes of the tree. -/
structure Forward where
  /-- The facts by their expression. -/
  index : Index Nat := {}
  /-- The facts that have not been expanded forward yet. -/
  front : Array Nat := #[]
  /-- The number of facts. -/
  count : Nat := 0
  /-- The applications that have been made: the assertion, and the fact for each of its
  hypotheses. The same application is not made again (`applyForward`). -/
  applied : Std.HashSet (Array Nat) := {}
  /-- The facts made from the proofs of intermediate goals. A new subgoal is joined with
  every one of them that unifies with it, whatever `joinCap` says. -/
  hintFacts : Array Nat := #[]
  deriving Inhabited

structure Env where
  db : Db
  task : Task
  /-- The conclusions of all assertions; only those before `task.limit` are used. -/
  assertions : Index Nat
  /-- The premises of the task, by their number. -/
  premises : Index Nat
  /-- Expression nodes; node 0 is the root. -/
  hyps : Array HypNode
  props : Array PropNode := #[]
  /-- The assertion nodes not expanded yet, in the order they were made
  (`RuProverTree.leafs`). A node that is expanded stays in the list until the end of the
  round (`Env.dropExpanded`): taking each one out when it is expanded would be a pass
  over the whole list for every node. -/
  leafs : Array Nat := #[]
  /-- The assertion nodes expanded, in the order they were, each with who expanded it. -/
  labels : Array (Nat × Label) := #[]
  /-- The hypotheses of the assertions, for the forward direction. -/
  hypIndexes : HypIndexes := {}
  /-- The forward front, once a strategy has asked for it. -/
  forward : Option Forward := none
  /-- `RuProverEnv.backwardFront`: the subgoals of the backward tree by their expression,
  filled while there is a forward front, so that a new fact can find the subgoals it
  proves. -/
  backwardFront : Index Nat := {}
  /-- `RuProverEnv.admitJoin`: whether a new fact (first) is joined with a subgoal
  (second) that it unifies with. A strategy sets it; the engine only asks. -/
  admitJoin : Exp → Exp → Bool := fun _ _ => true
  /-- Whether an expression node is also expanded by the (def, occurrence) steps
  (`convCandidates`). Off in the differential test against the reference engine, which
  has the conversion judgment as assertions only (`docs/THEORY.md`, decision 12). -/
  convSteps : Bool := true
  /-- The number of the next fresh variable. -/
  fresh : Nat := freshBase
  /-- The proofs that reached the root and have not been taken by the driver yet. -/
  rootProofs : Array Proof := #[]
  /-- How often the assertions are used in the proofs of the file, for the rank of
  variants (`Uses.lean`); empty unless a front-end gives it. Shared, and only read. -/
  uses : Uses := {}
  /-- The goal nodes of the intermediate goals, in the order they were offered: nodes
  without a parent, expanded backward like the root (`offerHint`). -/
  hints : Array Nat := #[]
  /-- The proofs that reached the goal node of an intermediate goal and have not been
  made facts yet (`takeHints`). -/
  hintProofs : Array Proof := #[]
  counters : Counters := {}
  /-- The largest number of tuples of proofs that unify — proofs to be made — that
  `addProof` may join in the whole search. When a join would go past it, nothing of it
  is kept and `overBudget` is set:
  the search stops there and says so (`Ending.limit`). A resource limit, not a choice of
  variants: no variant is dropped while the search goes on. -/
  tupleBudget : Nat := 0xFFFFFFFFFFFF
  /-- The largest work of the joins (`Counters.work`); past it, as past `tupleBudget`. -/
  workBudget : Nat := 0xFFFFFFFFFFFF
  /-- How many facts of the forward front a new subgoal is joined with when it is made
  (`Limits.joinCap`, `fwd_cap`). -/
  joinCap : Nat := 4
  /-- When the search must stop, by the monotonic clock in milliseconds. -/
  deadline : Nat := 0xFFFFFFFFFFFFFFFF
  overBudget : Bool := false
  /-- What stopped a join (`overBudget`). -/
  stop : Option Stop := none
  deriving Inhabited

/-- The leaves without those that have been expanded. -/
def Env.dropExpanded (env : Env) : Env :=
  let props := env.props
  { env with leafs := env.leafs.filter fun p => !props[p]!.expanded }

/-- How short memory is (`watchMemory` in `Replay.lean`): 0 not at all, 1 the largest
running search gives up, 2 every running search gives up. -/
initialize memoryLevel : IO.Ref Nat ← IO.mkRef 0

/-- The engine's monad: the state of the search, and the clock — a join can run long, and
must stop when its theorem's time is up (`Env.deadline`). -/
abbrev ProverM := StateT Env BaseIO

/-- `ruInitProverEnv`, up to the first expansion of the root. The first fresh variables
are the metavariables of the task. -/
def Env.init (db : Db) (assertions : Index Nat) (task : Task) (hypIndexes : HypIndexes := {}) : Env :=
  { db, task, assertions, hypIndexes, fresh := freshBase + task.metas.size,
    premises := (Array.range task.premises.size).foldl (init := {}) fun ix k => ix.insert task.premises[k]! k,
    hyps := #[{ ind := 0, expr := task.goal, parent := none }] }

end Whitehead.Prove
