/-
The state of a proof search: a port of `RuProverEnv`
(`russell-flow/src/ru/prover/core/env.flow`), without the parts of the layers that are
not ported (fragments) and without the replaceable functions `RuProverFuncs`: what a
strategy may restrict is passed to the functions that expand.
-/
import Whitehead.Prove.Tree

namespace Whitehead.Prove

/-- What the expansion of one expression node may use, when a strategy restricts it. -/
inductive Only where
  /-- Only this premise, and no assertion. -/
  | premise (ind : Nat)
  /-- Only this assertion, and no premise. -/
  | assertion (id : Nat)
  /-- Only this unfolding: def `term` unfolded (or folded) at `path` of the expression. -/
  | conv (term : Nat) (path : Array Nat) (unfold : Bool)
  deriving Inhabited

/-- The restriction of an expansion to the step of a known proof. -/
def Skeleton.only : Skeleton → Only
  | .step t _ => .assertion t
  | .hyp k => .premise k
  | .conv t path unfold _ => .conv t path unfold

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
  /-- Facts made by the forward direction, and joins of a fact with a subgoal or the
  root. -/
  facts : Nat := 0
  joins : Nat := 0
  deriving Inhabited

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
  /-- The number of the next fresh variable. -/
  fresh : Nat := freshBase
  /-- The proofs that reached the root and have not been taken by the driver yet. -/
  rootProofs : Array Proof := #[]
  counters : Counters := {}
  /-- The largest number of tuples of proofs that `addProof` may join in the whole
  search. When a join would go past it, nothing of it is done and `overBudget` is set:
  the search stops there and says so (`Ending.limit`). A resource limit, not a choice of
  variants: no variant is dropped while the search goes on. -/
  tupleBudget : Nat := 0xFFFFFFFFFFFF
  overBudget : Bool := false
  deriving Inhabited

/-- The leaves without those that have been expanded. -/
def Env.dropExpanded (env : Env) : Env :=
  let props := env.props
  { env with leafs := env.leafs.filter fun p => !props[p]!.expanded }

abbrev ProverM := StateM Env

/-- `ruInitProverEnv`, up to the first expansion of the root. The first fresh variables
are the metavariables of the task. -/
def Env.init (db : Db) (assertions : Index Nat) (task : Task) (hypIndexes : HypIndexes := {}) : Env :=
  { db, task, assertions, hypIndexes, fresh := freshBase + task.metas.size,
    premises := (Array.range task.premises.size).foldl (init := {}) fun ix k => ix.insert task.premises[k]! k,
    hyps := #[{ ind := 0, expr := task.goal, parent := none }] }

end Whitehead.Prove
