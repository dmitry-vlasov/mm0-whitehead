/-
The state of a proof search: a port of `RuProverEnv`
(`russell-flow/src/ru/prover/core/env.flow`), without the parts of the layers that are
not ported yet (fragments, the forward front) and without the replaceable functions
`RuProverFuncs`: what a strategy may restrict is passed to the functions that expand.
-/
import Whitehead.Prove.Tree

namespace Whitehead.Prove

/-- What the expansion of one expression node may use, when a strategy restricts it. -/
inductive Only where
  /-- Only this premise, and no assertion. -/
  | premise (ind : Nat)
  /-- Only this assertion, and no premise. -/
  | assertion (id : Nat)
  deriving Inhabited

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
  duplicate : Nat := 0
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
  (`RuProverTree.leafs`). -/
  leafs : Array Nat := #[]
  /-- The number of the next fresh variable. -/
  fresh : Nat := freshBase
  /-- The proofs that reached the root and have not been taken by the driver yet. -/
  rootProofs : Array Proof := #[]
  counters : Counters := {}
  deriving Inhabited

abbrev ProverM := StateM Env

/-- `ruInitProverEnv`, up to the first expansion of the root. -/
def Env.init (db : Db) (assertions : Index Nat) (task : Task) : Env :=
  { db, task, assertions,
    premises := (Array.range task.premises.size).foldl (init := {}) fun ix k => ix.insert task.premises[k]! k,
    hyps := #[{ ind := 0, expr := task.goal, parent := none }] }

end Whitehead.Prove
