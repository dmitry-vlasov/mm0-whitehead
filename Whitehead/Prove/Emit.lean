/-
A proof found by the prover as the proof body of a theorem in the `.mmb` format
(`docs/MMB-NOTES.md`, sections 5 and 6).

The format compares expressions by identity: where the statement of an applied theorem
mentions a binder twice, the proof must give the same node twice. So every expression
is built once here, saved if it is needed again, and referred to afterwards; then equal
expressions are the same node everywhere. Subproofs are shared in the same way, by what
they prove, as `ruMakeLinearProof` (`russell-flow/src/ru/proof_tree.flow`) shares the
steps with the same statement.

The body is: for each hypothesis of the theorem its expression and `Hyp`; then the
proof, each step as the proofs of its premises, the expressions for all binders of the
assertion, the conclusion, and `Thm`. A variable that is left in the proof must be a
name, and becomes a `Dummy`.

The order in which things are asked for is fixed by `plan`; it runs twice, first to
count how often each expression and each subproof is asked for, then to write the
commands, saving what is asked for again.
-/
import Whitehead.Mmb.Encode
import Whitehead.Prove.Tree

namespace Whitehead.Prove

open Whitehead.Mmb

structure Emitter where
  db : Db
  /-- The first run only counts. -/
  counting : Bool
  /-- How often an expression is asked for. -/
  exprUses : Std.HashMap Exp Nat := {}
  /-- How often a proof of an expression is asked for after one has been made. A step
  can prove what a step below it proves already, so "made" is recorded when the step is
  complete, not when it is first asked for. -/
  proofRefs : Std.HashMap Exp Nat := {}
  proofMade : Std.HashSet Exp := {}
  /-- The heap entry of a saved expression, of a dummy, of a saved proof by what it
  proves, and of each hypothesis. -/
  exprAt : Std.HashMap Exp Nat := {}
  proofAt : Std.HashMap Exp Nat := {}
  hypAt : Array Nat := #[]
  heap : Nat
  cmds : Array ProofCmd := #[]
  /-- A variable that is not a name was left in the proof. -/
  bad : Bool := false

abbrev EmitM := StateM Emitter

/-- Asks for the subexpression of `e` that starts at node `i`: it is built, or referred
to if it was built before. -/
partial def emitExpr (e : Exp) (i : Nat) : EmitM Unit := do
  let n := e.nodes[i]!
  if Node.isConst n then
    -- a binder of the theorem: the heap starts with them
    modify fun st => { st with cmds := st.cmds.push (.ref (Node.appId n - Node.constBase)) }
    return
  let sub := e.sub i
  let st ← get
  if st.counting then
    let uses := st.exprUses.getD sub 0
    set { st with exprUses := st.exprUses.insert sub (uses + 1), bad := st.bad || Node.isVar n && !Ty.isName (Node.ty n) }
    if uses == 0 && !Node.isVar n then
      args
  else
    match st.exprAt[sub]? with
    | some at_ => set { st with cmds := st.cmds.push (.ref at_) }
    | none =>
      if Node.isVar n then
        -- a name that nothing determined: a dummy, which is saved by its command
        set { st with cmds := st.cmds.push (.dummy (Ty.sort (Node.ty n))), exprAt := st.exprAt.insert sub st.heap,
                      heap := st.heap + 1 }
      else
        args
        let save := (st.exprUses.getD sub 0) > 1
        modify fun st =>
          let st := { st with cmds := st.cmds.push (.term (Node.appId n) save) }
          if save then { st with exprAt := st.exprAt.insert sub st.heap, heap := st.heap + 1 } else st
where
  /-- The arguments of the application at `i`, in order. -/
  args : EmitM Unit := do
    let stop := i + 1 + Node.len e.nodes[i]!
    let mut j := i + 1
    while j < stop do
      emitExpr e j
      j := j + 1 + Node.len e.nodes[j]!

/-- The conclusion of a step: that of its assertion, with the expressions of the step
for its binders. -/
def stepConcl (db : Db) (assertion : Nat) (args : Array Exp) : Exp :=
  let a := db.asserts[assertion]!
  let map : Std.HashMap Nat SubExp := (Array.range a.vars.size).foldl (init := {}) fun m k =>
    m.insert k (SubExp.mk' a.vars[k]! args[k]!)
  ({ map } : Subst).apply a.concl

/-- Asks for a proof. -/
partial def emitProof (t : ProofTree) : EmitM Unit := do
  match t with
  | .hyp i => modify fun st => { st with cmds := st.cmds.push (.ref (st.hypAt[i]?.getD 0)) }
  | .step assertion args children =>
    let st ← get
    let concl := stepConcl st.db assertion args
    if st.counting then
      if st.proofMade.contains concl then
        set { st with proofRefs := st.proofRefs.insert concl (st.proofRefs.getD concl 0 + 1) }
      else
        body args children concl
        modify fun st => { st with proofMade := st.proofMade.insert concl }
    else
      match st.proofAt[concl]? with
      | some at_ => set { st with cmds := st.cmds.push (.ref at_) }
      | none =>
        body args children concl
        let save := (st.proofRefs.getD concl 0) > 0
        modify fun st =>
          let st := { st with cmds := st.cmds.push (.thm assertion save) }
          if save then { st with proofAt := st.proofAt.insert concl st.heap, heap := st.heap + 1 } else st
where
  body (args : Array Exp) (children : Array ProofTree) (concl : Exp) : EmitM Unit := do
    for c in children do emitProof c
    for a in args do emitExpr a 0
    emitExpr concl 0

/-- Everything that is asked for, in order: the hypotheses, then the proof. -/
def plan (task : Task) (proof : ProofTree) : EmitM Unit := do
  for premise in task.premises do
    emitExpr premise 0
    modify fun st => { st with cmds := st.cmds.push .hyp, hypAt := st.hypAt.push st.heap, heap := st.heap + 1 }
  emitProof proof

/-- The proof body for `proof` of the task: the commands, without the `END`. `none` if a
variable that is not a name is left in the proof. -/
def emitBody (db : Db) (task : Task) (proof : ProofTree) : Option (Array ProofCmd) :=
  let (_, counted) := (plan task proof).run { db, counting := true, heap := task.consts.size }
  if counted.bad then none
  else
    let (_, st) := (plan task proof).run
      { db, counting := false, heap := task.consts.size, exprUses := counted.exprUses, proofRefs := counted.proofRefs }
    some st.cmds

end Whitehead.Prove
