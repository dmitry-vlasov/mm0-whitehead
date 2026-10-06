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

An unfolding step (`ProofTree.conv`) is `Conv` with the conversion proof written from
the path: `Cong` at each application on the way, `Refl` for the arguments beside the
path, and at the end `Unfold` (after `Symm` for a fold) with the value pushed first,
then `Refl`. `Refl` and `Unfold` need the same node on both sides, which the sharing
above gives: everything beside the path is asked for twice, by both statements.

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
  /-- The premises of the task: what `ProofTree.hyp` proves. -/
  premises : Array Exp
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

/-- What a proof proves. -/
partial def ProofTree.concl (db : Db) (premises : Array Exp) : ProofTree → Exp
  | .hyp i => premises[i]!
  | .step a args _ => stepConcl db a args
  | .conv t path unfold args dummies child =>
    let c := child.concl db premises
    match c.nodeAt path with
    | some pos => c.replace pos (if unfold then Exp.mkApp t db.terms[t]!.ty args else db.unfolded t args dummies)
    | none => c

/-- The conversion proof for an unfolding at `path`, the obligation `e1 =?= e2` being on
the stack; `i1` and `i2` are where the path has got to in each. -/
partial def emitConv (e1 e2 : Exp) (path : Array Nat) (unfold : Bool) (k i1 i2 : Nat) : EmitM Unit := do
  let push (c : ProofCmd) : EmitM Unit := modify fun st => { st with cmds := st.cmds.push c }
  if k == path.size then
    -- `f(args) =?= value` for an unfolding, the converse for a fold
    if !unfold then push .symm
    emitExpr (if unfold then e2 else e1) (if unfold then i2 else i1)
    push .unfold
    push .refl
  else
    push .cong
    let a1 := e1.argStarts i1
    let a2 := e2.argStarts i2
    for j in [0:a1.size] do
      if j == path[k]! then emitConv e1 e2 path unfold (k + 1) a1[j]! a2[j]!
      else push .refl

/-- Asks for a proof. -/
partial def emitProof (t : ProofTree) : EmitM Unit := do
  match t with
  | .hyp i => modify fun st => { st with cmds := st.cmds.push (.ref (st.hypAt[i]?.getD 0)) }
  | .step assertion args children =>
    let st ← get
    let concl := stepConcl st.db assertion args
    proof concl (body args children concl) (fun save => some (.thm assertion save))
  | .conv _ path unfold _ _ child =>
    let st ← get
    let e1 := t.concl st.db st.premises
    let e2 := child.concl st.db st.premises
    proof e1 (do
      emitExpr e1 0
      emitProof child
      modify fun st => { st with cmds := st.cmds.push .conv }
      emitConv e1 e2 path unfold 0 0 0) (fun save => if save then some .save else none)
where
  body (args : Array Exp) (children : Array ProofTree) (concl : Exp) : EmitM Unit := do
    for c in children do emitProof c
    for a in args do emitExpr a 0
    emitExpr concl 0
  /-- A proof of `concl` made by `make`, shared by what it proves: counted the first
  time, referred to afterwards. `finish save` is the command that completes it and
  saves it if asked: `Thm` for a step; for an unfolding, which `make` completes, `Save`
  or nothing. -/
  proof (concl : Exp) (make : EmitM Unit) (finish : Bool → Option ProofCmd) : EmitM Unit := do
    let st ← get
    if st.counting then
      if st.proofMade.contains concl then
        set { st with proofRefs := st.proofRefs.insert concl (st.proofRefs.getD concl 0 + 1) }
      else
        make
        modify fun st => { st with proofMade := st.proofMade.insert concl }
    else
      match st.proofAt[concl]? with
      | some at_ => set { st with cmds := st.cmds.push (.ref at_) }
      | none =>
        make
        let save := (st.proofRefs.getD concl 0) > 0
        modify fun st =>
          let st := match finish save with
            | some c => { st with cmds := st.cmds.push c }
            | none => st
          if save then { st with proofAt := st.proofAt.insert concl st.heap, heap := st.heap + 1 } else st

/-- Everything that is asked for, in order: the hypotheses, then the proof. -/
def plan (task : Task) (proof : ProofTree) : EmitM Unit := do
  for premise in task.premises do
    emitExpr premise 0
    modify fun st => { st with cmds := st.cmds.push .hyp, hypAt := st.hypAt.push st.heap, heap := st.heap + 1 }
  emitProof proof

/-- The proof body for `proof` of the task: the commands, without the `END`. `none` if a
variable that is not a name is left in the proof. -/
def emitBody (db : Db) (task : Task) (proof : ProofTree) : Option (Array ProofCmd) :=
  let (_, counted) := (plan task proof).run { db, premises := task.premises, counting := true, heap := task.consts.size }
  if counted.bad then none
  else
    let (_, st) := (plan task proof).run
      { db, premises := task.premises, counting := false, heap := task.consts.size,
        exprUses := counted.exprUses, proofRefs := counted.proofRefs }
    some st.cmds

end Whitehead.Prove
