/-
The upward pass: a port of `russell-flow/src/ru/prover/core/expand.flow`, and of
`ruProveProp` from `prove.flow`.

`expandHyp` gives an expression node one assertion node for every assertion whose
conclusion unifies with it. `expandProp` gives an assertion node its expression nodes,
the premises of the assertion under the unifier; each is matched with the premises of
the task and expanded at once. If there is a forward front, each new subgoal is also
recorded for the facts to come, and joined with the facts that are there
(`Forward.lean`). Not ported: the forward closure (`forward_closure.flow`) and the
positional join of the completeness test, which `ruExpandProp` also has.
-/
import Whitehead.Prove.Forward

namespace Whitehead.Prove

/-- A way to expand expression node `h`: the step, its rule, and the unifier of the
rule's conclusion with the expression of the node. -/
structure Candidate where
  step : Step
  rule : Assertion
  /-- The bindings that unify the rule's conclusion with the expression. -/
  binds : Binds

/-- The rule for unfolding (or folding) def `t` at node `pos` of `e`, as an assertion
over variables of its own: the def's arguments `0 .. n-1`, its dummies `n .. n+m-1`, and
the variables of the rest of `e`. To unfold, the conclusion is `e` with `f(xs)` at `pos`
and the premise the same with the value there; to fold, the converse. Unifying the
conclusion with `e` gives the arguments, and for a fold the dummies too; for an unfolding
the dummies stay free and become fresh names, under the condition that each is apart
from the arguments and from the other dummies — what the verifier checks at `Unfold`. -/
def convRule (db : Db) (e : Exp) (t pos : Nat) (unfold : Bool) : Option Assertion := do
  let info := db.terms[t]!
  let v ← info.value
  let n := info.args.size
  let m := v.dummies.size
  let xs := (Array.range n).map fun k => Node.var k info.args[k]!
  let app := Exp.mkApp t info.ty (xs.map Exp.ofVar)
  -- the rest of `e`, its variables renamed from `n + m` on
  let hole : Exp := Exp.ofVar (Node.var 0 (Node.ty e.nodes[pos]!))
  let rest := e.replace pos hole
  let restVars := rest.vars.filter (· != hole.nodes[0]!)
  let renamed := (Array.range restVars.size).foldl (init := ({} : Std.HashMap Nat SubExp)) fun s k =>
    let w := restVars[k]!
    s.insert (Node.varId w) (SubExp.mk' w (Exp.ofVar (Node.var (n + m + k) (Node.ty w))))
  let rename : Subst := { map := renamed }
  let withDef := (rename.apply e).replace pos app
  let withValue := (rename.apply e).replace pos v.expr
  let mut disjs : Array (Nat × Nat) := #[]
  for j in [0:m] do
    for i in [0:n] do disjs := disjs.push (n + j, i)
    for j' in [j + 1:m] do disjs := disjs.push (n + j, n + j')
  return { id := t, name := s!"{if unfold then "unfold" else "fold"} {info.name}", binders := #[],
           vars := xs ++ v.dummies ++ (Array.range restVars.size).map (fun k => Node.var (n + m + k) (Node.ty restVars[k]!)),
           hyps := #[if unfold then withValue else withDef], concl := if unfold then withDef else withValue, disjs }

/-- The unfoldings and foldings that expression `e` has: for every application of a def
in `e`, the unfolding of it; for every application whose term is the head of a def's
value, the folding into that def, if the value unifies there. Only defs declared before
the theorem. -/
def convCandidates (env : Env) (e : Exp) : Array Candidate := Id.run do
  let db := env.db
  let try_ (t pos : Nat) (unfold : Bool) : Option Candidate := do
    let rule ← convRule db e t pos unfold
    -- the conclusion first: of two variables the later is kept, so the rule's are bound
    let sub ← unifyExps #[rule.concl, e] {}
    return { step := .conv t pos unfold, rule, binds := Binds.ofSubst sub }
  let mut out := #[]
  for pos in [0:e.size] do
    let node := e.nodes[pos]!
    if Node.isVar node || Node.isConst node then continue
    let head := Node.appId node
    if head < env.task.terms && (db.terms[head]!.value).isSome then
      if let some c := try_ head pos true then out := out.push c
    for t in db.defs do
      if t < env.task.terms then
        if let some v := db.terms[t]!.value then
          let root := v.expr.nodes[0]!
          if !Node.isVar root && Node.appId root == head then
            if let some c := try_ t pos false then out := out.push c
  return out

/-- The ways to expand expression node `h`: the assertions whose conclusion unifies with
its expression — all that the index finds among those declared before the task's
theorem, or the one that `only` names — and the unfoldings. -/
def candidates (env : Env) (h : Nat) (only : Option Only) : Array Candidate :=
  let e := env.hyps[h]!.expr
  match only with
  | none =>
    (env.assertions.unifyRaw e (rankLimit env.task.limit)).map (fun u =>
      { step := .assertion u.data, rule := env.db.asserts[u.data]!, binds := u.binds })
      ++ (if env.convSteps then convCandidates env e else #[])
  | some (.assertion id) =>
    match unifyExps #[e, env.db.asserts[id]!.concl] {} with
    | some s => #[{ step := .assertion id, rule := env.db.asserts[id]!, binds := Binds.ofSubst s }]
    | none => #[]
  | some (.premise _) => #[]

/-- `ruExpandHyp` -/
def expandHyp (h : Nat) (only : Option Only := none) : ProverM Unit := do
  let env ← get
  -- the candidates that bind more come first; among equals, the order of the index
  let found := candidates env h only
  -- a stable bucket sort by the number of bindings, the most first
  let most := found.foldl (init := 0) fun m c => max m c.binds.size
  let mut buckets : Array (Array Candidate) := Array.replicate (most + 1) #[]
  for c in found do
    buckets := buckets.modify (most - c.binds.size) (·.push c)
  for bucket in buckets do
    for unif in bucket do
      -- a candidate keeps the bindings; they are split when it is expanded (`splitProp`)
      let prop : PropNode := { step := unif.step, rule := unif.rule, parent := h, unif := some unif.binds }
      modify fun env =>
        let p := env.props.size
        { env with props := env.props.push prop, leafs := env.leafs.push p,
                   hyps := env.hyps.modify h fun hyp => { hyp with children := hyp.children.push p },
                   counters := { env.counters with props := env.counters.props + 1 } }

/-- The unifier of candidate `p` split into `sub` and `outer`, the variables of the rule
that it leaves free being given fresh names. Done once, when the node is expanded. -/
def splitProp (p : Nat) : ProverM Unit := do
  let env ← get
  let prop := env.props[p]!
  let some bs := prop.unif | return
  -- the bindings as one idempotent substitution; `none` cannot happen for the bindings
  -- of a walk, which keeps cycles out, and is counted so that a test would see it
  let some u := bs.toSubst
    | set { env with props := env.props.modify p fun prop => { prop with unif := none },
                     counters := { env.counters with badCandidates := env.counters.badCandidates + 1 } }
  let a := prop.rule
  let free := a.vars.filter fun v => !u.maps (Node.varId v)
  let base := env.fresh
  let fresher : Subst :=
    { map := (Array.range free.size).foldl (init := {}) fun m k =>
        let v := free[k]!
        m.insert (Node.varId v) (SubExp.mk' v (Exp.ofVar (Node.var (base + k) (Node.ty v)))) }
  let sAll := u.unsafeCompose fresher
  let isOfAssertion : Nat → Exp → Bool := fun v _ => Node.varId v < freshBase
  set { env with fresh := base + free.size,
                 props := env.props.modify p fun prop =>
                   { prop with sub := sAll.filter (fun v e => !isOfAssertion v e), outer := sAll.filter isOfAssertion,
                               unif := none } }

/-- `ruExpandProp`. `only` restricts, for each premise of the assertion, what its
expression node may use. -/
def expandProp (p : Nat) (only : Option (Array Only) := none) : ProverM Unit := do
  splitProp p
  modify fun env =>
    { env with props := env.props.modify p fun prop => { prop with expanded := true },
               counters := { env.counters with expanded := env.counters.expanded + 1 } }
  let env ← get
  let prop := env.props[p]!
  let a := prop.rule
  if a.hyps.isEmpty then
    -- an assertion without premises is a proof at once, if its conditions on bound
    -- variables allow it
    let visible := (prop.sub.apply env.hyps[prop.parent]!.expr).varIds
    match openConds env prop prop.sub visible #[] with
    | none => modify fun env => { env with counters := { env.counters with disjoint := env.counters.disjoint + 1 } }
    | some conds =>
      modify fun env => { env with props := env.props.modify p fun prop =>
        { prop with proofs := prop.proofs.push (.prop p prop.sub #[] conds) } }
  else
    for i in [0:a.hyps.size] do
      let ex := prop.outer.apply (prop.sub.apply a.hyps[i]!)
      let h := (← get).hyps.size
      modify fun env =>
        { env with hyps := env.hyps.push { ind := i, expr := ex, parent := some p },
                   props := env.props.modify p fun prop => { prop with children := prop.children.push h } }
      -- the premises of the task that this expression unifies with
      let restriction : Option Only := only.map (·[i]!)
      let env ← get
      let unified :=
        match restriction with
        | none => env.premises.unify ex
        | some (.premise k) => (env.premises.unify ex).filter (·.data == k)
        | some (.assertion _) => #[]
      for unif in unified do
        let proof := Proof.top h unif.expr unif.data unif.sub
        modify fun env => { env with hyps := env.hyps.modify h fun hyp => { hyp with proofs := hyp.proofs.push proof } }
        addProof p proof
      -- the join with the forward front: the subgoal is recorded for the facts to come
      -- (`backwardFront`), and the facts that unify with it prove it. The `joinCap`
      -- facts with the smallest proofs are taken (Russell's `fwd_cap`: four).
      if (← get).forward.isSome && restriction.isNone then
        modify fun env => { env with backwardFront := env.backwardFront.insert ex h }
        let env ← get
        let found := ((env.forward.map (·.index.unify ex)).getD #[]).map (·.data)
        let size (f : Nat) : Nat := (env.hyps[f]!.factProof.map (·.size)).getD 0
        let nearest := (found.qsort fun a b => size a < size b || size a == size b && a < b).extract 0 env.joinCap
        for f in nearest do
          if let some (proof, _) ← graft f h ex then
            modify fun env =>
              { env with hyps := env.hyps.modify h fun hyp => { hyp with proofs := hyp.proofs.push proof },
                         counters := { env.counters with joins := env.counters.joins + 1 } }
            addProof p proof
      expandHyp h restriction

/-- `ruProveProp`: expands an assertion node, and carries the proofs that this gives it
down the tree. -/
def proveProp (p : Nat) (only : Option (Array Only) := none) : ProverM Unit := do
  expandProp p only
  buildPropProofs p (← get).props[p]!.proofs

end Whitehead.Prove
