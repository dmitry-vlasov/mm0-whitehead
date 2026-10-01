/-
The forward direction: a port of `russell-flow/src/ru/prover/core/forward.flow`.

It is the mirror of `expandHyp`. `expandHyp` unifies a goal with the conclusions of the
assertions and makes their hypotheses subgoals; `expandForward` unifies a fact with the
hypotheses of the assertions and makes their conclusions facts. A fact is an expression
node of the tree with a proof on it (`RuProverExp` with the sentinel parent); the
assertion node that produced it and the nodes of its hypotheses are ordinary nodes, and
the proofs are joined by the same `addProof`.

The two directions meet in a join: a fact that unifies with a subgoal of the backward
tree proves it (`reverseJoin`, and the splice in `expandProp`), and a fact that the goal
is an instance of proves the goal.

Ported: `ruSeedForwardFront` (the premises and the assertions without hypotheses as
facts), `ruApplyForward`, `ruApplyForwardOn` for an assertion without hypotheses,
`ruExpandForwardProved`, `ruReverseJoin`, `ruFwdRegister`. The loops over the facts of a
wave, over the applications of a fact and over the subgoals that a new fact is joined
with are in `Prove.lean` (`forwardWave`), where the clock is: these functions are what
the loops do at each turn. Not ported: the seed hooks of the tactic layer, the
ordered wave, the positional join of the completeness test (`pathIndex`), and
`forward_closure.flow`.

What differs from Russell:

- **A fact is used with fresh variables.** A fact with variables is a lemma, and each use
  of it gets its own copy of them (`freshCopy`), as each use of an assertion does. In
  Russell the variables of a fact are the same in every use, so one fact cannot fill two
  hypotheses of an assertion in two different instances: `ruUnifySubs` then has to make
  the two instances equal.
- **Facts are told apart up to the names of their variables** (`factKey`); Russell's
  `seen` has the nodes as they are, so the same fact derived twice is two facts.
- **No acyclicity check.** `ruJoinAcyclic` guards against a fact whose derivation depends
  on the subgoal it is joined with. Facts here are derived from the premises and from
  assertions without hypotheses only, never from a subgoal, so there is nothing to
  check; the source says the same of its own check ("premise-grounded, so this always
  holds").
- **The proof of a fact is read off once**, when the fact is made, and kept with it.
  Russell calls `ruMakeProofTree` at every use.
- Seeding stops at the limit of facts; Russell seeds every assertion without hypotheses
  in scope and then finds the front over its limit, so that no wave runs.
- One application is held to the room that the front has left (`applyForward`). In
  Russell the limit is looked at between applications only.
-/
import Whitehead.Prove.Proofs

namespace Whitehead.Prove

/-- The expression with its variables numbered in the order of their first occurrence:
the same for two expressions that differ only in the names of their variables. -/
def factKey (e : Exp) : Exp := Id.run do
  let mut seen : Array Nat := #[]
  let mut out : Array Nat := Array.mkEmpty e.size
  for n in e.nodes do
    if Node.isVar n then
      match seen.findIdx? (· == n) with
      | some k => out := out.push (Node.var k (Node.ty n))
      | none =>
        out := out.push (Node.var seen.size (Node.ty n))
        seen := seen.push n
    else out := out.push n
  return ⟨out⟩

/-- A condition under a substitution. -/
def Cond.subst (s : Subst) (c : Cond) : Cond :=
  ⟨(s.apply ⟨#[c.name]⟩).nodes[0]!, s.apply c.expr⟩

/-- Fact `f` with new variables: its expression, its proof, and the conditions on bound
variables that its proof left open. -/
def freshCopy (f : Nat) : ProverM (Exp × ProofTree × Array Cond) := do
  let env ← get
  let node := env.hyps[f]!
  let tree := node.factProof.getD (.hyp 0)
  let conds := (node.proofs[0]?.map (·.conds)).getD #[]
  let mut vars := tree.vars node.expr.vars
  for c in conds do
    for n in (#[c.name] ++ c.expr.nodes) do
      if Node.isVar n && !vars.contains n then vars := vars.push n
  if vars.isEmpty then return (node.expr, tree, conds)
  let base := env.fresh
  let map : Std.HashMap Nat SubExp := (Array.range vars.size).foldl (init := {}) fun m k =>
    let v := vars[k]!
    m.insert (Node.varId v) (SubExp.mk' v (Exp.ofVar (Node.var (base + k) (Node.ty v))))
  let toFresh : Subst := { map }
  set { env with fresh := base + vars.size }
  return (toFresh.apply node.expr, tree.subst toFresh, conds.map (·.subst toFresh))

/-- `RuProverProofForward`: fact `f` as a proof of expression node `h`, whose expression
is `pattern` under `pre`. `none` if the fact does not unify with it. Returns the proof,
and `pre` followed by the unifier. -/
def graft (f h : Nat) (pattern : Exp) (pre : Subst := {}) : ProverM (Option (Proof × Subst)) := do
  let (e, tree, conds) ← freshCopy f
  let target := pre.apply pattern
  match unifyExps #[target, e] {} with
  | none => return none
  | some s =>
    let full := pre.unsafeCompose s
    return some (.forward h (s.apply target) (restrict full pattern) (tree.subst s) (conds.map (·.subst s)), full)

/-- `ruFwdRegister`: a new fact with the expression `expr`, and the proof that `proof`
makes for the number of its node. `none` if the fact is known. -/
def addFact (expr : Exp) (proof : Nat → Proof) (children : Array Nat) : ProverM (Option Nat) := do
  let env ← get
  let some fwd := env.forward | return none
  let key := factKey expr
  if fwd.seen.contains key then return none
  let f := env.hyps.size
  let tree := makeProofTree env (proof f)
  set { env with
    hyps := env.hyps.push { ind := 0, expr, parent := none, children, proofs := #[proof f], factProof := some tree },
    forward := some { index := fwd.index.insert expr f, front := fwd.front.push f, seen := fwd.seen.insert key,
                      count := fwd.count + 1 },
    counters := { env.counters with facts := env.counters.facts + 1 } }
  return some f

/-- `ruReverseJoin`, the first part: the new fact `f` proves the goal if the goal is an
instance of it. Only the variables of the fact are bound, so that what is proved is the
goal itself. Returns the subgoals of the backward tree that the fact unifies with and
that the strategy admits: the second part, `joinSubgoal`, is done for each. (Russell has
both in one function; here the search loop looks at the clock in between, because a
fact can unify with thousands of subgoals.) -/
def joinRoot (f : Nat) : ProverM (Array Nat) := do
  let (e, tree, conds) ← freshCopy f
  let env ← get
  if let some s := matchExp env.task.goal e then
    -- the conditions that the fact carries, now that its variables are those of the goal
    let conds := conds.map (·.subst s)
    let violated := conds.any fun c =>
      match judge env.task {} ⟨#[c.name]⟩ c.expr with
      | .violated => true
      | _ => false
    if violated then
      modify fun env => { env with counters := { env.counters with disjoint := env.counters.disjoint + 1 } }
    else
      let proof := Proof.forward 0 env.task.goal {} (tree.subst s) conds
      modify fun env =>
        { env with rootProofs := env.rootProofs.push proof,
                   counters := { env.counters with joins := env.counters.joins + 1 } }
  let env ← get
  return ((env.backwardFront.unify env.hyps[f]!.expr).map (·.data)).filter fun h =>
    env.admitJoin env.hyps[f]!.expr env.hyps[h]!.expr

/-- `ruReverseJoin`, the second part: the fact `f` as a proof of the subgoal `h`, put on
the subgoal and carried down the tree. -/
def joinSubgoal (f h : Nat) : ProverM Unit := do
  let env ← get
  let some p := env.hyps[h]!.parent | return
  if let some (proof, _) ← graft f h env.hyps[h]!.expr then
    let before := (← get).props[p]!.proofs.size
    modify fun env =>
      { env with hyps := env.hyps.modify h fun hyp => { hyp with proofs := hyp.proofs.push proof },
                 counters := { env.counters with joins := env.counters.joins + 1 } }
    addProof p proof
    let all := (← get).props[p]!.proofs
    buildPropProofs p (all.extract before all.size)

/-- The variables of an assertion replaced by fresh ones. -/
def freshVars (a : Assertion) : ProverM Subst := do
  let base := (← get).fresh
  modify fun env => { env with fresh := base + a.vars.size }
  let map : Std.HashMap Nat SubExp := (Array.range a.vars.size).foldl (init := {}) fun m k =>
    let v := a.vars[k]!
    m.insert (Node.varId v) (SubExp.mk' v (Exp.ofVar (Node.var (base + k) (Node.ty v))))
  return { map }

/-- `ruApplyForwardOn` for an assertion without hypotheses: its conclusion, with fresh
variables, is a fact. -/
def applyNoHyps (a : Assertion) : ProverM (Option Nat) := do
  let fresh ← freshVars a
  let conc := fresh.apply a.concl
  let env ← get
  let cnode := env.hyps.size
  let p := env.props.size
  let prop : PropNode := { assertion := a.id, sub := {}, outer := fresh, parent := cnode, expanded := true }
  match openConds env prop {} conc.varIds #[] with
  | none => return none
  | some conds =>
    let proof := Proof.prop p {} #[] conds
    set { env with hyps := env.hyps.push { ind := 0, expr := conc, parent := none, children := #[p] },
                   props := env.props.push { prop with proofs := #[proof] } }
    addFact conc (fun f => .stmt f conc {} proof) #[p]

/-- `ruApplyForward`: one application of assertion `a`, in which the fact `fact` is its
hypothesis number `trig`. The other hypotheses are filled from the front, each with
every fact that unifies with it under what the trigger has fixed. `addProof` joins them
as it does in the backward tree, and every proof it makes is a new fact. Returns the
new facts; they are joined with the backward tree by the caller.

The front has room for `maxFacts` facts. An application cannot make more facts than
there is room for, so it takes no more candidates for a hypothesis, and no more of the
tuples that unify. This is a limit on work, like the limit on the front itself: without
it one assertion with two hypotheses that the trigger leaves open is the square of the
front. -/
def applyForward (fact : Nat) (a : Assertion) (trig : Nat) (maxFacts : Nat) : ProverM (Array Nat) := do
  let room := maxFacts - (((← get).forward.map (·.count)).getD 0)
  if room == 0 then return #[]
  let fresh ← freshVars a
  let hyps := a.hyps.map fresh.apply
  let concTmpl := fresh.apply a.concl
  -- the node of the conclusion, the assertion node on it, and a node for each hypothesis
  let env ← get
  let cnode := env.hyps.size
  let p := env.props.size
  let first := cnode + 1
  let hypNodes : Array HypNode := (Array.range hyps.size).map fun j => { ind := j, expr := hyps[j]!, parent := some p }
  set { env with
    hyps := (env.hyps.push { ind := 0, expr := concTmpl, parent := none, children := #[p] }) ++ hypNodes,
    props := env.props.push { assertion := a.id, sub := {}, outer := fresh, parent := cnode,
                              children := (Array.range hyps.size).map (first + ·), expanded := true },
    counters := { env.counters with props := env.counters.props + 1 } }
  let some (trigProof, sigma) ← graft fact (first + trig) hyps[trig]! | return #[]
  for j in [0:hyps.size] do
    if j != trig then
      let some fwd := (← get).forward | return #[]
      let found := ((fwd.index.unify (sigma.apply hyps[j]!)).map (·.data)).extract 0 room
      for g in found do
        if let some (proof, _) ← graft g (first + j) hyps[j]! sigma then
          modify fun env =>
            { env with hyps := env.hyps.modify (first + j) fun hyp => { hyp with proofs := hyp.proofs.push proof } }
  modify fun env =>
    { env with hyps := env.hyps.modify (first + trig) fun hyp => { hyp with proofs := hyp.proofs.push trigProof } }
  addProof p trigProof room
  let mut made := #[]
  for pp in (← get).props[p]!.proofs do
    if (((← get).forward.map (·.count)).getD 0) ≥ maxFacts then break
    let conc := pp.sub.apply concTmpl
    if let some f ← addFact conc (fun f => .stmt f conc (restrict pp.sub concTmpl) pp) #[p] then
      made := made.push f
  return made

/-- `ruExpandForwardProved`, the choice: the applications of an assertion in which the
fact can be one of the hypotheses, as the assertion and the position of the hypothesis.
`applyForward` does each. -/
def forwardTriggers (env : Env) (fact : Nat) : Array (Nat × Nat) :=
  let expr := env.hyps[fact]!.expr
  let single := (env.hypIndexes.single.unify expr {} env.task.limit).map fun u => (u.data, 0)
  let multi := (env.hypIndexes.multi.unify expr {} env.task.limit).map (·.data)
  single ++ multi

/-- `ruSeedForwardFront`: the front at the start. The premises of the task are facts,
and so are the assertions without hypotheses that precede the theorem, which no wave
would reach (a wave applies an assertion when a fact fits one of its hypotheses). The
seeds are then joined with the goal. It must run before the root is expanded, so that
the subgoals are recorded for the joins. Returns the seeds. -/
def seedForward (maxFacts : Nat) : ProverM (Array Nat) := do
  if (← get).forward.isSome then return #[]
  modify fun env => { env with forward := some {} }
  let env ← get
  let mut seeds : Array Nat := #[]
  for k in [0:env.task.premises.size] do
    let premise := env.task.premises[k]!
    if let some f ← addFact premise (fun f => .top f premise k {}) #[] then seeds := seeds.push f
  for id in [0:env.task.limit] do
    let a := env.db.asserts[id]!
    if a.hyps.isEmpty then
      if ((← get).forward.map (·.count)).getD 0 ≥ maxFacts then break
      if let some f ← applyNoHyps a then seeds := seeds.push f
  return seeds

end Whitehead.Prove
