/-
The upward pass: a port of `russell-flow/src/ru/prover/core/expand.flow`, and of
`ruProveProp` from `prove.flow`.

`expandHyp` gives an expression node one assertion node for every assertion whose
conclusion unifies with it. `expandProp` gives an assertion node its expression nodes,
the premises of the assertion under the unifier; each is matched with the premises of
the task and expanded at once. Not ported: the forward closure and the forward front
that `ruExpandProp` also consults.
-/
import Whitehead.Prove.Proofs

namespace Whitehead.Prove

/-- The assertions that may prove expression node `h`, each with the unifier of its
conclusion and the expression: all that the index finds among those declared before the
task's theorem, or the one that `only` names. -/
def candidates (env : Env) (h : Nat) (only : Option Only) : Array (Index.Unified Nat) :=
  let e := env.hyps[h]!.expr
  match only with
  | none => env.assertions.unify e {} env.task.limit
  | some (.assertion id) =>
    match unifyExps #[e, env.db.asserts[id]!.concl] {} with
    | some s => #[⟨s, id, s.apply e⟩]
    | none => #[]
  | some (.premise _) => #[]

/-- `ruExpandHyp` -/
def expandHyp (h : Nat) (only : Option Only := none) : ProverM Unit := do
  let env ← get
  -- the candidates that bind more come first; among equals, the order of the index
  let unified := (candidates env h only).toList.mergeSort (fun a b => a.sub.size ≥ b.sub.size)
  for unif in unified do
    let a := (← get).db.asserts[unif.data]!
    -- the variables of the assertion that the unifier leaves free get fresh names
    let free := a.vars.filter fun v => !unif.sub.maps (Node.varId v)
    let base := (← get).fresh
    let fresher : Subst :=
      { map := (Array.range free.size).foldl (init := {}) fun m k =>
          let v := free[k]!
          m.insert (Node.varId v) (SubExp.mk' v (Exp.ofVar (Node.var (base + k) (Node.ty v)))) }
    let sAll := unif.sub.unsafeCompose fresher
    let isOfAssertion : Nat → Exp → Bool := fun v _ => Node.varId v < freshBase
    let prop : PropNode :=
      { assertion := a.id, parent := h,
        sub := sAll.filter fun v e => !isOfAssertion v e,
        outer := sAll.filter isOfAssertion }
    modify fun env =>
      let p := env.props.size
      { env with fresh := base + free.size, props := env.props.push prop, leafs := env.leafs.push p,
                 hyps := env.hyps.modify h fun hyp => { hyp with children := hyp.children.push p },
                 counters := { env.counters with props := env.counters.props + 1 } }

/-- `ruExpandProp`. `only` restricts, for each premise of the assertion, what its
expression node may use. -/
def expandProp (p : Nat) (only : Option (Array Only) := none) : ProverM Unit := do
  modify fun env =>
    { env with props := env.props.modify p fun prop => { prop with expanded := true },
               counters := { env.counters with expanded := env.counters.expanded + 1 } }
  let env ← get
  let prop := env.props[p]!
  let a := env.db.asserts[prop.assertion]!
  if a.hyps.isEmpty then
    -- an assertion without premises is a proof at once, if its conditions on bound
    -- variables allow it
    let visible := (prop.sub.apply env.hyps[prop.parent]!.expr).varIds
    match openConds env prop prop.sub visible #[] with
    | none => modify fun env => { env with counters := { env.counters with disjoint := env.counters.disjoint + 1 } }
    | some conds =>
      modify fun env => { env with props := env.props.modify p fun prop =>
        { prop with proofs := prop.proofs.push (.prop p prop.sub #[] conds),
                    keys := prop.keys.insert (prop.sub.key ++ condsKey conds) } }
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
      let unified := (env.premises.unify ex).filter fun u =>
        match restriction with
        | none => true
        | some (.premise k) => u.data == k
        | some (.assertion _) => false
      for unif in unified do
        let proof := Proof.top h unif.expr unif.data unif.sub
        modify fun env => { env with hyps := env.hyps.modify h fun hyp => { hyp with proofs := hyp.proofs.push proof } }
        addProof p proof
      expandHyp h restriction

/-- `ruProveProp`: expands an assertion node, and carries the proofs that this gives it
down the tree. -/
def proveProp (p : Nat) (only : Option (Array Only) := none) : ProverM Unit := do
  expandProp p only
  buildPropProofs p (← get).props[p]!.proofs

end Whitehead.Prove
