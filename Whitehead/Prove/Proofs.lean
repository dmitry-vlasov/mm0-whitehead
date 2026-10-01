/-
The downward pass: a port of `russell-flow/src/ru/prover/core/proofs.flow`.

When an expression node gets a new proof, `addProof` joins it with the proofs of its
siblings into proofs of their assertion node: for each tuple, the most general unifier
of the substitutions of the tuple, composed with the unifier of the assertion node.
`buildPropProofs` and `buildExpProofs` carry what is new to the parent, up to the root.

What differs from Russell:

- A proof of an expression node goes up with its substitution restricted to the
  variables of the node's expression (`restrict`). Russell carries the whole
  substitution of the subtree to the root; it grows with the subtree, and a proof of
  thousands of steps is then composed again at every level. The restricted one has the
  same bindings for everything that the nodes above can see, so the same tuples unify,
  with the same result on those variables. Two things follow. `ruMakeProofTree` cannot
  rely on the substitution of a node to contain those of its subtree (see
  `makeProofTree`). And proofs of one assertion node have the same key (`ruProofSubKey`)
  when they agree on what is visible above, also if they differ below. Keeping one of
  them is right when either can stand for the other in every proof above, which is so
  unless a condition on bound variables is still open in one of them: that one may be
  rejected at the root where the other would not. So only proofs that apply no
  assertion with such conditions are kept once per key; the others are all kept.
- The product of the proofs is always walked tuple by tuple. Russell switches to
  `ruUnifySubsProd` (`unify/prod.flow`) for products of 64 tuples and more; it gives the
  same proofs faster and is not ported yet.
- `ruCheckDisjs` is given the substitution `theta` of the new proof, which binds
  variables of the tree, and looks up in it the variables of the assertion's disjoint
  pairs, which `theta` does not bind (they are in `outer`); so it lets everything pass,
  and Russell finds a violated restriction only when the finished proof is verified.
  Here the two binders of a pair are looked up through `outer` and then `theta`, and a
  proof is discarded if the pair is violated whatever the remaining variables become
  (`docs/DESIGN.md`, "Where MM0 differs").
-/
import Whitehead.Prove.Env

namespace Whitehead.Prove

/-- Does a name certainly occur in `e`? `x` is the node of the name: a constant for a
bound variable of the task, or a variable of the tree. Certainly: for a constant, if it
occurs or a regular constant that depends on it does; for a variable, if it occurs. What
a variable of `e` may still become is not counted. -/
def occursFor (task : Task) (x : Nat) (e : Exp) : Bool :=
  if Node.isVar x then e.nodes.contains x
  else
    let k := Node.appId x - Node.constBase
    e.nodes.any fun n =>
      Node.isConst n && (task.consts[Node.appId n - Node.constBase]!.names.contains k)

/-- The disjoint variable conditions of the assertion of `prop`, under `theta`: `false`
if one of them is violated for certain. -/
def checkDisjs (env : Env) (prop : PropNode) (theta : Subst) : Bool :=
  let a := env.db.asserts[prop.assertion]!
  a.disjs.all fun (x, v) =>
    let ex := theta.apply (prop.outer.lookupD a.vars[x]!)
    let ev := theta.apply (prop.outer.lookupD a.vars[v]!)
    !(ex.size == 1 && occursFor env.task ex.nodes[0]! ev)

/-- `check_consistent` of `ruAddProof`: each child's expression under `theta` must be an
instance of the premise of the assertion it stands for, by one substitution for all
premises. It guards against a `theta` that is not applied through. -/
def consistent (env : Env) (prop : PropNode) (theta : Subst) (children : Array Proof) : Bool :=
  let a := env.db.asserts[prop.assertion]!
  if a.hyps.size != children.size then true
  else
    ((Array.range a.hyps.size).foldl (init := some ({} : Subst)) fun acc i =>
      acc.bind fun s =>
        (matchExp (theta.apply children[i]!.expr) a.hyps[i]!).bind fun sigma => s.merge sigma).isSome

/-- `ruAddProof`: the proofs of assertion node `p` that use the new proof `hypProof` of
one of its children. They are added to the node. -/
def addProof (p : Nat) (hypProof : Proof) : ProverM Unit := do
  let env ← get
  let prop := env.props[p]!
  let arity := env.db.asserts[prop.assertion]!.hyps.size
  if prop.children.size != arity then return
  -- for each child its proofs, the new one alone for its own node
  let sets : Array (Array Proof) := prop.children.map fun c =>
    if c == hypProof.node then #[hypProof] else env.hyps[c]!.proofs
  if sets.any (·.isEmpty) then return
  let hasPairs := !env.db.asserts[prop.assertion]!.disjs.isEmpty
  let mut counters := env.counters
  let mut proofs := prop.proofs
  let mut keys := prop.keys
  -- all tuples, the last position changing fastest
  let mut pick : Array Nat := Array.replicate sets.size 0
  let mut more := true
  while more do
    let row := (Array.range sets.size).map fun i => sets[i]![pick[i]!]!
    counters := { counters with tuples := counters.tuples + 1 }
    match unifySubs (row.map (·.sub)) with
    | none => counters := { counters with notUnified := counters.notUnified + 1 }
    | some s =>
      match prop.sub.compose s with
      | none => counters := { counters with notUnified := counters.notUnified + 1 }
      | some theta =>
        if !checkDisjs env prop theta then
          counters := { counters with disjoint := counters.disjoint + 1 }
        else if !consistent env prop theta row then
          counters := { counters with inconsistent := counters.inconsistent + 1 }
        else
          -- one proof for each substitution, but only among proofs that no condition on
          -- bound variables can still spoil: see the note at the head of this file
          let conds := hasPairs || row.any (·.conds)
          let key := theta.key
          if !conds && keys.contains key then
            counters := { counters with duplicate := counters.duplicate + 1 }
          else
            keys := keys.insert key
            proofs := proofs.push (.prop p theta row conds)
    -- the next tuple
    let mut i := sets.size
    more := false
    while i > 0 && !more do
      i := i - 1
      if pick[i]! + 1 < sets[i]!.size then
        pick := pick.set! i (pick[i]! + 1)
        more := true
      else
        pick := pick.set! i 0
  modify fun env =>
    { env with counters, props := env.props.modify p fun prop => { prop with proofs, keys } }

/-- The bindings of `theta` for the variables of `e`. A proof of an expression node goes
up the tree with these only: the other variables that its substitution binds were made
below the node and occur nowhere else, so the proofs of the siblings cannot depend on
them. -/
def restrict (theta : Subst) (e : Exp) : Subst :=
  { map := e.nodes.foldl (init := {}) fun m n =>
      if Node.isVar n then
        match theta.map[Node.varId n]? with
        | some x => m.insert (Node.varId n) x
        | none => m
      else m }

mutual

/-- `ruBuildPropProofs`: the new proofs `proofs` of assertion node `p` become proofs of
its expression node, and go on from there. -/
partial def buildPropProofs (p : Nat) (proofs : Array Proof) : ProverM Unit := do
  if proofs.isEmpty then return
  let env ← get
  let h := env.props[p]!.parent
  let hyp := env.hyps[h]!
  let added := proofs.map fun proof =>
    Proof.stmt h (proof.sub.apply hyp.expr) (restrict proof.sub hyp.expr) proof
  modify fun env => { env with hyps := env.hyps.modify h fun hyp => { hyp with proofs := hyp.proofs ++ added } }
  match hyp.parent with
  | some _ => buildExpProofs h added
  | none =>
    -- `ruBuildRootProofs`: the driver takes them from here
    modify fun env => { env with rootProofs := env.rootProofs ++ added }

/-- `ruBuildExpProofs`: the new proofs `proofs` of expression node `h` are joined with
those of its siblings. -/
partial def buildExpProofs (h : Nat) (proofs : Array Proof) : ProverM Unit := do
  let env ← get
  let some p := env.hyps[h]!.parent | return
  let before := env.props[p]!.proofs.size
  for proof in proofs do
    addProof p proof
  let env ← get
  let all := env.props[p]!.proofs
  buildPropProofs p (all.extract before all.size)

end

/-- The bindings of all substitutions in a proof, as one substitution. The proof is
walked from the root down, and a binding of a node is taken if no node above it binds
the variable; its image is brought under the bindings from above first.

A variable can be bound below and free above: when two variables are identified, a node
below may bind the first to the second and a node above the second to the first. The
binding from below then says nothing new — under the bindings from above its image is
the variable itself — and is left out. -/
partial def allBindings (proof : Proof) (acc : Subst := {}) : Subst :=
  let add (acc : Subst) (s : Subst) : Subst :=
    s.map.fold (init := acc) fun acc v x =>
      if acc.map.contains v then acc
      else
        let image := acc.apply x.exp
        if image.isTheVar x.var then acc
        else { map := acc.map.insert v (SubExp.mk' x.var image) }
  match proof with
  | .top _ _ _ sub => add acc sub
  | .stmt _ _ _ child => allBindings child acc
  | .prop _ sub children _ => children.foldl (init := add acc sub) fun acc ch => allBindings ch acc

/-- `ruMakeProofTree`: the proof that a substitution proof tree stands for.

Russell instantiates the expressions of a step by the substitution of that step, and
then applies the substitution of every step above it to the whole subtree. Here the
bindings of all steps are collected first (`allBindings`) and applied to each expression
once: the result is the same, and a step is visited once instead of once for every step
above it. -/
partial def makeProofTree (env : Env) (proof : Proof) : ProofTree :=
  go (allBindings proof) proof
where
  /-- One application is enough if no image has a bound variable; a few more are allowed
  for, and what is still not through is caught by the verifier. -/
  resolve (all : Subst) (e : Exp) (fuel : Nat := 8) : Exp :=
    if fuel != 0 && all.affects e then resolve all (all.applyRaw e) (fuel - 1) else e
  go (all : Subst) : Proof → ProofTree
    | .top _ _ premise _ => .hyp premise
    | .stmt _ _ _ child => go all child
    | .prop p _ children _ =>
      let prop := env.props[p]!
      let a := env.db.asserts[prop.assertion]!
      .step a.id (a.vars.map fun v => resolve all (prop.outer.lookupD v)) (children.map (go all))

end Whitehead.Prove
