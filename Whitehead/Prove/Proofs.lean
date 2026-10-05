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
  with the same result on those variables. `ruMakeProofTree` cannot rely on the
  substitution of a node to contain those of its subtree (see `makeProofTree`).
- The proofs that are kept are those that Russell keeps: one for each *whole*
  substitution (`ruProofSubKey` of Russell's `theta`), and not one for each restricted
  one, which would drop a proof that differs from another only below the node. The
  whole substitution is not carried, so it is put together from the proof when it is
  needed as a key (`allBindings`, `proofKey`), and it is needed only on a node that has
  more than one proof. The open conditions on bound variables are part of the key: two
  proofs with the same substitution and other conditions cannot stand for each other.
- Conditions on bound variables. `ruCheckDisjs` is given the substitution `theta` of
  the new proof, which binds variables of the tree, and looks up in it the variables of
  the assertion's disjoint pairs, which `theta` does not bind (they are in `outer`); so
  it lets everything pass, and Russell finds a violated restriction only when the
  finished proof is verified. Here the two binders of a pair are looked up through
  `outer` and then `theta`, and the pair is judged (`judge`): a proof is discarded if
  the pair is violated whatever the remaining variables become; a pair that can still
  go either way is kept with the proof as an open condition, is carried up with it, and
  is judged again under every substitution it meets (`openConds`). So a proof that is
  doomed stops where it becomes doomed, and what reaches the root satisfies every
  condition, up to the choice of what is put for the variables that are left
  (`docs/DESIGN.md`, "Where MM0 differs").
-/
import Whitehead.Prove.Env
import Whitehead.Prove.Prod

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

/-- What can be said of a condition "the name `x` does not occur in `e`", given the
variables that the nodes above can still replace (`visible`). -/
inductive Verdict where
  /-- It is false, whatever the remaining variables become. -/
  | violated
  /-- It is true, whatever they become. -/
  | settled
  /-- It can still go either way. -/
  | pending (c : Cond)

/-- Judges a condition. `x` must be a name: one node.

- A bound variable of the task: violated if it occurs in `e`, or a regular variable of
  the task that depends on it does; settled if `e` has no variable left; else open.
- A variable of the tree: violated if it occurs in `e`. Otherwise, if no node above can
  replace it, it will become a dummy of its own (or be merged with another name that no
  step needs it to differ from, `mergeNames`), which occurs in nothing: settled. If a
  node above can still replace it, open. -/
def judge (task : Task) (visible : Std.HashSet Nat) (x e : Exp) : Verdict :=
  if x.size != 1 then .settled
  else
    let n := x.nodes[0]!
    if occursFor task n e then .violated
    else if Node.isVar n then
      if visible.contains (Node.varId n) then .pending ⟨n, e⟩ else .settled
    else if e.hasVars then .pending ⟨n, e⟩
    else .settled

/-- The conditions on bound variables of a proof of assertion node `prop` with
substitution `theta` and the proofs `row` of its premises: those of its own assertion,
and those that the proofs of the premises still carry, all under `theta`. `none` if one
is violated; otherwise those that are still open. `visible` are the variables that
remain in the expression of the node above. -/
def openConds (env : Env) (prop : PropNode) (theta : Subst) (visible : Std.HashSet Nat)
    (row : Array Proof) : Option (Array Cond) := Id.run do
  let a := env.db.asserts[prop.assertion]!
  let mut out : Array Cond := #[]
  for (x, v) in a.disjs do
    match judge env.task visible (theta.apply (prop.outer.lookupD a.vars[x]!))
        (theta.apply (prop.outer.lookupD a.vars[v]!)) with
    | .violated => return none
    | .settled => pure ()
    | .pending c => if !out.contains c then out := out.push c
  for child in row do
    for c in child.conds do
      match judge env.task visible (theta.apply ⟨#[c.name]⟩) (theta.apply c.expr) with
      | .violated => return none
      | .settled => pure ()
      | .pending c => if !out.contains c then out := out.push c
  return some out

/-- The open conditions as a part of the key of a proof: in an order that does not
depend on how they were found. -/
def condsKey (conds : Array Cond) : Array Nat :=
  if conds.isEmpty then #[]
  else
    let rows := conds.map fun c => (#[c.name, c.expr.size] ++ c.expr.nodes)
    let less (a b : Array Nat) : Bool := Id.run do
      for i in [0:min a.size b.size] do
        if a[i]! != b[i]! then return a[i]! < b[i]!
      return a.size < b.size
    (rows.qsort less).foldl (init := #[conds.size]) (· ++ ·)

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
  | .forward _ _ _ _ _ whole => add acc whole

/-- The key by which `addProof` keeps one proof of an assertion node for each
(`ruProofSubKey`): the whole substitution of the proof, which is Russell's `theta` — every
binding made in the proof, not only those that the nodes above can see — and its open
conditions on bound variables. -/
def proofKey (proof : Proof) : Array Nat :=
  (allBindings proof).key ++ condsKey proof.conds

/-- No limit on the number of tuples. -/
def noLimit : Nat := 0xFFFFFFFF

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
one of its children. They are added to the node. At most `maxTuples` of the tuples
that unify are taken; the backward tree gives no limit, the forward front one that keeps
it within its number of facts. -/
def addProof (p : Nat) (hypProof : Proof) (maxTuples : Nat := noLimit) : ProverM Unit := do
  let env ← get
  let prop := env.props[p]!
  let arity := env.db.asserts[prop.assertion]!.hyps.size
  if prop.children.size != arity then return
  -- for each child its proofs, the new one alone for its own node
  let sets : Array (Array Proof) := prop.children.map fun c =>
    if c == hypProof.node then #[hypProof] else env.hyps[c]!.proofs
  if sets.any (·.isEmpty) then return
  let hypExpr := env.hyps[prop.parent]!.expr
  let size := sets.foldl (init := 1) (· * ·.size)
  let mut counters := { env.counters with tuples := env.counters.tuples + size }
  -- the tuples whose substitutions unify, each with the unifier: tuple by tuple for a
  -- small product, by `unifySubsProd` from 64 tuples on, as in Russell. A product with
  -- one large set only is also walked: there the other way has nothing to save.
  let mut unified : Array (Subst × Array Proof) := #[]
  if size < 64 || (sets.filter (·.size > 1)).size ≤ 1 then
    for picks in tuples (sets.map fun set => Array.range set.size) do
      let row := (Array.range sets.size).map fun i => sets[i]![picks[i]!]!
      match unifySubs (row.map (·.sub)) with
      | some s => unified := unified.push (s, row)
      | none => pure ()
  else
    unified := (unifySubsProd (sets.map (·.map (·.sub)))).map fun (s, picks) =>
      (s, (Array.range sets.size).map fun i => sets[i]![picks[i]!]!)
  counters := { counters with notUnified := counters.notUnified + (size - unified.size) }
  let mut proofs := prop.proofs
  let mut keys := prop.keys
  for (s, row) in unified.extract 0 maxTuples do
    match prop.sub.compose s with
    | none => counters := { counters with notUnified := counters.notUnified + 1 }
    | some theta =>
      match openConds env prop theta (theta.apply hypExpr).varIds row with
      | none => counters := { counters with disjoint := counters.disjoint + 1 }
      | some conds =>
        if !consistent env prop theta row then
          counters := { counters with inconsistent := counters.inconsistent + 1 }
        else
          -- one proof for each whole substitution with its open conditions. The keys
          -- are made when the node gets its second proof: a node with one proof, as
          -- every node of a replay, needs none.
          let proof := Proof.prop p theta row conds
          counters := { counters with made := counters.made + 1 }
          if proofs.isEmpty then proofs := proofs.push proof
          else
            if keys.isEmpty then keys := keys.insert (proofKey proofs[0]!)
            let key := proofKey proof
            if keys.contains key then
              counters := { counters with duplicate := counters.duplicate + 1 }
            else
              keys := keys.insert key
              proofs := proofs.push proof
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
    -- `ruBuildRootProofs`: the driver takes them from here. (A node of the forward
    -- front has no parent either; its proofs go nowhere.)
    if h == 0 then modify fun env => { env with rootProofs := env.rootProofs ++ added }

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
    | .forward _ _ _ tree _ _ => tree.subst all
    | .prop p _ children _ =>
      let prop := env.props[p]!
      let a := env.db.asserts[prop.assertion]!
      .step a.id (a.vars.map fun v => resolve all (prop.outer.lookupD v)) (children.map (go all))

end Whitehead.Prove
