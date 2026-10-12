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
- Which proofs are kept (decided 2026-10-11). Of the proofs of an assertion node, one is
  kept for each substitution of the variables of the parent's expression together with
  its open conditions on bound variables (`proofKey`). That is all a proof shows to the
  nodes above: the parent's proof goes up with these bindings only (`restrict`), and
  the conditions are all that is judged later. So two proofs with the same key can stand
  for each other in every proof above, and the goals proved and the substitutions found
  at the root are the same with one of them as with both; what is not kept is the other
  subproof below the node. Russell keeps one per whole substitution (`ruProofSubKey`),
  which still tells apart proofs that differ only in variables made below the node; the
  number of those multiplies with every step (`propeqop` of set.mm: a million proofs on
  one node after 14 expansions).
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
  let a := prop.rule
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
  | .forward _ _ sub _ _ _ => add acc sub

/-- The open conditions as a part of a key: in an order that does not depend on how they
were found. -/
def condsKey (conds : Array Cond) : Array Nat :=
  if conds.isEmpty then #[]
  else
    let rows := conds.map fun c => (#[c.name, c.expr.size] ++ c.expr.nodes)
    let less (a b : Array Nat) : Bool := Id.run do
      for i in [0:min a.size b.size] do
        if a[i]! != b[i]! then return a[i]! < b[i]!
      return a.size < b.size
    (rows.qsort less).foldl (init := #[conds.size]) (· ++ ·)

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

/-- The key by which `addProof` keeps one proof of an assertion node: its substitution
of the variables of the parent's expression `e`, and its open conditions. -/
def proofKey (theta : Subst) (e : Exp) (conds : Array Cond) : Array Nat :=
  (restrict theta e).key ++ condsKey conds

/-- No limit on the number of tuples. -/
def noLimit : Nat := 0xFFFFFFFF

/-- `check_consistent` of `ruAddProof`: each child's expression under `theta` must be an
instance of the premise of the assertion it stands for, by one substitution for all
premises. It guards against a `theta` that is not applied through. -/
def consistent (prop : PropNode) (theta : Subst) (children : Array Proof) : Bool :=
  let a := prop.rule
  if a.hyps.size != children.size then true
  else
    ((Array.range a.hyps.size).foldl (init := some ({} : Subst)) fun acc i =>
      acc.bind fun s =>
        (matchExp (theta.apply children[i]!.expr) a.hyps[i]!).bind fun sigma => s.merge sigma).isSome

/-- The key of a proof in the index of the joins: what its substitution puts for the
variables `vars`, as one expression. -/
def joinKey (vars : Array Nat) (s : Subst) : Exp :=
  Exp.mkApp (Node.constBase - 1) 0 (vars.map s.lookupD)

/-- From how many proofs a child is indexed for the joins (`catchUp`). -/
def joinIndexFrom : Nat := 64

/-- The indexes of the joins of assertion node `p`, brought up to date with the proofs
of its children. A proof of a child `c` is kept in the index of `c` under what it puts
for the variables that `c` shares with the other children: a new proof of another child
can be joined only with those whose key unifies with its own, which the index finds
without trying the others. The proofs of a node are only ever appended, so the index
of a child grows with them, and a join looks at the proofs that fit and no others. -/
def catchUp (env : Env) (p : Nat) : Env :=
  let hyps := env.hyps
  { env with props := env.props.modify p fun pr =>
      let pr :=
        if pr.joinShared.size == pr.children.size then pr
        else
          let varsOf := pr.children.map fun c => hyps[c]!.expr.vars
          let shared := (Array.range varsOf.size).map fun i =>
            varsOf[i]!.filter fun v => (Array.range varsOf.size).any fun j => j != i && varsOf[j]!.contains v
          { pr with joinShared := shared, joinIndex := shared.map fun _ => {}, joinCount := shared.map fun _ => 0 }
      (Array.range pr.children.size).foldl (init := pr) fun pr i =>
        let proofs := hyps[pr.children[i]!]!.proofs
        let from_ := pr.joinCount[i]!
        -- a child with few proofs is not indexed: trying them is cheaper
        if from_ ≥ proofs.size || pr.joinShared[i]!.isEmpty || proofs.size < joinIndexFrom then pr
        else
          let vars := pr.joinShared[i]!
          { pr with joinIndex := pr.joinIndex.modify i (fun ix =>
                      (Array.range (proofs.size - from_)).foldl (init := ix) fun ix d =>
                        ix.insert (joinKey vars proofs[from_ + d]!.sub) (from_ + d)),
                    joinCount := pr.joinCount.set! i proofs.size } }

/-- `ruAddProof`: the proofs of assertion node `p` that use the new proof `hypProof` of
one of its children. They are added to the node, all of them. At most `maxTuples` of
the tuples that unify are taken; the backward tree gives no limit, the forward front
one that keeps it within its number of facts. A tuple that `made` says has been joined
before is passed over: the forward front asks this, where the same tuple can come up
again; in the backward tree it cannot. -/
def addProof (p : Nat) (hypProof : Proof) (maxTuples : Nat := noLimit)
    (made : Option (Array Proof → Bool) := none) : ProverM Unit := do
  let ready ← do
    let env ← get
    pure (env.props[p]!.children.size == env.props[p]!.rule.hyps.size && !env.overBudget)
  if !ready then return
  -- the theorem's time, and the memory of the process (`memoryLevel`): a join can be the
  -- one step that runs long
  if (← IO.monoMsNow) > (← get).deadline || (← memoryLevel.get) ≥ 2 then
    modify fun env => { env with overBudget := true }
    return
  -- in place: the state is the only holder of the node here
  modify fun env => catchUp env p
  let env ← get
  let prop := env.props[p]!
  -- for each child its proofs that can be joined with the new one, the new one alone
  -- for its own node: those whose key in the index unifies with the new one's
  let sets : Array (Array Proof) := (Array.range prop.children.size).map fun i =>
    let c := prop.children[i]!
    if c == hypProof.node then #[hypProof]
    else
      let proofs := env.hyps[c]!.proofs
      let vars := prop.joinShared[i]!
      if vars.isEmpty || proofs.size < joinIndexFrom then proofs
      else
        let found := (prop.joinIndex[i]!.unify (joinKey vars hypProof.sub)).map (·.data)
        (found.qsort (· < ·)).map fun d => proofs[d]!
  if sets.any (·.isEmpty) then return
  let hypExpr := env.hyps[prop.parent]!.expr
  let size := sets.foldl (init := 1) (· * ·.size)
  -- the work of a join is about the proofs it looks at; past the budget the search stops
  let work := env.counters.work + sets.foldl (init := 0) (· + ·.size)
  if work > env.workBudget then
    set { env with overBudget := true }
    return
  let mut counters := { env.counters with tuples := env.counters.tuples + size, work }
  -- the tuples whose substitutions unify, each with the unifier: tuple by tuple for a
  -- small product, by `unifySubsProd` from 64 tuples on, as in Russell. A product with
  -- one large set only is also walked: there the other way has nothing to save.
  let mut unified : Array (Subst × Array Proof) := #[]
  if size < 64 || (sets.filter (·.size > 1)).size ≤ 1 then
    for picks in tuplesUpTo (sets.map fun set => Array.range set.size) env.tupleBudget do
      if unified.size > env.tupleBudget then break
      let row := (Array.range sets.size).map fun i => sets[i]![picks[i]!]!
      match unifySubs (row.map (·.sub)) with
      | some s => unified := unified.push (s, row)
      | none => pure ()
  else
    -- stopped as soon as it would take the search past its budget
    let cap := env.tupleBudget - min env.tupleBudget (env.counters.tuples - env.counters.notUnified)
    unified := (unifySubsProd (sets.map (·.map (·.sub))) cap).map fun (s, picks) =>
      (s, (Array.range sets.size).map fun i => sets[i]![picks[i]!]!)
  counters := { counters with notUnified := counters.notUnified + (size - unified.size) }
  -- the budget is on the tuples that unify: each is a proof to be made and kept
  if counters.tuples - counters.notUnified > env.tupleBudget then
    set { env with overBudget := true }
    return
  if let some made := made then unified := unified.filter fun (_, row) => !made row
  -- the new proofs are collected apart and appended at the end: the node's own array
  -- and key set are then updated in place, where extending them here, while `env` and
  -- `prop` still hold them, would copy them for every call (quadratic in the proofs of
  -- a node: `nfpo` of set.mm took 88 s)
  let mut proofs : Array Proof := #[]
  let mut keys : Std.HashSet (Array Nat) := {}
  for (s, row) in unified.extract 0 maxTuples do
    match prop.sub.compose s with
    | none => counters := { counters with notUnified := counters.notUnified + 1 }
    | some theta =>
      match openConds env prop theta (theta.apply hypExpr).varIds row with
      | none => counters := { counters with disjoint := counters.disjoint + 1 }
      | some conds =>
        if !consistent prop theta row then
          counters := { counters with inconsistent := counters.inconsistent + 1 }
        else
          let key := proofKey theta hypExpr conds
          if keys.contains key || prop.keys.contains key then
            counters := { counters with duplicate := counters.duplicate + 1 }
          else
            keys := keys.insert key
            proofs := proofs.push (.prop p theta row conds)
  modify fun env =>
    { env with counters, props := env.props.modify p fun prop =>
        { prop with proofs := prop.proofs ++ proofs, keys := keys.fold (init := prop.keys) (·.insert ·) } }

mutual

/-- `ruBuildPropProofs`: the new proofs `proofs` of assertion node `p` become proofs of
its expression node, and go on from there. -/
partial def buildPropProofs (p : Nat) (proofs : Array Proof) : ProverM Unit := do
  if proofs.isEmpty then return
  let env ← get
  let h := env.props[p]!.parent
  -- only what is needed is read, so that the node's array of proofs is extended in place
  let expr := env.hyps[h]!.expr
  let parent := env.hyps[h]!.parent
  let added := proofs.map fun proof =>
    Proof.stmt h (proof.sub.apply expr) (restrict proof.sub expr) proof
  modify fun env => { env with hyps := env.hyps.modify h fun hyp => { hyp with proofs := hyp.proofs ++ added } }
  match parent with
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
      let args := prop.rule.vars.map fun v => resolve all (prop.outer.lookupD v)
      match prop.step with
      | .assertion id => .step id args (children.map (go all))
      | .conv t pos unfold =>
        -- the rule's variables are the def's arguments, then its dummies, then the
        -- variables of the rest of the parent's expression
        let n := env.db.terms[t]!.args.size
        let m := ((env.db.terms[t]!.value.map (·.dummies.size)).getD 0)
        .conv t (env.hyps[prop.parent]!.expr.pathTo pos) unfold (args.extract 0 n) (args.extract n (n + m))
          (go all children[0]!)

end Whitehead.Prove
