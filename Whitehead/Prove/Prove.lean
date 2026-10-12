/-
The search loop: a port of `russell-flow/src/ru/prover/core/prove.flow`, with the
strategy interface of `core/controls.flow` (`RuProverTactic`) reduced to what the two
strategies here need, and the acceptance of a found proof
(`ruMakeProofFromSteps` in `core/util.flow`).

The layers: the engine (`Expand.lean`, `Proofs.lean`) grows the tree and joins proofs;
a strategy only says which assertion nodes to expand next; a proof that reaches the root
is closed, emitted and checked by the verifier here, and a proof that fails the check is
dropped while the search goes on.
-/
import Whitehead.Verify.Check
import Whitehead.Prove.Expand
import Whitehead.Prove.Emit

namespace Whitehead.Prove

open Whitehead.Mmb

/-- `RuProverTacticStep`: what a strategy asks for. -/
inductive Decision where
  /-- Expand these assertion nodes, each with the restriction of its premises, if any. -/
  | expand (items : Array (Nat × Option (Array Only)))
  /-- `RuTacticExpandForward`: advance the forward front by one wave. -/
  | forward
  | done

/-- `RuProverTactic`. A strategy has a state of its own and reads the tree; it does not
change it. -/
structure Strategy (σ : Type) where
  /-- The restriction for the root, if any. -/
  root : Option Only
  init : σ
  step : Env → σ → Decision × σ
  /-- The strategy uses the forward front: it is seeded before the root is expanded. -/
  forward : Bool := false
  /-- Which joins of a new fact with a subgoal are made (`RuProverEnv.admitJoin`). -/
  admitJoin : Exp → Exp → Bool := fun _ _ => true

/-- `ruBreadthFirstTactic` (`tactics/breadth_first.flow`): all leaves, round by round.
This is the fair strategy of the completeness theorem. -/
def breadthFirst : Strategy Unit where
  root := none
  init := ()
  step env _ :=
    let leafs := env.leafs.filter fun p => !env.props[p]!.expanded
    if leafs.isEmpty then (.done, ()) else (.expand (leafs.map fun p => (p, none)), ())

/-- `ruForwardTactic`: one wave of the forward front after another. A proof is found
when a fact proves the goal. -/
def forwardOnly : Strategy Unit where
  root := none
  init := ()
  step _ _ := (.forward, ())
  forward := true

/-- Both directions in turn: a round of the backward tree, then a wave of the forward
front. The two meet in the joins of `Forward.lean`. (In Russell such a strategy is put
together in the tactic language, from `bfs` and `forward`.)

A new fact is not joined with a subgoal that is a bare variable, such as the minor
premise of modus ponens: it unifies with every fact, and with a backward tree of any
size each fact would be put on thousands of them. This is the policy that Russell's
`ordered` tactic installs (`tactics/dsl.flow`). Such a subgoal is still proved by the
backward search, by the facts that are there when it is made, and through the joins of
its siblings. -/
def bidirectional : Strategy Bool where
  root := none
  init := false
  step env forwardTurn :=
    let leafs := env.leafs.filter fun p => !env.props[p]!.expanded
    if forwardTurn || leafs.isEmpty then (.forward, false)
    else (.expand (leafs.map fun p => (p, none)), true)
  forward := true
  admitJoin _ subgoal := !subgoal.isVar

/-- The state of `oracle`: the assertion nodes expanded in the last round, each with the
step of the known proof that it stands for. -/
structure OracleState where
  started : Bool := false
  expanded : Array (Nat × Skeleton) := #[]

/-- Replay of a known proof (after `tactics/oracle.flow`): at every expression node only
the assertion that the known proof uses there is expanded, and a premise only where the
known proof uses that premise. The expressions of the known proof are not used. -/
def oracle (skel : Skeleton) : Strategy OracleState where
  root := some skel.only
  init := {}
  step env st :=
    -- the assertion nodes that the last round made for the steps of the known proof
    let matching (h : Nat) (s : Skeleton) : Array (Nat × Skeleton) :=
      let wanted : Option Step := match s with
        | .step t _ => some (.assertion t)
        | .hyp _ => none
        | .conv t path unfold _ => (env.hyps[h]!.expr.nodeAt path).map fun pos => .conv t pos unfold
      match wanted with
      | some step => env.hyps[h]!.children.filterMap fun p =>
          if env.props[p]!.step == step && !env.props[p]!.expanded then some (p, s) else none
      | none => #[]
    let children (s : Skeleton) : Array Skeleton := match s with
      | .step _ cs => cs
      | .conv _ _ _ c => #[c]
      | .hyp _ => #[]
    let next : Array (Nat × Skeleton) :=
      if !st.started then matching 0 skel
      else st.expanded.foldl (init := #[]) fun acc (p, s) =>
        let hyps := env.props[p]!.children
        let cs := children s
        (Array.range (min hyps.size cs.size)).foldl (init := acc) fun acc i => acc ++ matching hyps[i]! cs[i]!
    if next.isEmpty then (.done, { st with started := true })
    else
      let items := next.map fun (p, s) =>
        match s with
        | .hyp _ => (p, none)
        | _ => (p, some ((children s).map (·.only)))
      (.expand items, { started := true, expanded := next })

/-- The state of `oracleAll`: as for `oracle`, and the nodes whose alternatives have
been taken. -/
structure OracleAllState where
  started : Bool := false
  expanded : Array (Nat × Skeleton) := #[]

/-- `ruOracleTactic` (`tactics/oracle.flow`): replay of a known proof over the full
expansion. Every expression node is expanded without restriction, so it gets *all* its
variants — every assertion whose conclusion unifies with it, found in the index, every
unfolding, every premise it unifies with — and the strategy clicks the one on the path
of the known proof. With `others`, it also expands up to that many of the other
variants of every node on the path (`none`: all of them), whose proofs then meet those
of the path in the joins of `ruAddProof`. A variant is never removed: the strategy
only chooses what to expand. -/
def oracleAll (skel : Skeleton) (others : Option Nat) : Strategy OracleAllState where
  root := none
  init := {}
  step env st :=
    let wanted (h : Nat) (s : Skeleton) : Option Step := match s with
      | .step t _ => some (.assertion t)
      | .hyp _ => none
      | .conv t path unfold _ => (env.hyps[h]!.expr.nodeAt path).map fun pos => .conv t pos unfold
    -- the variant on the path at node `h`, if any, and the alternatives to expand
    let at_ (h : Nat) (s : Skeleton) : Array (Nat × Skeleton) × Array Nat :=
      let w := wanted h s
      let kids := env.hyps[h]!.children
      let onPath := kids.filter fun p => some env.props[p]!.step == w && !env.props[p]!.expanded
      let rest := kids.filter fun p => some env.props[p]!.step != w && !env.props[p]!.expanded
      let alts := match others with
        | none => rest
        | some n => rest.extract 0 n
      (onPath.map (·, s), alts)
    let children (s : Skeleton) : Array Skeleton := match s with
      | .step _ cs => cs
      | .conv _ _ _ c => #[c]
      | .hyp _ => #[]
    let (next, alts) : Array (Nat × Skeleton) × Array Nat :=
      if !st.started then at_ 0 skel
      else st.expanded.foldl (init := (#[], #[])) fun (acc, alts) (p, s) =>
        let hyps := env.props[p]!.children
        let cs := children s
        (Array.range (min hyps.size cs.size)).foldl (init := (acc, alts)) fun (acc, alts) i =>
          let (n, a) := at_ hyps[i]! cs[i]!
          (acc ++ n, alts ++ a)
    if next.isEmpty && alts.isEmpty then (.done, { st with started := true })
    else (.expand ((next.map fun (p, _) => (p, none)) ++ alts.map fun p => (p, none)),
          { started := true, expanded := next })

/-- Does a proof have the shape of a known one: the same assertions, nested the same
way, the same hypotheses at the leaves? -/
partial def sameShape (t : ProofTree) (s : Skeleton) : Bool :=
  match t, s with
  | .hyp i, .hyp j => i == j
  | .step a _ cs, .step b ds => a == b && cs.size == ds.size && (cs.zip ds).all fun (c, d) => sameShape c d
  | .conv t p u _ _ c, .conv t' p' u' d => t == t' && p == p' && u == u' && sameShape c d
  | _, _ => false

/-- What `accept` says of a proof at the root that is not the one asked for. -/
def anotherProof : String := "another proof than the known one"

/-! ### Closing and accepting a proof -/

/-- What a regular variable that is left in a proof may be replaced by: a new name, if
the sort has bound variables; a term without arguments; a variable of the theorem. -/
def closers (env : Env) (ty : Nat) (freshId : Nat) : Array Exp := Id.run do
  let db := env.db
  let sort := Ty.sort ty
  let mut out : Array Exp := #[]
  -- a dummy needs a sort that is neither strict nor free
  if (db.file.sorts[sort]!.raw &&& 10) == 0 then
    out := out.push (Exp.ofVar (Node.var freshId (Ty.mk sort true)))
  for t in [0:env.task.terms] do
    let info := db.terms[t]!
    if info.ty == ty && info.args.isEmpty then out := out.push (Exp.mkApp t ty #[])
  -- the variables of the theorem, those with fewer dependencies first
  let consts := (Array.range env.task.consts.size).filter fun k => Ty.fits ty env.task.consts[k]!.ty
  for k in consts.qsort fun a b => env.task.consts[a]!.names.size < env.task.consts[b]!.names.size do
    out := out.push ⟨#[Node.const k env.task.consts[k]!.ty]⟩
  return out

/-- The pairs of leftover names of a proof that must stay different: a step needs them
so when one is given for a bound binder `x` of its assertion and the other occurs in
what is given for a binder that `x` must be kept apart from. -/
partial def nameConflicts (db : Db) (t : ProofTree) (acc : Array (Nat × Nat) := #[]) : Array (Nat × Nat) :=
  match t with
  | .hyp _ => acc
  | .step a args children =>
    let acc := db.asserts[a]!.disjs.foldl (init := acc) fun acc (x, v) => apart acc args[x]! args[v]!
    children.foldl (init := acc) fun acc c => nameConflicts db c acc
  | .conv _ _ _ args dummies child =>
    -- a dummy of the def must differ from the other dummies and from the names in
    -- the arguments
    let acc := (Array.range dummies.size).foldl (init := acc) fun acc j =>
      let acc := args.foldl (init := acc) fun acc a => apart acc dummies[j]! a
      (Array.range dummies.size).foldl (init := acc) fun acc j' =>
        if j' != j then apart acc dummies[j]! dummies[j']! else acc
    nameConflicts db child acc
where
  /-- The name `ex`, if it is a variable, must differ from the variables of `e`. -/
  apart (acc : Array (Nat × Nat)) (ex e : Exp) : Array (Nat × Nat) :=
    if ex.isVar then
      e.nodes.foldl (init := acc) fun acc n =>
        if Node.isVar n && n != ex.nodes[0]! then acc.push (ex.nodes[0]!, n) else acc
    else acc

/-- The proof with as few leftover names as its steps allow: every name is replaced by
the first earlier one of its type that it need not differ from. MM0 allows 55 bound
variables in a theorem, and the most general proof has a name of its own wherever the
known proof could use one name again. -/
def mergeNames (db : Db) (tree : ProofTree) : ProofTree := Id.run do
  let names := tree.vars.filter fun v => Ty.isName (Node.ty v)
  let conflicts := nameConflicts db tree
  let mut differs : Std.HashSet (Nat × Nat) := {}
  for (a, b) in conflicts do
    differs := (differs.insert (a, b)).insert (b, a)
  -- the names that are kept, and for each of them the names that became it
  let mut kept : Array (Nat × Array Nat) := #[]
  let mut map : Std.HashMap Nat SubExp := {}
  for v in names do
    let mut placed := false
    for k in [0:kept.size] do
      let (rep, members) := kept[k]!
      if !placed && Node.ty rep == Node.ty v && members.all fun m => !differs.contains (m, v) then
        kept := kept.set! k (rep, members.push v)
        map := map.insert (Node.varId v) (SubExp.mk' v (Exp.ofVar rep))
        placed := true
    if !placed then kept := kept.push (v, #[v])
  return if map.isEmpty then tree else tree.subst { map }

/-- The proof with its leftover regular variables replaced, in up to `tries` ways: the
`k`-th way takes the `k`-th choice for every variable (the last one, if there are
fewer). Names that are left stay: they become dummies. `conds` are the conditions on
bound variables that are still open in the proof; a choice must keep them true. -/
def closings (env : Env) (tree : ProofTree) (conds : Array Cond := #[]) (tries : Nat := 4) :
    Array ProofTree := Id.run do
  let regular := tree.vars.filter fun v => !Ty.isName (Node.ty v)
  if regular.isEmpty then return #[fit tree]
  let choices := (Array.range regular.size).map fun i => closers env (Node.ty regular[i]!) (env.fresh + i)
  if choices.any (·.isEmpty) then return #[]
  let most := choices.foldl (init := 1) fun n c => max n c.size
  let mut out := #[]
  for k in [0:min tries most] do
    let map : Std.HashMap Nat SubExp := (Array.range regular.size).foldl (init := {}) fun m i =>
      let c := choices[i]!
      m.insert (Node.varId regular[i]!) (SubExp.mk' regular[i]! c[min k (c.size - 1)]!)
    -- a choice that makes an open condition false is left out
    let closing : Subst := { map }
    let fails := conds.any fun c =>
      match judge env.task {} (closing.apply ⟨#[c.name]⟩) (closing.apply c.expr) with
      | .violated => true
      | _ => false
    if !fails then out := out.push (fit (tree.subst closing))
  return out
where
  /-- Names are merged only when there would be too many bound variables otherwise. -/
  fit (tree : ProofTree) : ProofTree :=
    let names := (tree.vars.filter fun v => Ty.isName (Node.ty v)).size
    let bound := (env.task.consts.filter fun c => Ty.isName c.ty).size
    if names + bound > 55 then mergeNames env.db tree else tree

/-- The proof body for a proof that reached the root, if the verifier accepts one of
its closings; otherwise what the verifier said about the last one. -/
def accept (vc : Verify.Ctx) (env : Env) (tree : ProofTree) (conds : Array Cond) :
    Except String ByteArray := Id.run do
  let db := env.db
  let mut why := "a variable is left in the proof that nothing can be put for"
  for closed in closings env tree conds do
    match emitBody db env.task closed with
    | none => why := "a variable that is not a name is left in the proof"
    | some cmds =>
      let body := encodeProof cmds
      match Verify.checkBody vc db.file env.task.limit env.task.sorts env.task.terms body with
      | .ok () => return .ok body
      | .error msg => why := msg
  return .error why

/-- Accepts every proof, with no proof body: for a task that is not a theorem of the
file, such as one with metavariables, whose proof proves an instance of the theorem. -/
def acceptAny (_ : Env) (_ : ProofTree) (_ : Array Cond) : Except String ByteArray := .ok ByteArray.empty

/-- Why a search ended. -/
inductive Ending where
  | proved
  /-- The strategy has nothing more to expand. -/
  | exhausted
  /-- The limit of assertion nodes or of time was reached. -/
  | limit
  deriving BEq, Inhabited

structure Limits where
  /-- The largest number of assertion nodes in the tree. -/
  maxProps : Nat := 1000000
  /-- The time allowed, in milliseconds. -/
  maxMs : Nat := 1000000000
  /-- The largest number of facts in the forward front (`forward-search-size`). -/
  maxFacts : Nat := 512
  /-- The largest number of tuples of proofs joined (`Env.tupleBudget`), and the largest
  work of the joins (`Env.workBudget`). -/
  maxTuples : Nat := 0xFFFFFFFFFFFF
  maxWork : Nat := 0xFFFFFFFFFFFF

structure Result where
  ending : Ending
  proof : Option ProofTree := none
  /-- The proof body, with its `END`. -/
  body : Option ByteArray := none
  /-- The goal as it was proved: with the variables it had replaced by what the proof
  needs them to be. Variables that the proof leaves open are still there. -/
  answer : Option Exp := none
  /-- What the proof puts for each metavariable of the task. One that the proof leaves
  open stands for itself. -/
  values : Array Exp := #[]
  /-- The proofs that reached the root and were not accepted by the verifier, and what
  it said about the last of them. -/
  rejected : Nat := 0
  rejection : String := ""
  /-- The last proof that was rejected. -/
  rejectedProof : Option ProofTree := none
  /-- Proofs that reached the root and were turned down as `anotherProof`; they are not
  counted in `rejected`. -/
  others : Nat := 0
  env : Env

/-- What a proof at the root puts for the metavariables of the task. -/
def metaValues (env : Env) (proof : Proof) : Array Exp :=
  if env.task.metas.isEmpty then #[]
  else
    let all := allBindings proof
    env.task.metas.map fun m => makeProofTree.resolve all (Exp.ofVar m)

/-- The proofs that have reached the root: the first that the verifier accepts, as the
proof, its body, the goal as it is proved, and the values of the metavariables. -/
def takeRootProofs (accept : Env → ProofTree → Array Cond → Except String ByteArray) (env : Env) :
    Option (ProofTree × ByteArray × Exp × Array Exp) × Array (String × ProofTree) × Env := Id.run do
  let mut rejections := #[]
  for proof in env.rootProofs do
    let tree := makeProofTree env proof
    match accept env tree proof.conds with
    | .ok body =>
      return (some (tree, body, proof.expr, metaValues env proof), rejections, { env with rootProofs := #[] })
    | .error msg => rejections := rejections.push (msg, tree)
  return (none, rejections, { env with rootProofs := #[] })

/-- Is a limit of the search reached? -/
def over (env : Env) (limits : Limits) (now start : Nat) : Bool :=
  env.props.size > limits.maxProps || now - start > limits.maxMs || env.overBudget


/-- The searches that are running, by a number of their own, with the number of
assertion nodes each has. -/
initialize runningSizes : IO.Ref (Std.HashMap Nat Nat) ← IO.mkRef {}
initialize nextSearch : IO.Ref Nat ← IO.mkRef 0

/-- `over`, now; and while memory is short, for the largest search that is running (as
Russell's heap-aware budget, `25c4be54`): it gives up, as at a limit, and frees its
memory, and the others go on — or, when memory is very short, for every search. -/
def overNow (env : Env) (limits : Limits) (start : Nat) (sid : Nat) : IO Bool := do
  let size := env.props.size
  runningSizes.modify (·.insert sid size)
  if over env limits (← IO.monoMsNow) start then return true
  let level ← memoryLevel.get
  if level == 0 then return false
  if level ≥ 2 then return true
  let largest := (← runningSizes.get).fold (init := 0) fun m _ n => max m n
  return size ≥ largest

/-- `ruReverseJoin` for each of the new facts: the goal, then every subgoal it unifies
with, as long as the limits allow. -/
def joinFacts (env : Env) (facts : Array Nat) (limits : Limits) (start : Nat) (sid : Nat) : IO Env := do
  let mut env := env
  for f in facts do
    let (targets, env') ← (joinRoot f).run env
    env := env'
    for h in targets do
      if ← overNow env limits start sid then return env
      env := ((← (joinSubgoal f h).run env)).2
  return env

/-- `ruRunForwardWave`: every fact of the front is expanded, and the facts that this
makes are the new front. Nothing is done if the front is empty or has reached its limit.
Returns whether there is a front to go on with. -/
def forwardWave (env : Env) (limits : Limits) (start : Nat) (sid : Nat) : IO (Env × Bool) := do
  let some fwd := env.forward | return (env, false)
  if fwd.front.isEmpty || fwd.count ≥ limits.maxFacts then return (env, false)
  let front := fwd.front
  let mut env := { env with forward := some { fwd with front := #[] } }
  for f in front do
    for (id, pos) in forwardTriggers env f do
      if ← overNow env limits start sid then return (env, false)
      if ((env.forward.map (·.count)).getD 0) ≥ limits.maxFacts then break
      let (made, env') ← (applyForward f env.db.asserts[id]! pos limits.maxFacts).run env
      env ← joinFacts env' made limits start sid
  return (env, !((env.forward.map (·.front.isEmpty)).getD true))

/-- The search of `searchWith`; `sid` is its number among the searches that are running
(`runningSizes`). -/
partial def searchCore {σ : Type} (accept : Env → ProofTree → Array Cond → Except String ByteArray) (env : Env)
    (strategy : Strategy σ) (limits : Limits) (sid : Nat) : IO Result := do
  let start ← IO.monoMsNow
  -- a goal that is one of the premises needs no assertion; Russell's root is not matched
  -- with the premises. With metavariables: a goal that unifies with one.
  let direct := (env.premises.unify env.task.goal).filter fun u =>
    match strategy.root with
    | some (.premise j) => j == u.data
    | some (.assertion _) | some (.conv ..) => false
    | none => true
  for u in direct.qsort (·.data < ·.data) do
    if let .ok body := accept env (.hyp u.data) #[] then
      return { ending := .proved, proof := some (.hyp u.data), body := some body, answer := some u.expr,
               values := env.task.metas.map fun m => u.sub.apply (Exp.ofVar m), env }
  let mut env := { env with admitJoin := strategy.admitJoin, tupleBudget := limits.maxTuples, workBudget := limits.maxWork,
                             deadline := start + limits.maxMs }
  let mut rejected := 0
  let mut others := 0
  let mut rejection := ""
  let mut rejectedProof : Option ProofTree := none
  -- the forward front is seeded before the root is expanded (`ruSeedForwardFront`), and
  -- a seed may be the goal
  if strategy.forward then
    let (seeds, env') ← (seedForward limits.maxFacts).run env
    env ← joinFacts env' seeds limits start sid
    let (found, r, env') := takeRootProofs accept env
    env := env'
    others := others + (r.filter (·.1 == anotherProof)).size
    rejected := rejected + (r.filter (·.1 != anotherProof)).size
    if let some (tree, body, answer, values) := found then
      return { ending := .proved, proof := some tree, body := some body, answer := some answer, values, rejected, others, env }
  env := ((← (expandHyp 0 strategy.root).run env)).2
  let mut st := strategy.init
  -- a wave that leaves no front lets the strategy decide once more; two in a row end
  -- the search (`ruProveRec`)
  let mut dry := false
  while true do
    let (decision, st') := strategy.step env st
    st := st'
    match decision with
    | .done =>
      -- a join that the budget stopped leaves the tree without some of its proofs
      return { ending := if env.overBudget then .limit else .exhausted, rejected, rejection, rejectedProof, others, env }
    | .forward =>
      let (env', more) ← forwardWave env limits start sid
      env := env'
      let (found, r, env') := takeRootProofs accept env
      env := env'
      others := others + (r.filter (·.1 == anotherProof)).size
      rejected := rejected + (r.filter (·.1 != anotherProof)).size
      if let some (msg, tree) := (r.filter (·.1 != anotherProof)).back? then
        rejection := msg
        rejectedProof := some tree
      if let some (tree, body, answer, values) := found then
        return { ending := .proved, proof := some tree, body := some body, answer := some answer, values,
                 rejected, rejection, rejectedProof, others, env }
      if ← overNow env limits start sid then
        return { ending := .limit, rejected, rejection, rejectedProof, others, env }
      if more then dry := false
      else if !dry then dry := true
      else return { ending := .exhausted, rejected, rejection, rejectedProof, others, env }
    | .expand items =>
      dry := false
      env := env.dropExpanded
      for (p, only) in items do
        if env.props[p]!.expanded then continue
        if ← overNow env limits start sid then
          return { ending := .limit, rejected, rejection, rejectedProof, others, env }
        let (_, env') ← (proveProp p only).run env
        env := env'
        if !env.rootProofs.isEmpty then
          let (found, r, env') := takeRootProofs accept env
          env := env'
          others := others + (r.filter (·.1 == anotherProof)).size
          rejected := rejected + (r.filter (·.1 != anotherProof)).size
          if let some (msg, tree) := (r.filter (·.1 != anotherProof)).back? then
            rejection := msg
            rejectedProof := some tree
          if let some (tree, body, answer, values) := found then
            return { ending := .proved, proof := some tree, body := some body, answer := some answer, values,
                     rejected, rejection, rejectedProof, others, env }
  return { ending := if env.overBudget then .limit else .exhausted, rejected, rejection, rejectedProof, others, env }

/-- `ruProve`: searches for a proof of the task of `env` with a strategy. A proof that
reaches the root is given to `accept`, which says whether it counts. -/
def searchWith {σ : Type} (accept : Env → ProofTree → Array Cond → Except String ByteArray) (env : Env)
    (strategy : Strategy σ) (limits : Limits := {}) : IO Result := do
  let sid ← nextSearch.modifyGet fun n => (n, n + 1)
  try searchCore accept env strategy limits sid
  finally runningSizes.modify (·.erase sid)

/-- `searchWith` for a theorem of the file: a proof counts if the verifier accepts its
proof body. -/
def search {σ : Type} (vc : Verify.Ctx) (env : Env) (strategy : Strategy σ) (limits : Limits := {}) :
    IO Result :=
  searchWith (accept vc) env strategy limits

end Whitehead.Prove
