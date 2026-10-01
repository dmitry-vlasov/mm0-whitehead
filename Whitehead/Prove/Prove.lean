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
  | done

/-- `RuProverTactic`. A strategy has a state of its own and reads the tree; it does not
change it. -/
structure Strategy (σ : Type) where
  /-- The restriction for the root, if any. -/
  root : Option Only
  init : σ
  step : Env → σ → Decision × σ

/-- `ruBreadthFirstTactic` (`tactics/breadth_first.flow`): all leaves, round by round.
This is the fair strategy of the completeness theorem. -/
def breadthFirst : Strategy Unit where
  root := none
  init := ()
  step env _ :=
    let leafs := env.leafs.filter fun p => !env.props[p]!.expanded
    if leafs.isEmpty then (.done, ()) else (.expand (leafs.map fun p => (p, none)), ())

/-- The state of `oracle`: the assertion nodes expanded in the last round, each with the
step of the known proof that it stands for. -/
structure OracleState where
  started : Bool := false
  expanded : Array (Nat × Skeleton) := #[]

/-- Replay of a known proof (after `tactics/oracle.flow`): at every expression node only
the assertion that the known proof uses there is expanded, and a premise only where the
known proof uses that premise. The expressions of the known proof are not used. -/
def oracle (skel : Skeleton) : Strategy OracleState where
  root := match skel with
    | .step t _ => some (.assertion t)
    | .hyp k => some (.premise k)
  init := {}
  step env st :=
    -- the assertion nodes that the last round made for the steps of the known proof
    let matching (h : Nat) (s : Skeleton) : Array (Nat × Skeleton) :=
      match s with
      | .step t _ => env.hyps[h]!.children.filterMap fun p =>
          if env.props[p]!.assertion == t && !env.props[p]!.expanded then some (p, s) else none
      | .hyp _ => #[]
    let next : Array (Nat × Skeleton) :=
      if !st.started then matching 0 skel
      else st.expanded.foldl (init := #[]) fun acc (p, s) =>
        match s with
        | .step _ children =>
          let hyps := env.props[p]!.children
          (Array.range hyps.size).foldl (init := acc) fun acc i => acc ++ matching hyps[i]! children[i]!
        | .hyp _ => acc
    if next.isEmpty then (.done, { st with started := true })
    else
      let items := next.map fun (p, s) =>
        match s with
        | .step _ children => (p, some (children.map fun c =>
            match c with
            | .step t _ => Only.assertion t
            | .hyp k => Only.premise k))
        | .hyp _ => (p, none)
      (.expand items, { started := true, expanded := next })

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
    let acc := db.asserts[a]!.disjs.foldl (init := acc) fun acc (x, v) =>
      let ex := args[x]!
      if ex.isVar then
        args[v]!.nodes.foldl (init := acc) fun acc n =>
          if Node.isVar n && n != ex.nodes[0]! then acc.push (ex.nodes[0]!, n) else acc
      else acc
    children.foldl (init := acc) fun acc c => nameConflicts db c acc

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
file, such as a goal with variables to be found. -/
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

structure Result where
  ending : Ending
  proof : Option ProofTree := none
  /-- The proof body, with its `END`. -/
  body : Option ByteArray := none
  /-- The goal as it was proved: with the variables it had replaced by what the proof
  needs them to be. Variables that the proof leaves open are still there. -/
  answer : Option Exp := none
  /-- The proofs that reached the root and were not accepted by the verifier, and what
  it said about the last of them. -/
  rejected : Nat := 0
  rejection : String := ""
  /-- The last proof that was rejected. -/
  rejectedProof : Option ProofTree := none
  env : Env

/-- The proofs that have reached the root: the first that the verifier accepts. -/
def takeRootProofs (accept : Env → ProofTree → Array Cond → Except String ByteArray) (env : Env) :
    Option (ProofTree × ByteArray × Exp) × Array (String × ProofTree) × Env := Id.run do
  let mut rejections := #[]
  for proof in env.rootProofs do
    let tree := makeProofTree env proof
    match accept env tree proof.conds with
    | .ok body => return (some (tree, body, proof.expr), rejections, { env with rootProofs := #[] })
    | .error msg => rejections := rejections.push (msg, tree)
  return (none, rejections, { env with rootProofs := #[] })

/-- `ruProve`: searches for a proof of the task of `env` with a strategy. A proof that
reaches the root is given to `accept`, which says whether it counts. -/
partial def searchWith {σ : Type} (accept : Env → ProofTree → Array Cond → Except String ByteArray) (env : Env)
    (strategy : Strategy σ) (limits : Limits := {}) : IO Result := do
  let start ← IO.monoMsNow
  -- a goal that is one of the premises needs no assertion; Russell's root is not matched
  -- with the premises
  if let some k := env.task.premises.findIdx? (· == env.task.goal) then
    let allowed := match strategy.root with
      | some (.premise j) => j == k
      | some (.assertion _) => false
      | none => true
    if allowed then
      if let .ok body := accept env (.hyp k) #[] then
        return { ending := .proved, proof := some (.hyp k), body := some body, answer := some env.task.goal, env }
  let (_, env) := (expandHyp 0 strategy.root).run env
  let mut env := env
  let mut st := strategy.init
  let mut rejected := 0
  let mut rejection := ""
  let mut rejectedProof : Option ProofTree := none
  while true do
    let (decision, st') := strategy.step env st
    st := st'
    match decision with
    | .done => return { ending := .exhausted, rejected, rejection, rejectedProof, env }
    | .expand items =>
      env := env.dropExpanded
      for (p, only) in items do
        if env.props[p]!.expanded then continue
        if env.props.size > limits.maxProps || (← IO.monoMsNow) - start > limits.maxMs then
          return { ending := .limit, rejected, rejection, rejectedProof, env }
        let (_, env') := (proveProp p only).run env
        env := env'
        if !env.rootProofs.isEmpty then
          let (found, r, env') := takeRootProofs accept env
          env := env'
          rejected := rejected + r.size
          if let some (msg, tree) := r.back? then
            rejection := msg
            rejectedProof := some tree
          if let some (tree, body, answer) := found then
            return { ending := .proved, proof := some tree, body := some body, answer := some answer,
                     rejected, rejection, rejectedProof, env }
  return { ending := .exhausted, rejected, rejection, rejectedProof, env }

/-- `searchWith` for a theorem of the file: a proof counts if the verifier accepts its
proof body. -/
def search {σ : Type} (vc : Verify.Ctx) (env : Env) (strategy : Strategy σ) (limits : Limits := {}) :
    IO Result :=
  searchWith (accept vc) env strategy limits

end Whitehead.Prove
