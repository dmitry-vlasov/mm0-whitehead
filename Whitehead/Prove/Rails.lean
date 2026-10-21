/-
The replay of subproofs: the fragments of existing proofs as guiding rails at a goal
(`docs/DESIGN.md`, "Phase 4", "Proof rails"). Russell's experiment is `spr`
(`russell-flow/src/ru/prover/tactics/subproof_replay.flow`, with `ruBuildStepIndex`
and `follow-proof`).

The index has one entry for each distinct subproof below a node of the proofs of the
file (`Subproofs.lean`): a pointer to it, keyed by the conclusion of its most general
lemma. A goal fits a subproof if it unifies with that conclusion. No lemma is added to
the database. A subproof is put down at a goal by a tactic that expands, at the goal,
the variant for its top assertion, and then, at the goal of each premise, the variant
for the subproof below that premise, by position.

Each step is an ordinary expansion. Every goal it makes is matched with the premises,
joined with the facts and the intermediate goals, and has all its other variants. So
any branch of a fragment can be left wherever something else proves it, and every
connected piece of the fragment is used, without being listed. Where the next step of a
fragment does not fit, because the goal has no variant for its assertion, that branch
of the replay ends.

Which subproofs are put down, and how many, is configured (`ReplayConfig`): how many at a
goal, by which rank, from what size, and from which proofs. Where they are put down is
`follow`'s (`FollowConfig`). The tactics `replay` and `rails` are definitions made of
`follow`, `search` and `first` (`tactics/*.tac`; `docs/DESIGN.md`, "Composable tactics").
-/
import Whitehead.Prove.Subproofs
import Whitehead.Prove.Cost
import Whitehead.Prove.Congr

namespace Whitehead.Prove

/-- The order of the subproofs that fit a goal. -/
inductive RailRank where
  /-- In the most proofs before the theorem first. -/
  | occurrences
  /-- The largest first. -/
  | size
  /-- The smallest first. -/
  | small
  /-- Those that leave the fewest hypotheses open first: put down at the goal, the
  hypotheses of a subproof's lemma that no premise of the theorem fits (the author's idea:
  from the goal to the premises in one step). A subproof with none open proves the goal. -/
  | reach
  /-- Those whose lemma's conclusion has the most nodes that are not variables first: the
  most specific to the goal, which they all fit. Then by occurrences. -/
  | specific
  /-- Those that occur in the latest proof before the theorem first. Then by occurrences. -/
  | recent
  deriving BEq, Inhabited, Repr

/-- Which subproofs may be put down for a theorem. -/
inductive RailSource where
  /-- Those that occur in a proof of a theorem before it. -/
  | earlier
  /-- Those that occur in two proofs of theorems before it. -/
  | recurring
  deriving BEq, Inhabited, Repr

/-- Where subproofs are put down. -/
inductive RailSeeds where
  /-- At the main goal and the intermediate goals. -/
  | root
  /-- At every goal node that is open when it is looked at, each once. -/
  | open
  deriving BEq, Inhabited, Repr

structure ReplayConfig where
  /-- How many subproofs are put down at a goal. -/
  count : Nat := 3
  rank : RailRank := .occurrences
  /-- The fewest steps of a subproof put down. -/
  minSize : Nat := 2
  source : RailSource := .earlier
  /-- Only subproofs that leave at most this many hypotheses open (see `RailRank.reach`). -/
  maxOpen : Nat := 1000000
  deriving Inhabited, Repr

structure Rails where
  sp : Subproofs
  /-- The conclusion of each subproof's most general lemma. -/
  concl : Array Exp
  /-- The hypotheses of each subproof's lemma: its leaves that are hypotheses. -/
  hyps : Array (Array Exp) := #[]
  /-- The conclusions that are not a bare variable, each ranked so that a theorem finds
  only the subproofs of the proofs before it. -/
  index : Index Nat
  /-- The congruence and reflexivity lemmas of the file, for the guide `congr`. -/
  congr : CongrTable := {}
  deriving Inhabited

namespace Rails

/-- The rails of the proofs of `db`. -/
def ofDb (db : Db) : Rails := Id.run do
  let sp := Subproofs.ofDb db
  let lemmas := sp.lemmas db
  let concl := lemmas.map fun l => (l.map (·.concl)).getD default
  let hyps := lemmas.map fun l => (l.map (·.hyps)).getD #[]
  let mut ix : Index Nat := {}
  for k in [1:sp.nodes.size] do
    if let some l := lemmas[k]! then
      if !l.concl.isVar then ix := ix.insert l.concl k (2 * sp.first[k]! + 2)
  return { sp, concl, hyps, index := ix, congr := CongrTable.ofDb db }

/-- How many hypotheses of subproof `k`'s lemma, put down at goal `goal`, no premise of
the theorem of `env` fits. A hypothesis is judged on its own, under the unifier of the
lemma's conclusion with the goal. -/
def openHyps (r : Rails) (env : Env) (goal : Exp) (k : Nat) : Nat := Id.run do
  -- the lemma's variables are its own numbers, below those of the tree
  let some sub := unifyExps #[goal, r.concl[k]!] {} | return r.hyps[k]!.size
  let mut n := 0
  for h in r.hyps[k]! do
    if (env.premises.unify (sub.applyAll h)).isEmpty then n := n + 1
  return n

/-- The subproofs that fit goal node `h` of the tree, as `cfg` chooses and orders them. -/
def at_ (r : Rails) (env : Env) (h : Nat) (cfg : ReplayConfig) : Array Nat := Id.run do
  let thm := env.task.limit
  let found := (r.index.unifyRaw env.hyps[h]!.expr (rankLimit thm)).map (·.data)
  let mut seen : Std.HashSet Nat := {}
  let mut ok := #[]
  for k in found do
    if seen.contains k then continue
    seen := seen.insert k
    if r.sp.sizes[k]! < cfg.minSize then continue
    if cfg.source == .recurring && r.sp.occBefore k thm < 2 then continue
    ok := ok.push k
  let occ (k : Nat) : Nat := r.sp.occBefore k thm
  let size (k : Nat) : Nat := r.sp.sizes[k]!
  -- the hypotheses each leaves open, when asked for
  let goal := env.hyps[h]!.expr
  let opens : Std.HashMap Nat Nat :=
    if cfg.rank == .reach || cfg.maxOpen < 1000000 then
      ok.foldl (init := {}) fun m k => m.insert k (r.openHyps env goal k)
    else {}
  let kept := if cfg.maxOpen < 1000000 then ok.filter fun k => (opens[k]?.getD 0) ≤ cfg.maxOpen else ok
  let op (k : Nat) : Nat := opens[k]?.getD 0
  let spec (k : Nat) : Nat := (r.concl[k]!.nodes.filter (!Node.isVar ·)).size
  -- the latest theorem before this one whose proof has it
  let latest (k : Nat) : Nat := match r.sp.occBefore k thm with
    | 0 => 0
    | n => r.sp.occ[k]![n - 1]!
  let byOcc (a b : Nat) : Bool := occ a > occ b || occ a == occ b && (size a > size b || size a == size b && a < b)
  let ordered := match cfg.rank with
    | .occurrences => kept.qsort fun a b => occ a > occ b || occ a == occ b && (size a > size b || size a == size b && a < b)
    | .size => kept.qsort fun a b => size a > size b || size a == size b && a < b
    | .small => kept.qsort fun a b => size a < size b || size a == size b && a < b
    | .reach => kept.qsort fun a b => op a < op b || op a == op b && (occ a > occ b || occ a == occ b && a < b)
    | .specific =>
      let sp := kept.foldl (init := ({} : Std.HashMap Nat Nat)) fun (m : Std.HashMap Nat Nat) k => m.insert k (spec k)
      kept.qsort fun a b => sp[a]! > sp[b]! || sp[a]! == sp[b]! && byOcc a b
    | .recent =>
      let lt := kept.foldl (init := ({} : Std.HashMap Nat Nat)) fun (m : Std.HashMap Nat Nat) k => m.insert k (latest k)
      kept.qsort fun a b => lt[a]! > lt[b]! || lt[a]! == lt[b]! && byOcc a b
  return ordered.extract 0 cfg.count

end Rails

/-- Is `h` a goal node of a backward tree: of the main goal's, or of an intermediate
goal's? -/
def Env.isBackwardGoal (env : Env) (h : Nat) : Bool := Id.run do
  let mut h := h
  for _ in [0:env.hyps.size] do
    if h == 0 || env.hints.contains h then return true
    match env.hyps[h]?.bind (·.parent) with
    | some p => h := env.props[p]!.parent
    | none => return false
  return false

/-- A fragment to follow: a subproof of the index, by its node; or a proof that a procedure
computed, as the assertions it applies and how they nest (`Skeleton`), a hypothesis leaf
being a goal it leaves open. -/
inductive Fragment where
  | indexed (k : Nat)
  | computed (sk : Skeleton)
  deriving Inhabited

/-- The top of a fragment: its assertion, and for each premise the fragment below, none
where it leaves the goal open. -/
def Rails.fragTop (rails : Rails) : Fragment → Option (Nat × Array (Option Fragment))
  | .indexed k =>
    let (a, kids) := rails.sp.nodes[k]!
    some (a, kids.map fun c => if c == 0 then none else some (.indexed c))
  | .computed (.step a cs) => some (a, cs.map fun c => match c with | .hyp _ => none | s => some (.computed s))
  | .computed (.hyp _) => none

/-- The state of a replay: the fragments to put down, each at a goal node; the assertion
nodes expanded in the last step, each with its fragment, whose premises come next; the
goal nodes looked at; and how far the goal nodes have been looked at. -/
structure ReplayState where
  pending : Array (Nat × Fragment) := #[]
  expanding : Array (Nat × Fragment) := #[]
  seeded : Std.HashSet Nat := {}
  looked : Nat := 0
  started : Bool := false
  deriving Inhabited

/-- One step of a replay: the premises of what was expanded, then each pending fragment's
top assertion at its goal. Returns the assertion nodes to expand and the state. -/
def replayStep (rails : Rails) (env : Env) (st : ReplayState) : Array Nat × ReplayState := Id.run do
  let mut pending := st.pending
  for (p, f) in st.expanding do
    let some (_, kids) := rails.fragTop f | continue
    let goals := env.props[p]!.children
    for i in [0:min kids.size goals.size] do
      if let some c := kids[i]! then pending := pending.push (goals[i]!, c)
  let mut items := #[]
  let mut expanding := #[]
  for (h, f) in pending do
    let some (a, _) := rails.fragTop f | continue
    -- the variant for the fragment's assertion; none: this branch of the fragment ends
    match env.hyps[h]!.children.find? fun p => env.props[p]!.step == .assertion a with
    | none => pure ()
    | some p =>
      if !env.props[p]!.expanded && !items.contains p then items := items.push p
      expanding := expanding.push (p, f)
  return (items, { st with pending := #[], expanding })

/-- Subproofs `pairs`, each put down at its goal node, and followed; then done. -/
def Strategy.replayFrom (rails : Rails) (pairs : Array (Nat × Nat)) : Strategy ReplayState where
  root := none
  init := { pending := pairs.map fun (h, k) => (h, .indexed k), started := true }
  step env st :=
    let (items, st) := replayStep rails env st
    if items.isEmpty && st.expanding.isEmpty then (.done, st) else (.expand (items.map (·, none)) .follow, st)

/-! ### Guides, and `follow` -/

/-- Where the proof fragments for a goal come from, for `follow`. -/
inductive Guide where
  /-- The subproofs of earlier proofs that fit the goal, as `cfg` chooses and orders
  them (`Rails.at_`). -/
  | subproofs (cfg : ReplayConfig)
  /-- The theorem's own proof, when it is a theorem of the file (`oracle` does the same
  from the proof's statements): for tests. -/
  | proof
  /-- Congruence: the goal `[ph ->] L = R` or `L <-> R` rewritten by the file's congruence
  lemmas down to where its sides differ (`Congr.lean`). -/
  | congr
  deriving Inhabited, Repr

/-- The fragments of guide `g` for goal node `h`. -/
def Guide.at_ (g : Guide) (r : Rails) (env : Env) (h : Nat) : Array Fragment :=
  match g with
  | .subproofs cfg => (r.at_ env h cfg).map .indexed
  | .proof => match r.sp.roots.find? (·.1 == env.task.limit) with
    | some (_, k) => #[.indexed k]
    | none => #[]
  | .congr => match r.congr.planGoal env.task.limit env.hyps[h]!.expr with
    | some sk => #[.computed sk]
    | none => #[]

/-- Where `follow` puts fragments down. -/
structure FollowConfig where
  guide : Guide := .proof
  /-- At the root and the intermediate goals, or at every open goal, each once. -/
  seeds : RailSeeds := .open
  /-- Only at goals with at most this many assertion nodes above them that `follow` did
  not expand. -/
  upto : Option Nat := none
  /-- Only at goals without variables: a goal with variables fits many more subproofs. -/
  ground : Bool := false
  /-- Also at the goals that a fragment left open. Without it, `follow` stays fair
  beside a search whose cost makes its steps free: fragments are not put down on one
  another without end. -/
  chain : Bool := false
  deriving Inhabited, Repr

/-- The state of `follow`: the replay; the marks of the nodes it expanded; the costs of
goal nodes, for `upto`. -/
structure FollowState where
  replay : ReplayState := {}
  marks : Marks := {}
  cost : Std.HashMap Nat Nat := {}
  deriving Inhabited

/-- `follow(g, ...)`: the fragments of guide `g`, put down at goals as `cfg` says, and
followed step by step into their premises; nothing else. Each step expands, at a goal,
the variant for the fragment's assertion there; a branch where the goal has no such
variant ends. When nothing is left to follow, the goals not looked at yet are looked at;
when none of them takes a fragment, it has nothing to expand (done; inside `first`,
asked again the next round). Its nodes are labelled `follow`. Russell's `follow-proof`,
over many fragments; with `subproofs`, its `spr`. -/
def Strategy.follow (r : Rails) (cfg : FollowConfig) : Strategy FollowState where
  root := none
  init := {}
  step env st := Id.run do
    let (items0, rs0) := replayStep r env st.replay
    let mut items := items0
    let mut rs := rs0
    let mut marks := st.marks
    let mut cost := st.cost
    -- nothing to follow: new goals to put fragments down at
    if items.isEmpty && rs.expanding.isEmpty then
      marks := marks.update env #[.follow]
      let goals : Array Nat := match cfg.seeds with
        | .root => if rs.started then #[] else #[0] ++ env.hints
        | .open => (Array.range (env.hyps.size - rs.looked)).map (rs.looked + ·)
      let mut pending := #[]
      let mut seeded := rs.seeded
      for h in goals do
        if !env.isBackwardGoal h || !env.hyps[h]!.proofs.isEmpty || seeded.contains h then continue
        if !cfg.chain && env.hyps[h]!.parent.any marks.props.contains then continue
        if cfg.ground && env.hyps[h]!.expr.hasVars then continue
        if let some u := cfg.upto then
          let (c, cost') := goalCost env marks 0 cost h
          cost := cost'
          if c > u then continue
        seeded := seeded.insert h
        for k in cfg.guide.at_ r env h do pending := pending.push (h, k)
      rs := { rs with seeded, looked := env.hyps.size, started := true, pending }
      let (items', rs') := replayStep r env rs
      items := items'
      rs := rs'
    -- what was expanded already, by something else: on to its premises
    while items.isEmpty && !rs.expanding.isEmpty do
      let (items', rs') := replayStep r env rs
      items := items'
      rs := rs'
    let st := { replay := rs, marks, cost }
    if items.isEmpty then return (.done, st)
    return (.expand (items.map (·, none)) .follow, st)

/-- How far subproofs `k` and `j` agree from the top: the steps they have in common,
the same assertion at the same place. -/
partial def Rails.agree (r : Rails) (k j : Nat) : Nat :=
  if k == 0 || j == 0 then 0
  else if k == j then r.sp.sizes[k]!
  else
    let (a, ks) := r.sp.nodes[k]!
    let (b, js) := r.sp.nodes[j]!
    if a != b then 0
    else 1 + (Array.range (min ks.size js.size)).foldl (init := 0) fun acc i => acc + r.agree ks[i]! js[i]!

/-- `loop(t, n)` (`ruLoopWhileProgressTactic`): `t` from its start again each time it is
done, while the tree grows, up to `n` times. -/
def Strategy.loop {σ : Type} (n : Nat) (s : Strategy σ) : Strategy (σ × Nat × Option Nat) where
  root := s.root
  init := (s.init, 0, none)
  step env st :=
    let (inner, it, start) := st
    let start := start.getD env.props.size
    match s.step env inner with
    | (.done, inner) =>
      if it + 1 < n && env.props.size > start then
        let (d, inner) := s.step env s.init
        (d, (inner, it + 1, some env.props.size))
      else (.done, (inner, it, some start))
    | (d, inner) => (d, (inner, it, some start))
  forward := s.forward
  admitJoin := s.admitJoin

namespace AnyStrategy

def loop (a : AnyStrategy) (n : Nat) : AnyStrategy := ⟨a.strategy.loop n⟩

end AnyStrategy

end Whitehead.Prove
