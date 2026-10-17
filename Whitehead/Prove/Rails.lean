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
goal, by which rank, from what size, from which proofs, and at which goals.
-/
import Whitehead.Prove.Subproofs
import Whitehead.Prove.Combinators

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
  seeds : RailSeeds := .open
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
  return { sp, concl, hyps, index := ix }

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
  let ordered := match cfg.rank with
    | .occurrences => kept.qsort fun a b => occ a > occ b || occ a == occ b && (size a > size b || size a == size b && a < b)
    | .size => kept.qsort fun a b => size a > size b || size a == size b && a < b
    | .small => kept.qsort fun a b => size a < size b || size a == size b && a < b
    | .reach => kept.qsort fun a b => op a < op b || op a == op b && (occ a > occ b || occ a == occ b && a < b)
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

/-- The state of a replay: the subproofs to put down, each at a goal node; the assertion
nodes expanded in the last step, each with its subproof, whose premises come next; the
goal nodes looked at; and how far the goal nodes have been looked at. -/
structure ReplayState where
  pending : Array (Nat × Nat) := #[]
  expanding : Array (Nat × Nat) := #[]
  seeded : Std.HashSet Nat := {}
  looked : Nat := 0
  started : Bool := false
  deriving Inhabited

/-- One step of a replay: the premises of what was expanded, then each pending subproof's
top assertion at its goal. Returns the assertion nodes to expand and the state. -/
def replayStep (rails : Rails) (env : Env) (st : ReplayState) : Array Nat × ReplayState := Id.run do
  let mut pending := st.pending
  for (p, k) in st.expanding do
    let kids := rails.sp.nodes[k]!.2
    let goals := env.props[p]!.children
    for i in [0:min kids.size goals.size] do
      if kids[i]! != 0 then pending := pending.push (goals[i]!, kids[i]!)
  let mut items := #[]
  let mut expanding := #[]
  for (h, k) in pending do
    let a := rails.sp.nodes[k]!.1
    -- the variant for the subproof's assertion; none: this branch of the fragment ends
    match env.hyps[h]!.children.find? fun p => env.props[p]!.step == .assertion a with
    | none => pure ()
    | some p =>
      if !env.props[p]!.expanded && !items.contains p then items := items.push p
      expanding := expanding.push (p, k)
  return (items, { st with pending := #[], expanding })

/-- `replay` (Russell's `spr`): subproofs of earlier proofs put down at goals, `cfg.count`
of them at each, and followed step by step into their premises. When nothing is left to
follow, the goals not looked at yet are looked at, as `cfg.seeds` says; when no goal is
left, it is done. Unbounded on its own: within a `limited`, or a time. -/
def Strategy.replay (rails : Rails) (cfg : ReplayConfig) : Strategy ReplayState where
  root := none
  init := {}
  step env st := Id.run do
    let (items0, st0) := replayStep rails env st
    let mut st := st0
    let mut items := items0
    -- nothing to follow: new goals to put subproofs down at
    while items.isEmpty && st.expanding.isEmpty do
      let mut pending := #[]
      let mut seeded := st.seeded
      let goals : Array Nat := match cfg.seeds with
        | .root => if st.started then #[] else #[0] ++ env.hints
        | .open => (Array.range (env.hyps.size - st.looked)).map (st.looked + ·) |>.filter fun h =>
            env.isBackwardGoal h && env.hyps[h]!.proofs.isEmpty
      for h in goals do
        if seeded.contains h then continue
        seeded := seeded.insert h
        for k in rails.at_ env h cfg do pending := pending.push (h, k)
      st := { st with seeded, looked := env.hyps.size, started := true, pending }
      if pending.isEmpty then return (.done, st)
      let (items', st'') := replayStep rails env st
      items := items'
      st := st''
    return (.expand (items.map (·, none)), st)

/-- Subproofs `pairs`, each put down at its goal node, and followed; then done. -/
def Strategy.replayFrom (rails : Rails) (pairs : Array (Nat × Nat)) : Strategy ReplayState where
  root := none
  init := { pending := pairs, started := true }
  step env st :=
    let (items, st) := replayStep rails env st
    if items.isEmpty && st.expanding.isEmpty then (.done, st) else (.expand (items.map (·, none)), st)

/-- Where `rails` puts subproofs down, besides what it replays. -/
structure RailsConfig where
  replay : ReplayConfig := {}
  /-- Only at goals of this cost or less (`Strategy.rails`). -/
  upto : Nat := 0
  /-- Only at goals without variables: a goal with variables fits many more subproofs. -/
  ground : Bool := true
  /-- What a goal that a subproof leaves open costs more than the goal it was put down
  at: 0 builds it up in the same round as that goal's other variants, more puts it later. -/
  penalty : Nat := 0
  deriving Inhabited, Repr

/-- The state of `rails`: the replay; the assertion nodes it expanded; and the cost of the
goal nodes, as far as it is known. -/
structure RailsState where
  replay : ReplayState := {}
  replayed : Std.HashSet Nat := {}
  /-- The goal nodes at which the replay expanded a variant: on a rail. -/
  onRail : Std.HashSet Nat := {}
  cost : Std.HashMap Nat Nat := {}
  /-- The depth of goal nodes: the number of assertion nodes above them. -/
  depth : Std.HashMap Nat Nat := {}
  deriving Inhabited

/-- The cost of goal node `h`: the number of assertion nodes above it that the replay did
not expand. The cost of an assertion node is that of its goal and one more, unless the
replay expanded it; a goal that a replayed node leaves open, where the replay went no
further (not `onRail`), costs `penalty` more. -/
partial def railCost (env : Env) (replayed onRail : Std.HashSet Nat) (penalty : Nat) (cost : Std.HashMap Nat Nat)
    (h : Nat) : Nat × Std.HashMap Nat Nat :=
  if let some c := cost[h]? then (c, cost)
  else match env.hyps[h]!.parent with
    | none => (0, cost.insert h 0)
    | some q =>
      let (c, cost) := railCost env replayed onRail penalty cost env.props[q]!.parent
      let c := if !replayed.contains q then c + 1 else if onRail.contains h then c else c + penalty
      (c, cost.insert h c)

/-- `rails`: the replay of subproofs combined with breadth-first search, by cost.
- **Cost:** a step that the replay takes costs nothing, and one that the search takes
  costs one. Each round expands the leaves of the least cost, so without subproofs this is
  breadth-first, round for round.
- **Rails first:** the goals that a subproof leaves open cost what the goal it was put
  down at costs, so they are built up in the same round as that goal's other variants.
  At a goal on the rail, where the replay took a step, the other variants are the
  alternatives to the rail: they cost the depth of the goal and one, as in breadth-first,
  so that a rail does not bring the variants of all its goals into the first rounds.
- **Where subproofs go down:** at the goals of cost `upto` or less (with `ground`, those
  without variables), `count` of them at each, as `ReplayConfig` says, and followed before
  the next round. Not at a goal that a replay opened: subproofs there would cost nothing
  as well, and could be put down on one another without end.
- **Completeness:** every leaf is reached in its turn, so nothing is lost. -/
def Strategy.rails (r : Rails) (cfg : RailsConfig) : Strategy RailsState where
  root := none
  init := {}
  step env st := Id.run do
    let mut st := st
    -- the replay, first: what it has to follow, then new goals to put subproofs down at
    let (items, rs) := replayStep r env st.replay
    let mut items := items
    let mut rs := rs
    if items.isEmpty && rs.expanding.isEmpty then
      let mut pending := #[]
      let mut seeded := rs.seeded
      let mut cost := st.cost
      for h in [rs.looked:env.hyps.size] do
        if !env.isBackwardGoal h || !env.hyps[h]!.proofs.isEmpty || seeded.contains h then continue
        -- a goal that a replay opened is built up, not given subproofs of its own: those
        -- would cost nothing too, and put down without end
        if (env.hyps[h]!.parent.any st.replayed.contains) then continue
        if cfg.ground && env.hyps[h]!.expr.hasVars then continue
        let (c, cost') := railCost env st.replayed st.onRail cfg.penalty cost h
        cost := cost'
        if c > cfg.upto then continue
        seeded := seeded.insert h
        for k in r.at_ env h cfg.replay do pending := pending.push (h, k)
      rs := { rs with seeded, looked := env.hyps.size, pending }
      st := { st with cost }
      let (items', rs') := replayStep r env rs
      items := items'
      rs := rs'
    -- what the replay follows without expanding: on to its premises in the next step
    while items.isEmpty && !rs.expanding.isEmpty do
      let (items', rs') := replayStep r env rs
      items := items'
      rs := rs'
    if !items.isEmpty then
      return (.expand (items.map (·, none)),
        { st with replay := rs, replayed := items.foldl (init := st.replayed) (·.insert ·),
                  onRail := items.foldl (init := st.onRail) fun s p => s.insert env.props[p]!.parent })
    -- a round of the search: the leaves of the least cost
    let mut cost := st.cost
    let mut depth := st.depth
    let mut best := none
    let mut round := #[]
    for p in env.leafs do
      if env.props[p]!.expanded then continue
      let h := env.props[p]!.parent
      let c ← if st.onRail.contains h then do
          let (d, depth') := railCost env {} {} 0 depth h
          depth := depth'
          pure d
        else do
          let (c, cost') := railCost env st.replayed st.onRail cfg.penalty cost h
          cost := cost'
          pure c
      match best with
      | none =>
        best := some c
        round := #[p]
      | some b =>
        if c < b then
          best := some c
          round := #[p]
        else if c == b then round := round.push p
    st := { st with replay := rs, cost, depth }
    if round.isEmpty then return (.done, st)
    return (.expand (round.map (·, none)), st)

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
