/-
The replay strategies as they were before they were composed of atoms
(`docs/DESIGN.md`, "Composable tactics"): `replay` and `rails` written each as one
strategy. They are kept here as the reference for the definitions `tactics/replay.tac`
and `tactics/rails.tac`, which must build the same trees (`Tactics.lean`).
-/
import Whitehead.Prove.Rails

open Whitehead.Prove

namespace Tests.Prove.Ref

/-- `replay` (Russell's `spr`): subproofs of earlier proofs put down at goals, `cfg.count`
of them at each, and followed step by step into their premises. When nothing is left to
follow, the goals not looked at yet are looked at, as `cfg.seeds` says; when no goal is
left, it is done. Unbounded on its own: within a `limited`, or a time. -/
def replay (rails : Rails) (cfg : ReplayConfig) (seeds : RailSeeds := .open) : Strategy ReplayState where
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
      let goals : Array Nat := match seeds with
        | .root => if st.started then #[] else #[0] ++ env.hints
        | .open => (Array.range (env.hyps.size - st.looked)).map (st.looked + ·) |>.filter fun h =>
            env.isBackwardGoal h && env.hyps[h]!.proofs.isEmpty
      for h in goals do
        if seeded.contains h then continue
        seeded := seeded.insert h
        for k in rails.at_ env h cfg do pending := pending.push (h, Fragment.indexed k)
      st := { st with seeded, looked := env.hyps.size, started := true, pending }
      if pending.isEmpty then return (.done, st)
      let (items', st'') := replayStep rails env st
      items := items'
      st := st''
    return (.expand (items.map (·, none)), st)


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
def rails (r : Rails) (cfg : RailsConfig) : Strategy RailsState where
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
        for k in r.at_ env h cfg.replay do pending := pending.push (h, Fragment.indexed k)
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


end Tests.Prove.Ref
