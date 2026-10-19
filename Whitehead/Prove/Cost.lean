/-
The order of a search: costs of the leaves, and `search`, which each round expands the
leaves of the least cost (`docs/DESIGN.md`, "Phase 4", "Composable tactics").

A cost reads the tree and its labels (`Env.labels`), and nothing of another strategy's
state: what an atom did, as `follow` the steps it took, the cost reads off the tree. So
`rails` is `first(follow(...), search(depth(follow)))`, two atoms in one order.

`search` is complete when its cost is fair: for every N, only finitely many leaves cost
N or less. `depth` is; `depth(follow)` too, since each fragment that `follow` follows is
finite, and without its `chain` no fragment is put down at a goal that one left open.
-/
import Whitehead.Prove.Model

namespace Whitehead.Prove

/-- An order of the variants of a goal, by the proofs of the theorems before the one
being proved (`Uses.lean`). -/
inductive VariantRank where
  /-- By how many proofs use the assertion, the most first. -/
  | used
  /-- By the latest proof that uses the assertion, the latest first; then by uses. -/
  | recent
  /-- By a learned model's score, the highest first (`Model.lean`). -/
  | learned (m : Model)
  deriving Inhabited, Repr

/-- The order of the leaves for `search`. -/
inductive Cost where
  /-- The number of assertion nodes above a leaf's goal. Those with a label of `free`
  cost nothing; at a goal where such a node hangs, the other variants are the
  alternatives to it and cost the goal's full depth; and a goal that such a node left
  open, where none hangs, costs `penalty` more. With `free` empty, the depth.

  With a rank and a `width`, a step costs one and its place among the variants of its
  goal by the rank, from 0, divided by `width`: the first `width` variants nothing more,
  the next `width` one more, and so on (a search by discrepancies). Still fair: a cost
  only grows with the depth. -/
  | depth (free : Array Label := #[]) (penalty : Nat := 0) (rank : Option VariantRank := none)
      (width : Nat := 0)
  deriving Inhabited, Repr

/-- The nodes with one of a set of labels, kept up to date as the tree grows: the
assertion nodes, the goal nodes where they hang, and how far `Env.labels` was read. -/
structure Marks where
  props : Std.HashSet Nat := {}
  goals : Std.HashSet Nat := {}
  seen : Nat := 0
  deriving Inhabited

/-- `m` with the labels of `env` that it has not read yet. -/
def Marks.update (m : Marks) (env : Env) (labels : Array Label) : Marks := Id.run do
  if m.seen == env.labels.size then return m
  let mut props := m.props
  let mut goals := m.goals
  for i in [m.seen:env.labels.size] do
    let (p, l) := env.labels[i]!
    if labels.contains l then
      props := props.insert p
      goals := goals.insert env.props[p]!.parent
  return { props, goals, seen := env.labels.size }

/-- The cost of goal node `h`: the number of assertion nodes above it, those of `m`
free; a goal that a node of `m` left open, where none of `m` hangs, `penalty` more. The
costs found are kept in `memo`: what is above a goal does not change. -/
partial def goalCost (env : Env) (m : Marks) (penalty : Nat) (memo : Std.HashMap Nat Nat) (h : Nat) :
    Nat × Std.HashMap Nat Nat :=
  if let some c := memo[h]? then (c, memo)
  else match env.hyps[h]!.parent with
    | none => (0, memo.insert h 0)
    | some q =>
      let (c, memo) := goalCost env m penalty memo env.props[q]!.parent
      let c := if !m.props.contains q then c + 1 else if m.goals.contains h then c else c + penalty
      (c, memo.insert h c)

/-- The places of assertion nodes among the variants of their goals, from 0, by a rank;
those of a goal's variants are found together, the first time one is asked for. -/
structure Places where
  of : Std.HashMap Nat Nat := {}
  /-- For a learned rank, the file's symbols, counted once. -/
  stats : Option SymbolStats := none
  deriving Inhabited

/-- The place of assertion node `p` among the variants of its goal, by `rank`. -/
def Places.get (pl : Places) (env : Env) (rank : VariantRank) (p : Nat) : Nat × Places :=
  if let some r := pl.of[p]? then (r, pl)
  else Id.run do
    let kids := env.hyps[env.props[p]!.parent]!.children
    let uses (q : Nat) : Nat := match env.props[q]!.step with
      | .assertion a => env.uses.before a env.task.limit
      | .conv .. => 0
    let latest (q : Nat) : Nat := match env.props[q]!.step with
      | .assertion a => env.uses.latest a env.task.limit
      | .conv .. => 0
    let mut stats := pl.stats
    let sorted := match rank with
      | .learned m =>
        let st := stats.getD (SymbolStats.ofDb env.db)
        let gi := env.goalInfo env.props[p]!.parent
        let scores := kids.foldl (init := ({} : Std.HashMap Nat Float)) fun (acc : Std.HashMap Nat Float) q =>
          acc.insert q (m.score (env.variantFeatures st gi q))
        kids.qsort fun a b => scores[a]! > scores[b]! || scores[a]! == scores[b]! && a < b
      | _ =>
        let key (q : Nat) : Nat × Nat := match rank with
          | .used => (uses q, 0)
          | _ => (latest q, uses q)
        let keys := kids.foldl (init := ({} : Std.HashMap Nat (Nat × Nat))) fun (m : Std.HashMap Nat (Nat × Nat)) q =>
          m.insert q (key q)
        kids.qsort fun a b =>
          let (a1, a2) := keys[a]!
          let (b1, b2) := keys[b]!
          a1 > b1 || a1 == b1 && (a2 > b2 || a2 == b2 && a < b)
    if let .learned _ := rank then
      if stats.isNone then stats := some (SymbolStats.ofDb env.db)
    let mut of := pl.of
    for i in [0:sorted.size] do of := of.insert sorted[i]! i
    return (of[p]?.getD 0, { of, stats })

/-- The place of assertion node `p` for its cost: its place by `rank`, but at most `width`
for a variant without premises, which proves its goal at once if it applies at all: such
a step costs at most one more than the rank's first. On the compiler's theorems a learned
rank put one-step proofs out of reach; putting them all first instead floods the rounds
where there are many (mm0's numerals) (`docs/DESIGN.md`, "The learned ranking layer"). -/
def placeOf (env : Env) (pl : Places) (rank : VariantRank) (width p : Nat) : Nat × Places :=
  let (r, pl) := pl.get env rank p
  if env.props[p]!.rule.hyps.isEmpty then (min r width, pl) else (r, pl)

/-- `goalCost` with the steps ranked: a step that is not free costs one and its place by
`rank`, divided by `width`. -/
partial def rankedCost (env : Env) (m : Marks) (penalty : Nat) (rank : VariantRank) (width : Nat)
    (st : Std.HashMap Nat Nat × Places) (h : Nat) : Nat × (Std.HashMap Nat Nat × Places) :=
  if let some c := st.1[h]? then (c, st)
  else match env.hyps[h]!.parent with
    | none => (0, (st.1.insert h 0, st.2))
    | some q =>
      let (c, (memo, pl)) := rankedCost env m penalty rank width st env.props[q]!.parent
      let (r, pl) := placeOf env pl rank width q
      let c := if !m.props.contains q then c + 1 + r / width else if m.goals.contains h then c else c + penalty
      (c, (memo.insert h c, pl))

/-- The state of `search`: the marks of its cost's labels, the costs and depths of goal
nodes, as far as they are known, and the places of the variants, for a rank. -/
structure SearchState where
  marks : Marks := {}
  cost : Std.HashMap Nat Nat := {}
  depth : Std.HashMap Nat Nat := {}
  places : Places := {}
  deriving Inhabited

/-- `search(c)`: each round, the unexpanded leaves of the least cost `c`; done when there
is none. With `depth`, breadth-first round for round, on a tree without intermediate
goals (whose leaves would cost less, and come first). -/
def Strategy.search (c : Cost) : Strategy SearchState where
  root := none
  init := {}
  step env st := Id.run do
    let .depth free penalty rank width := c
    match rank.filter fun _ => width > 0 with
    | some rank =>
      let marks := st.marks.update env free
      let mut memo := (st.cost, st.places)
      let mut best : Option Nat := none
      let mut round := #[]
      for p in env.leafs do
        if env.props[p]!.expanded then continue
        let h := env.props[p]!.parent
        let (k, memo') := rankedCost env marks penalty rank width memo h
        let (r, pl) := placeOf env memo'.2 rank width p
        memo := (memo'.1, pl)
        let k := k + r / width
        match best with
        | none =>
          best := some k
          round := #[p]
        | some b =>
          if k < b then
            best := some k
            round := #[p]
          else if k == b then round := round.push p
      let st := { st with marks, cost := memo.1, places := memo.2 }
      if round.isEmpty then return (.done, st)
      return (.expand (round.map (·, none)), st)
    | none =>
      let marks := st.marks.update env free
      let mut cost := st.cost
      let mut depth := st.depth
      let mut best : Option Nat := none
      let mut round := #[]
      for p in env.leafs do
        if env.props[p]!.expanded then continue
        let h := env.props[p]!.parent
        let k ← if marks.goals.contains h then do
            let (d, depth') := goalCost env {} 0 depth h
            depth := depth'
            pure d
          else do
            let (k, cost') := goalCost env marks penalty cost h
            cost := cost'
            pure k
        match best with
        | none =>
          best := some k
          round := #[p]
        | some b =>
          if k < b then
            best := some k
            round := #[p]
          else if k == b then round := round.push p
      let st := { st with marks, cost, depth }
      if round.isEmpty then return (.done, st)
      return (.expand (round.map (·, none)), st)

end Whitehead.Prove
