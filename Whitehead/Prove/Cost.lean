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
import Whitehead.Prove.Combinators

namespace Whitehead.Prove

/-- The order of the leaves for `search`. -/
inductive Cost where
  /-- The number of assertion nodes above a leaf's goal. Those with a label of `free`
  cost nothing; at a goal where such a node hangs, the other variants are the
  alternatives to it and cost the goal's full depth; and a goal that such a node left
  open, where none hangs, costs `penalty` more. With `free` empty, the depth. -/
  | depth (free : Array Label := #[]) (penalty : Nat := 0)
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

/-- The state of `search`: the marks of its cost's labels, and the costs and depths of
goal nodes, as far as they are known. -/
structure SearchState where
  marks : Marks := {}
  cost : Std.HashMap Nat Nat := {}
  depth : Std.HashMap Nat Nat := {}
  deriving Inhabited

/-- `search(c)`: each round, the unexpanded leaves of the least cost `c`; done when there
is none. With `depth`, breadth-first round for round, on a tree without intermediate
goals (whose leaves would cost less, and come first). -/
def Strategy.search (c : Cost) : Strategy SearchState where
  root := none
  init := {}
  step env st := Id.run do
    match c with
    | .depth free penalty =>
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
      let st := { marks, cost, depth }
      if round.isEmpty then return (.done, st)
      return (.expand (round.map (·, none)), st)

end Whitehead.Prove
