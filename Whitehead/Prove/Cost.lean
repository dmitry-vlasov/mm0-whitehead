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
  /-- By a learned model's score, the highest first (`Model.lean`). With a `cheap` model,
  in two stages: the cheap one, of the features that need no instantiation of the variant's
  new goals, scores all the variants, and `m` the first `top` of them only; the rest keep
  the cheap order (`docs/DESIGN.md`, "Where the time goes"). -/
  | learned (m : Model) (cheap : Option Model := none) (top : Nat := 64)
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
  only grows with the depth.

  With a `value` (a model of goals and a scale `K`, with a rank), a step that is not free
  also costs its value term: K·Σ −ln V(g), rounded, over its new goals g, V the model's
  probability that g is proved (at least 1/1000), less that of the best of its goal's
  first variants (`valueOf`). A leaf pays for its own new goals and for the steps above
  it. With `absolute`, the term itself, not its excess over the goal's best: then a leaf
  pays for how hard all the goals on its way look, which compares the leaves across the
  tree, but makes a long proof costly however good each of its steps is (mm0's
  congruences, `docs/DESIGN.md`, step 4). Still fair: the term is not negative. With a
  `cap` above 0, a step's value term is at most `cap`: the value reorders the steps within
  that many levels of cost and never puts one out of reach — a model trained on short
  searches calls unlikely what a longer one proves (`DESIGN.md`, "The value at 5 s"). -/
  | depth (free : Array Label := #[]) (penalty : Nat := 0) (rank : Option VariantRank := none)
      (width : Nat := 0) (value : Option (Model × Nat) := none) (absolute : Bool := false)
      (cap : Nat := 0)
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
      | .learned m cheap top =>
        let st := stats.getD (SymbolStats.ofDb env.db)
        let gi := env.goalInfo env.props[p]!.parent
        let order (qs : Array Nat) (model : Model) (cheaply : Bool) : Array Nat :=
          let scores := qs.foldl (init := ({} : Std.HashMap Nat Float)) fun (acc : Std.HashMap Nat Float) q =>
            acc.insert q (model.score (env.variantFeatures st gi q cheaply))
          qs.qsort fun a b => scores[a]! > scores[b]! || scores[a]! == scores[b]! && a < b
        match cheap with
        | some c =>
          if kids.size ≤ top then order kids m false
          else
            -- the cheap model orders all the variants, the full one the first `top`
            let first := order kids c true
            order (first.extract 0 top) m false ++ first.extract top first.size
        | none => order kids m false
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
    if let .learned .. := rank then
      if stats.isNone then stats := some (SymbolStats.ofDb env.db)
    let mut of := pl.of
    for i in [0:sorted.size] do of := of.insert sorted[i]! i
    return (of[p]?.getD 0, { of, stats })

/-- The place of assertion node `p` for its cost: its place by `rank`, but at most `width`
for a variant without premises at a goal without metavariables, which proves its goal at
once if it applies at all: such a step costs at most one more than the rank's first. On
the compiler's theorems a learned rank put one-step proofs out of reach; putting them all
first instead floods the rounds where there are many (mm0's numerals) (`docs/DESIGN.md`,
"The learned ranking layer"). At a goal with metavariables such a step only binds them,
and every assertion without premises fits a bare one: at `?0` of `ASTIOeq1d` 3,351 of
them came at once, so there they keep their place. -/
def placeOf (env : Env) (pl : Places) (rank : VariantRank) (width p : Nat) : Nat × Places :=
  let (r, pl) := pl.get env rank p
  if env.props[p]!.rule.hyps.isEmpty && !env.hyps[env.props[p]!.parent]!.expr.hasVars then (min r width, pl)
  else (r, pl)

/-- The value terms of assertion nodes (`Cost.depth`), as far as they are found: they
depend on the node's new goals alone, which do not change. -/
structure Values where
  of : Std.HashMap Nat Nat := {}
  /-- For a goal node, what its variants without premises cost (`valueOf`). -/
  first : Std.HashMap Nat Nat := {}
  task : Option TaskInfo := none
  deriving Inhabited

/-- The value term of assertion node `q`: `scale` times Σ −ln V(g) over its new goals g,
rounded; `stats` are the file's symbols. -/
def Values.get (vs : Values) (env : Env) (stats : SymbolStats) (m : Model) (scale q : Nat) : Nat × Values :=
  if let some v := vs.of[q]? then (v, vs)
  else
    let ti := vs.task.getD (env.taskInfo stats)
    let depth := env.goalDepth env.props[q]!.parent + 1
    let goals := (env.propView q).goals.get
    let s := (Array.range goals.size).foldl (init := 0) fun acc i =>
      let siblings := (Array.range goals.size).filterMap fun j => if j == i then none else some goals[j]!
      acc - Float.log (max 0.001 (m.value (env.goalFeatures stats ti goals[i]! depth siblings)))
    let v := (scale.toFloat * s).round.toUInt64.toNat
    (v, { vs with of := vs.of.insert q v, task := some ti })

/-- The value term of assertion node `q`, if the cost has a value (`Cost.depth`): its
`Values.get` less that of the best of its goal's first `width` variants with premises —
or, with `absolute`, itself. The file's symbols are those of the places, found here if a
rank has not found them.

A step without premises has no new goals, and costs what that best variant costs: with
`absolute`, nothing would put it after the steps that leave goals, as the rank alone does
(`placeOf`). -/
def valueOf (env : Env) (value : Option (Model × Nat)) (absolute : Bool) (cap : Nat) (rank : VariantRank) (width : Nat)
    (pl : Places) (vs : Values) (q : Nat) : Nat × Places × Values := Id.run do
  let some (m, scale) := value | return (0, pl, vs)
  let capped (t : Nat) : Nat := if cap > 0 then min t cap else t
  let stats := pl.stats.getD (SymbolStats.ofDb env.db)
  let mut pl := { pl with stats := some stats }
  let mut vs := vs
  let h := env.props[q]!.parent
  -- what the best of the goal's first variants with premises costs
  let first ← match vs.first[h]? with
    | some v => pure v
    | none => do
      -- the variants with premises of the first bucket that has any
      let mut firsts : Array (Nat × Nat) := #[]
      for k in env.hyps[h]!.children do
        if env.props[k]!.rule.hyps.isEmpty then continue
        let (r, pl') := pl.get env rank k
        pl := pl'
        firsts := firsts.push (r / width, k)
      let bucket := firsts.foldl (init := none) fun b (r, _) => some (b.elim r (min r))
      let mut best : Option Nat := none
      for (r, k) in firsts do
        if some r != bucket then continue
        let (v, vs') := vs.get env stats m scale k
        vs := vs'
        best := some (best.elim v (min v))
      vs := { vs with first := vs.first.insert h (best.getD 0) }
      pure (best.getD 0)
  if env.props[q]!.rule.hyps.isEmpty then return (capped (if absolute then first else 0), pl, vs)
  let (v, vs') := vs.get env stats m scale q
  return (capped (if absolute then v else v - min v first), pl, vs')

/-- `goalCost` with the steps ranked: a step that is not free costs one and its place by
`rank`, divided by `width`, and its value term. -/
partial def rankedCost (env : Env) (m : Marks) (penalty : Nat) (rank : VariantRank) (width : Nat)
    (value : Option (Model × Nat)) (absolute : Bool) (cap : Nat) (st : Std.HashMap Nat Nat × Places × Values) (h : Nat) :
    Nat × (Std.HashMap Nat Nat × Places × Values) :=
  if let some c := st.1[h]? then (c, st)
  else match env.hyps[h]!.parent with
    | none => (0, (st.1.insert h 0, st.2))
    | some q =>
      let (c, (memo, pl, vs)) := rankedCost env m penalty rank width value absolute cap st env.props[q]!.parent
      let (r, pl) := placeOf env pl rank width q
      if !m.props.contains q then
        let (v, pl, vs) := valueOf env value absolute cap rank width pl vs q
        let c := c + 1 + r / width + v
        (c, (memo.insert h c, pl, vs))
      else
        let c := if m.goals.contains h then c else c + penalty
        (c, (memo.insert h c, pl, vs))

/-- The state of `search`: the marks of its cost's labels, the costs and depths of goal
nodes, as far as they are known, and the places of the variants, for a rank. -/
structure SearchState where
  marks : Marks := {}
  cost : Std.HashMap Nat Nat := {}
  depth : Std.HashMap Nat Nat := {}
  places : Places := {}
  values : Values := {}
  deriving Inhabited

/-- `search(c)`: each round, the unexpanded leaves of the least cost `c`; done when there
is none. With `depth`, breadth-first round for round, on a tree without intermediate
goals (whose leaves would cost less, and come first). -/
def Strategy.search (c : Cost) : Strategy SearchState where
  root := none
  init := {}
  step env st := Id.run do
    let .depth free penalty rank width value absolute cap := c
    match rank.filter fun _ => width > 0 with
    | some rank =>
      let marks := st.marks.update env free
      let mut memo := (st.cost, st.places, st.values)
      let mut best : Option Nat := none
      let mut round := #[]
      -- the leaves by the cost of their goal, which is known: a leaf's own terms (its
      -- place, and its value) are found only for those that can still be the least, the
      -- cheapest goals first. The place of a leaf ranks all the variants of its goal, so
      -- this is where the search spends its time (`docs/DESIGN.md`, "Where the time goes"):
      -- the goals of the frontier, whose variants are never reached, are not ranked at all
      let mut byBase : Std.HashMap Nat (Array Nat) := {}
      for p in env.leafs do
        if env.props[p]!.expanded then continue
        let h := env.props[p]!.parent
        let (k, (cost, pl, vs)) := rankedCost env marks penalty rank width value absolute cap memo h
        memo := (cost, pl, vs)
        byBase := byBase.alter k fun ps => some ((ps.getD #[]).push p)
      for k in (byBase.toArray.map (·.1)).qsort (· < ·) do
        if best.any (· < k) then break
        for p in byBase[k]! do
          let (cost, pl, vs) := memo
          let (r, pl) := placeOf env pl rank width p
          let t := k + r / width
          -- the value only where the place leaves the leaf in the running
          let (v, pl, vs) := if best.any (· < t) then (0, pl, vs) else valueOf env value absolute cap rank width pl vs p
          memo := (cost, pl, vs)
          let t := t + v
          match best with
          | none =>
            best := some t
            round := #[p]
          | some b =>
            if t < b then
              best := some t
              round := #[p]
            else if t == b then round := round.push p
      let st := { st with marks, cost := memo.1, places := memo.2.1, values := memo.2.2 }
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
