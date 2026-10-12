/-
Unifying the substitutions of many tuples at once: a port of
`russell-flow/src/ru/unify/prod.flow` (`ruUnifySubsProd`) and of
`src/ru/unify/indexes.flow` (`ruUnifyIndexes`).

`addProof` has, for each premise of an assertion, a set of proofs, and wants the tuples,
one proof from each set, whose substitutions unify. Walking the product tuple by tuple
is hopeless when the sets are large, and nearly every tuple fails: the paper says so in
its last section, and a profile of a search with joins had 1.3 million tuples of which
0.8% unified.

The way out is to look at one variable at a time. For a variable, each set gives the
expressions that its proofs put for it; these go into an index per set, each expression
with the proofs that have it. `unifyIndexes` walks all these indexes together and
returns the ways to take one expression from each so that they unify, each way with the
proofs it stands for. Only tuples that pass for every variable can unify, so the results
for the variables are intersected, and the substitutions are unified for what is left.

`unifyIndexes` is `unifyAt` of `Index.lean` with several indexes instead of one
expression and one index: where all have an application of the same term the walk goes
into the arguments; where some have a variable, the subexpressions that the others have
there are unified among themselves and the variable is bound to the result.
-/
import Whitehead.Prove.Index

namespace Whitehead.Prove

/-- `RuSubIndex`: where the walk is in one of the indexes: in the subexpression that
starts at node `start`, at node `curr`. -/
structure SubIndex where
  ix : Nat
  start : Nat
  curr : Nat
  deriving Inhabited

/-- `RuUnifiyIndexesRet`: for each index the node where its expression ends, the
unifier, and the unified expression. -/
structure IndexesRet where
  vect : Array Nat
  sub : Subst
  expr : Exp
  deriving Inhabited

/-- The first `cap + 1` tuples of `sets` (all, if there are fewer), made one at a time in
the order of `tuples`: a product can be far too large to be made whole. -/
def tuplesUpTo {α : Type} [Inhabited α] (sets : Array (Array α)) (cap : Nat) : Array (Array α) := Id.run do
  if sets.any (·.isEmpty) then return #[]
  let mut picks : Array Nat := Array.replicate sets.size 0
  let mut out : Array (Array α) := #[]
  while out.size ≤ cap do
    out := out.push ((Array.range sets.size).map fun i => sets[i]![picks[i]!]!)
    -- the next tuple: the last place moves fastest
    let mut i := sets.size
    let mut carry := true
    while carry && i > 0 do
      i := i - 1
      if picks[i]! + 1 < sets[i]!.size then
        picks := picks.set! i (picks[i]! + 1)
        carry := false
      else picks := picks.set! i 0
    if carry then break
  return out

/-- All ways to take one element from each of the arrays. -/
def tuples {α : Type} [Inhabited α] (sets : Array (Array α)) : Array (Array α) :=
  sets.foldl (init := #[#[]]) fun acc set =>
    acc.foldl (init := #[]) fun out row => set.foldl (init := out) fun out x => out.push (row.push x)

/-- `RuUnifyIndexesStepAcc`: what the nodes at the current place of each index are. -/
structure IndexesStep where
  isVar : Array Bool := #[]
  /-- The variables: free ones, and those that bound variables stand for. -/
  vars : Array Nat := #[]
  /-- The images of the bound variables that are not variables. -/
  exprs : Array Exp := #[]
  /-- The places with an application. -/
  inds : Array SubIndex := #[]
  rule : Option Nat := none
  /-- The application has no arguments. -/
  leaf : Bool := false
  ok : Bool := true

/-- `ruDoUnifyIndexesStep` -/
def indexesStep (ixs : Array (Index Nat)) (at_ : Array SubIndex) (sub : Subst) : IndexesStep :=
  at_.foldl (init := {}) fun st si =>
    let node := ixs[si.ix]!.nodes[si.curr]!
    if Node.isVar node.key then
      match sub.lookup node.key with
      | none => { st with isVar := st.isVar.push true, vars := st.vars.push node.key }
      | some ex =>
        if Node.isVar ex.nodes[0]! then { st with isVar := st.isVar.push true, vars := st.vars.push ex.nodes[0]! }
        else { st with isVar := st.isVar.push true, exprs := st.exprs.push ex }
    else
      let id := Node.appId node.key
      { st with isVar := st.isVar.push false, inds := st.inds.push { si with start := si.curr },
                rule := some id, leaf := node.ends.contains si.curr,
                ok := st.ok && (st.rule.isNone || st.rule == some id) }

/-- `ruDoUnifyTrivial`: one index alone: every subexpression that starts at the node, as
it was stored. -/
def indexesTrivial (ixs : Array (Index Nat)) (si : SubIndex) (sub : Subst) (acc : Array IndexesRet) :
    Array IndexesRet :=
  let node := ixs[si.ix]!.nodes[si.curr]!
  (Array.range node.ends.size).foldl (init := acc) fun acc k =>
    acc.push ⟨#[node.ends[k]!], sub, node.endExps[k]!⟩

/- The results of a walk are pushed onto an accumulator, down the recursion, where Russell
concatenates the arrays that come back. -/
mutual

/-- `ruDoUnifyIndexes`: each index goes one node on, to a child of where it is. -/
partial def indexesDown (ixs : Array (Index Nat)) (at_ : Array SubIndex) (sub : Subst)
    (acc : Array IndexesRet) : Array IndexesRet :=
  indexesTuples ixs at_ false 0 none #[] sub acc

/-- The tuples of children of the places `at_`, one from each, walked by `indexesNodes`:
of the whole product (Russell's `CartProd`), only those whose applications are all of
one term, since `indexesStep` rejects every other at once and the product is mostly
those. The first `i` places are chosen (`picked`), their applications of the term
`rule`; with `fromRoot` the places are the roots of the indexes, and a child starts a
subexpression. The tuples come in the order of the product. -/
partial def indexesTuples (ixs : Array (Index Nat)) (at_ : Array SubIndex) (fromRoot : Bool) (i : Nat)
    (rule : Option Nat) (picked : Array SubIndex) (sub : Subst) (acc : Array IndexesRet) :
    Array IndexesRet := Id.run do
  if i == at_.size then return indexesNodes ixs picked sub acc
  let si := at_[i]!
  let ix := ixs[si.ix]!
  let node := ix.nodes[si.curr]!
  let mut acc := acc
  for c in node.rules do
    let id := Node.appId ix.nodes[c]!.key
    if rule.isNone || rule == some id then
      let next := if fromRoot then { si with start := c, curr := c } else { si with curr := c }
      acc := indexesTuples ixs at_ fromRoot (i + 1) (some id) (picked.push next) sub acc
  for c in node.vars do
    let next := if fromRoot then { si with start := c, curr := c } else { si with curr := c }
    acc := indexesTuples ixs at_ fromRoot (i + 1) rule (picked.push next) sub acc
  return acc

/-- `ruDoUnifyIndexNodes`: the indexes are at the nodes `at_`; these are unified, and the
walk goes on behind them. -/
partial def indexesNodes (ixs : Array (Index Nat)) (at_ : Array SubIndex) (sub : Subst)
    (acc : Array IndexesRet) : Array IndexesRet :=
  if at_.isEmpty then acc
  else if at_.size == 1 then indexesTrivial ixs at_[0]! sub acc
  else
    let step := indexesStep ixs at_ sub
    if !step.ok then acc
    else
      -- binds the variables of the step to `ex` and goes on from `next`
      let finish (s : Subst) (ex : Exp) (next : Array SubIndex) (acc : Array IndexesRet) : Array IndexesRet :=
        match step.vars.foldlM (init := s) fun s1 v => s1.add1 v ex with
        | some s1 => indexesNext ixs next s1 acc
        | none => acc
      match step.rule with
      | some _ =>
        if step.isVar.any fun isVar => isVar then
          if !step.leaf then
            -- the applications are unified among themselves first, as whole subexpressions
            let inner :=
              if step.inds.size > 1 then indexesDown ixs step.inds sub #[]
              else if step.inds.size == 1 then indexesTrivial ixs step.inds[0]! sub #[]
              else #[]
            inner.foldl (init := acc) fun acc ret =>
              match unifyExps (step.exprs.push ret.expr) ret.sub with
              | none => acc
              | some s =>
                -- the indexes with a variable stay at it; the others are at the end of
                -- their subexpression
                let next := Id.run do
                  let mut out := #[]
                  let mut k := 0
                  for i in [0:at_.size] do
                    if step.isVar[i]! then out := out.push at_[i]!
                    else
                      out := out.push { at_[i]! with curr := ret.vect[k]! }
                      k := k + 1
                  return out
                finish s (s.apply ret.expr) next acc
          else
            let const : Exp := ⟨#[ixs[step.inds[0]!.ix]!.nodes[step.inds[0]!.curr]!.key]⟩
            match unifyExps (step.exprs.push const) sub with
            | some s => finish s const at_ acc
            | none => acc
        else
          -- applications of one term everywhere: on into the arguments
          indexesNext ixs at_ sub acc
      | none =>
        if step.exprs.isEmpty then
          match unifyStepVar step.vars with
          | some w => finish sub (Exp.ofVar w) at_ acc
          | none => acc
        else
          match unifyExps step.exprs sub with
          | some s => finish s (s.apply step.exprs[0]!) at_ acc
          | none => acc

/-- `ruDoUnifyIndexNodesNext`: if every index has reached the end of its subexpression
the unification is complete; otherwise the walk goes on. -/
partial def indexesNext (ixs : Array (Index Nat)) (at_ : Array SubIndex) (sub : Subst)
    (acc : Array IndexesRet) : Array IndexesRet :=
  let ended := at_.all fun si =>
    let ends := ixs[si.ix]!.nodes[si.start]!.ends
    ends.isEmpty || ends.contains si.curr
  if ended then
    -- the expression of the first index: a variable (a node without ends), or the
    -- stored subexpression that ends where it is
    let si := at_[0]!
    let node := ixs[si.ix]!.nodes[si.start]!
    let ex := if node.ends.isEmpty then Exp.ofVar node.key
      else node.endExps[(node.ends.findIdx? (· == si.curr)).getD 0]!
    acc.push ⟨at_.map (·.curr), sub, sub.apply ex⟩
  else indexesDown ixs at_ sub acc

end

/-- `ruUnifyIndexes`: the ways to take one stored expression from each index so that all
of them unify: the unifier, the unified expression, and for each index what is stored
under the expression taken. -/
def unifyIndexes (ixs : Array (Index Nat)) (sub : Subst := {}) : Array (Subst × Exp × Array (Array Nat)) :=
  if ixs.isEmpty then #[]
  else
    let roots := (Array.range ixs.size).map fun i => ({ ix := i, start := 0, curr := 0 } : SubIndex)
    let rets := indexesTuples ixs roots true 0 none #[] sub #[]
    rets.map fun ret => (ret.sub, ret.expr, (Array.range ixs.size).map fun i => ixs[i]!.nodes[ret.vect[i]!]!.data)

/-- `ruUnifySubsProd`: the tuples, one substitution from each set, that unify: for each,
the unifier and the places of its substitutions in their sets.

As in Russell since `47c52bdf`: a column (`RuSubsMatrix`) is made only for a variable
that substitutions of two or more sets bind. A variable bound in one set only cannot
filter a tuple — every other set reads it as free — so its bindings are put back per
tuple (`finish`). And the column unifiers of a group are unified in one call, not folded
pairwise.

With `cap`, the work stops once more than `cap` tuples are found: the caller is over its
budget then, and what is returned past that point is not a result (`addProof`). A
product can be exponential in the number of its sets, and nothing else stops it. -/
def unifySubsProd (sets : Array (Array Subst)) (cap : Nat := 0xFFFFFFFFFFFF) : Array (Subst × Array Nat) := Id.run do
  if sets.isEmpty || sets.any (·.isEmpty) then return #[]
  if sets.size == 1 then return (Array.range sets[0]!.size).map fun k => (sets[0]![k]!, #[k])
  -- in how many sets each variable is bound; the shared ones, in the order first seen
  let mut count : Std.HashMap Nat Nat := {}
  let mut order : Array Nat := #[]
  for set in sets do
    let mut inSet : Std.HashSet Nat := {}
    for sub in set do
      for v in sub.vars do inSet := inSet.insert v
    for v in inSet do
      if !count.contains v then order := order.push v
      count := count.insert v (count.getD v 0 + 1)
  let shared := order.filter fun v => count.getD v 0 ≥ 2
  -- each substitution's bindings of the variables that are not shared
  let privates : Array (Array Subst) := sets.map fun set =>
    set.map fun sub => sub.filter fun v _ => count.getD v 0 < 2
  -- a tuple's unifier: that of its group with the private bindings of its substitutions
  let finish (group : Subst) (picks : Array Nat) : Option Subst :=
    let parts := ((Array.range sets.size).map fun i => privates[i]![picks[i]!]!).filter (·.size > 0)
    if parts.isEmpty then some group else unifySubs (#[group] ++ parts)
  if shared.isEmpty then
    let mut out := #[]
    for picks in tuplesUpTo (sets.map fun set => Array.range set.size) cap do
      if out.size > cap then break
      if let some s := finish {} picks then out := out.push (s, picks)
    return out
  -- for each shared variable: the ways its images unify across the sets, each with the
  -- substitutions of every set that have the image taken (`RuSubsMatrix`)
  let mut columns : Array (Array (Subst × Array (Array Nat))) := #[]
  for v in shared do
    let rows : Array (Index Nat) := sets.map fun set =>
      (Array.range set.size).foldl (init := {}) fun ix k => ix.insert (set[k]!.lookupD v) k
    let column := (unifyIndexes rows).filterMap fun (sub, expr, data) =>
      match sub.lookup v with
      | none => (sub.add1 v expr).map fun s => (s, data)
      | some ex => (unifyExps #[expr, ex] sub).bind fun un => (sub.compose un).map fun s => (s, data)
    if column.isEmpty then return #[]
    columns := columns.push column
  -- `ruIntersectCols`: a tuple must pass for every variable. Two entries can have a
  -- tuple in common only if they share a substitution of the largest set, so the
  -- entries so far are looked up by those, not all tried against all.
  let widest := (Array.range sets.size).foldl (init := 0) fun best i =>
    if sets[i]!.size > sets[best]!.size then i else best
  let mut inter : Array (Array Subst × Array (Array Nat)) := columns[0]!.map fun (s, data) => (#[s], data)
  for c in [1:columns.size] do
    let mut having : Array (Array Nat) := Array.replicate sets[widest]!.size #[]
    for e in [0:inter.size] do
      for k in inter[e]!.2[widest]! do
        having := having.modify k (·.push e)
    let mut next := #[]
    for (s, data2) in columns[c]! do
      let mut tried : Std.HashSet Nat := {}
      for k in data2[widest]! do
        for e in having[k]! do
          if !tried.contains e then
            tried := tried.insert e
            let (subs, data) := inter[e]!
            let common := (Array.range data.size).map fun i => data[i]!.filter fun k => data2[i]!.contains k
            if !common.any (·.isEmpty) then next := next.push (subs.push s, common)
    inter := next
    -- every group has at least one tuple: past the cap, there is no use going on
    if inter.size > cap then return inter.extract 0 (cap + 1) |>.map fun (_, data) => ({}, data.map (·[0]!))
  -- the column unifiers of a group are unified at once, and every tuple that is left
  -- gets the result with its private bindings
  let mut out := #[]
  for (subs, data) in inter do
    if out.size > cap then break
    if let some group := unifySubs subs then
      for picks in tuplesUpTo data (cap - min cap out.size) do
        if out.size > cap then break
        if let some s := finish group picks then out := out.push (s, picks)
  return out

end Whitehead.Prove
