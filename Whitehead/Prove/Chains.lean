/-
Phase 4, the first tool: mining linear subproofs.

A *chain* is a path of `k` steps in a proof tree — the tree of assertions that
`Db.skeleton` gives — each step proving one hypothesis of the one above it: `a₁` at the
top, `a₂` proving its `j₁`-th hypothesis, …, `aₖ` proving the `j_{k-1}`-th hypothesis of
`a_{k-1}`. The other hypotheses of the steps are open. Two occurrences are of the same
chain when the assertions and the positions agree; the chain is then a derived rule,
with one unifier (`CLAUDE.md`, phase 4). Russell's `common_subproofs.flow` counts the
chains of parents that the uses of an assertion share; `linear_guided.flow` replays a
chain from a goal down to a premise.

The miner counts how often each chain occurs in the proofs of a file, by length, in
the manner of Apriori: a chain of length `k + 1` is counted only where its upper `k`
steps are a chain that occurs at least `min` times, since a chain occurs at most as
often as any part of it. So memory holds the frequent chains and the counts of those
are exact; the occurrences that were not counted are reported as such. A shared
subproof is walked every time it is used, as `Skeleton.size` counts it.
-/
import Std.Data.HashMap
import Std.Data.HashSet
import Whitehead.Prove.Db

namespace Whitehead.Prove

open Whitehead.Mmb

/-- The key of a chain of `k` steps, top down: the assertion at the top, then for each
step below it the position of the hypothesis it proves and its assertion:
`[a₁, j₁, a₂, …, j_{k-1}, aₖ]`. -/
abbrev ChainKey := Array Nat

structure ChainOptions where
  /-- The longest chains mined. -/
  maxLen : Nat := 6
  /-- A chain is frequent, and kept, when it occurs at least this often. -/
  min : Nat := 2
  /-- How many of the most frequent chains of each length are listed. -/
  top : Nat := 10
  /-- Coverage is reported for each of these counts that is at least `min`: the share
  of the steps that lie on a chain occurring that often. -/
  thresholds : Array Nat := #[2, 10, 100, 1000]

/-- What the miner found for one length. -/
structure LengthStats where
  len : Nat
  /-- Steps that end a chain of this length: every occurrence, frequent or not. -/
  occurrences : Nat := 0
  /-- Of those, the occurrences counted: the ones whose upper part is frequent. -/
  counted : Nat := 0
  /-- Of the counted, those whose top step is the root of its proof, and those whose
  bottom step has a hypothesis of the theorem as a child. -/
  toRoot : Nat := 0
  fromHyp : Nat := 0
  /-- Distinct chains with at least `min` occurrences, and their occurrences in all. -/
  frequent : Nat := 0
  frequentOccurrences : Nat := 0
  /-- The most frequent chains, each with its occurrences and the number of proofs it
  occurs in: a chain in a shared subproof occurs once per use, and a few large proofs
  can make most of a count. -/
  top : Array (ChainKey × Nat × Nat) := #[]
  deriving Inhabited

structure ChainStats where
  proofs : Nat := 0
  steps : Nat := 0
  /-- By length, from 2. -/
  lengths : Array LengthStats := #[]
  /-- For each threshold: the threshold and the number of steps on a chain of length at
  least 2 that occurs at least that often. -/
  covered : Array (Nat × Nat) := #[]
  deriving Inhabited

/-- The key of the chain of `k` steps whose bottom is the last entry of `path`; `path`
holds the ancestors of a step top down, each with the position it has among the
hypotheses of its parent. `path.size ≥ k`. -/
def chainKey (path : Array (Nat × Nat)) (k : Nat) : ChainKey := Id.run do
  let d := path.size
  let mut key : ChainKey := #[path[d - k]!.1]
  for i in [d - k + 1 : d] do
    key := key.push path[i]!.2
    key := key.push path[i]!.1
  return key

/-- The accumulator of one pass of the miner. -/
structure ChainPass where
  counts : Std.HashMap ChainKey Nat := {}
  /-- The chains seen in the current proof, and in how many proofs each chain occurs. -/
  seen : Std.HashSet ChainKey := {}
  proofs : Std.HashMap ChainKey Nat := {}
  occurrences : Nat := 0
  counted : Nat := 0
  toRoot : Nat := 0
  fromHyp : Nat := 0

/-- One pass over a proof: for each step whose chain of length `k` ending at its parent
is in `frequent`, the chain of length `k + 1` ending at it is counted. `pos` is the
step's position among the hypotheses of its parent. -/
partial def chainPass (k : Nat) (frequent : Std.HashMap ChainKey Nat) (sk : Skeleton) (pos : Nat)
    (path : Array (Nat × Nat)) : StateM ChainPass Unit := do
  match sk with
  | .hyp _ => pure ()
  | .step thm children =>
    let path := path.push (thm, pos)
    if path.size ≥ k + 1 then
      modify fun a => { a with occurrences := a.occurrences + 1 }
      if frequent.contains (chainKey path.pop k) then
        let key := chainKey path (k + 1)
        let fromHyp := children.any fun c => match c with | .hyp _ => true | _ => false
        modify fun a =>
          let fresh := !a.seen.contains key
          { a with counts := a.counts.alter key fun | none => some 1 | some n => some (n + 1),
                   seen := if fresh then a.seen.insert key else a.seen,
                   proofs := if fresh then a.proofs.alter key (fun | none => some 1 | some n => some (n + 1)) else a.proofs,
                   counted := a.counted + 1,
                   toRoot := a.toRoot + (if path.size == k + 1 then 1 else 0),
                   fromHyp := a.fromHyp + (if fromHyp then 1 else 0) }
    for i in [0:children.size] do
      chainPass k frequent children[i]! i path

/-- The accumulator of the coverage pass: for each threshold, the steps of the current
proof on a frequent chain, by their number in the walk. -/
structure CoverPass where
  marks : Array (Array Bool) := #[]
  next : Nat := 0

/-- The coverage pass over a proof: a step is marked for a threshold when it lies on a
chain, of any length mined, that occurs at least that often. `frequent[k]` holds the
frequent chains of length `k`. `indices` are the numbers of the ancestors in the walk. -/
partial def coverPass (frequent : Array (Std.HashMap ChainKey Nat)) (thresholds : Array Nat) (sk : Skeleton)
    (pos : Nat) (path : Array (Nat × Nat)) (indices : Array Nat) : StateM CoverPass Unit := do
  match sk with
  | .hyp _ => pure ()
  | .step thm children =>
    let path := path.push (thm, pos)
    let me := (← get).next
    modify fun a => { a with next := a.next + 1 }
    let indices := indices.push me
    for k in [2:frequent.size] do
      if path.size ≥ k then
        if let some c := frequent[k]!.get? (chainKey path k) then
          for t in [0:thresholds.size] do
            if c ≥ thresholds[t]! then
              for i in [indices.size - k : indices.size] do
                modify fun a => { a with marks := a.marks.modify t (·.set! indices[i]! true) }
    for i in [0:children.size] do
      coverPass frequent thresholds children[i]! i path indices

/-- Mines the chains of the proofs of `db`. Proofs with a shared conversion are left
out, as the replay leaves them out. -/
def mineChains (db : Db) (opts : ChainOptions) : Except String ChainStats := do
  let f := db.file
  let mut skeletons : Array Skeleton := #[]
  let mut steps := 0
  for s in f.stmts do
    if let .thm _ := s.kind then
      match db.skeleton s with
      | .error msg => throw s!"theorem {f.thmName s.index}: {msg}"
      | .ok none => pure ()
      | .ok (some sk) =>
        skeletons := skeletons.push sk
        steps := steps + sk.size
  -- length 1: every assertion is a frequent chain of one step if it is used `min`
  -- times; counted by a pass with an empty set of frequent chains of length 0, which
  -- `chainKey` never looks at
  let mut frequent : Array (Std.HashMap ChainKey Nat) := #[{}, {}]
  let mut lengths : Array LengthStats := #[]
  let mut counts : Std.HashMap ChainKey Nat := {}
  for sk in skeletons do
    counts := countAssertions sk counts
  frequent := frequent.set! 1 (counts.filter fun _ n => n ≥ opts.min)
  for k in [1:opts.maxLen] do
    let mut acc : ChainPass := {}
    for sk in skeletons do
      acc := (chainPass k frequent[k]! sk 0 #[]).run { acc with seen := {} } |>.2
    let freq := acc.counts.filter fun _ n => n ≥ opts.min
    let top := ((freq.toArray.qsort fun a b => a.2 > b.2 || a.2 == b.2 && a.1.toList < b.1.toList).extract 0 opts.top).map
      fun (key, n) => (key, n, acc.proofs.getD key 0)
    lengths := lengths.push
      { len := k + 1, occurrences := acc.occurrences, counted := acc.counted, toRoot := acc.toRoot,
        fromHyp := acc.fromHyp, frequent := freq.size,
        frequentOccurrences := freq.fold (init := 0) fun n _ c => n + c, top }
    frequent := frequent.push freq
  -- coverage
  let thresholds := opts.thresholds.filter (· ≥ opts.min)
  let mut covered : Array Nat := Array.replicate thresholds.size 0
  for sk in skeletons do
    let n := sk.size
    let acc : CoverPass := { marks := Array.replicate thresholds.size (Array.replicate n false) }
    let acc := (coverPass frequent thresholds sk 0 #[] #[]).run acc |>.2
    for t in [0:thresholds.size] do
      covered := covered.modify t (· + (acc.marks[t]!.filter id).size)
  return { proofs := skeletons.size, steps, lengths, covered := thresholds.zip covered }
where
  countAssertions (sk : Skeleton) (counts : Std.HashMap ChainKey Nat) : Std.HashMap ChainKey Nat :=
    match sk with
    | .hyp _ => counts
    | .step thm children =>
      children.foldl (init := counts.alter #[thm] fun | none => some 1 | some n => some (n + 1)) fun c ch =>
        countAssertions ch c

/-- A chain for a reader: the assertions by name, each but the first after the position
of the hypothesis it proves, as `ax_mp .1 syl .0 a1i`. -/
def chainText (db : Db) (key : ChainKey) : String := Id.run do
  let mut s := db.asserts[key[0]!]!.name
  let mut i := 1
  while i + 1 < key.size do
    s := s ++ s!" .{key[i]!} " ++ db.asserts[key[i + 1]!]!.name
    i := i + 2
  return s

end Whitehead.Prove
