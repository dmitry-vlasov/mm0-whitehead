/-
How many variants an agent chooses among (`docs/DESIGN.md`, "Phase 4", "Measurement").

A known proof is replayed over the full expansion with no other variants
(`oracleAll skel (some 0)`): every goal node on its path is expanded against the whole
database, so it has all its variants, and the variant of the known proof is chosen.
The number of variants of each such node is what a filter has to narrow. A node closed
by a hypothesis of the theorem has nothing to choose, and is not counted.

This is the baseline for filters. Measuring a filter needs someone who writes it, an
agent; that comes with the front-ends.
-/
import Whitehead.Prove.Replay

namespace Whitehead.Prove

/-- The variants of the goal nodes on the path of the known proof of statement `i` of the
file, a theorem: for each node where a step is chosen, how many variants it has. `none`
for a proof with a shared conversion; and whether the replay stopped at a limit, in
which case the counts are of the nodes reached. -/
def variantCounts (db : Db) (index : Index Nat) (limits : Limits) (i : Nat) :
    IO (Option (Array Nat × Bool)) := do
  let s := db.file.stmts[i]!
  match db.skeleton s with
  | .error _ | .ok none => return none
  | .ok (some skel) =>
    let env := Env.init db index (db.task s.index)
    let r ← searchWith acceptAny env (oracleAll skel (some 0)) limits
    let env := r.env
    -- the goal nodes whose chosen variant was expanded, each once
    let mut seen : Std.HashSet Nat := {}
    let mut counts := #[]
    for p in [0:env.props.size] do
      let prop := env.props[p]!
      if prop.expanded && !seen.contains prop.parent then
        seen := seen.insert prop.parent
        counts := counts.push env.hyps[prop.parent]!.children.size
    return some (counts, r.ending == .limit)

/-- A summary of variant counts: how many nodes, the mean, quantiles, the largest, and how
many fall in each decade (1, 2–10, 11–100, ...). -/
def variantSummary (counts : Array Nat) : String := Id.run do
  if counts.isEmpty then return "no nodes"
  let sorted := counts.qsort (· < ·)
  let n := sorted.size
  let q (num den : Nat) : Nat := sorted[min (n - 1) (n * num / den)]!
  let sum := sorted.foldl (· + ·) 0
  let mut decades : Array Nat := #[]
  let mut lo := 1
  let mut hi := 1
  while lo ≤ sorted.back! do
    let k := (sorted.filter fun c => lo ≤ c && c ≤ hi).size
    decades := decades.push k
    lo := hi + 1
    hi := hi * 10
  let labels := #["1", "2-10", "11-100", "101-1000", "1001-10000", "10001-100000", "more"]
  let pct (k : Nat) : String := s!"{k * 1000 / n / 10}.{k * 1000 / n % 10}%"
  let parts := (Array.range decades.size).map fun j => s!"{labels[min j 6]!}: {decades[j]!} ({pct decades[j]!})"
  return s!"{n} nodes; variants per node: mean {sum / n}, median {q 1 2}, 90% {q 9 10}, 99% {q 99 100}, \
    largest {sorted.back!}\n  {", ".intercalate parts.toList}"

end Whitehead.Prove
