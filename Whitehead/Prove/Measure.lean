/-
How many variants an agent chooses among (`docs/DESIGN.md`, "Phase 4", "Measurement").

A known proof is replayed over the full expansion with no other variants
(`oracleAll skel (some 0)`): every goal node on its path is expanded against the whole
database, so it has all its variants, and the variant of the known proof is chosen.
The number of variants of each such node is what a filter has to narrow. A node closed
by a hypothesis of the theorem has nothing to choose, and is not counted.

This is the baseline for filters. Measuring a filter needs someone who writes it, an
agent; that comes with the front-ends.

What the filters can do, without an agent: at each such node, the filter that says only
what the new goals of the known proof's variant look like, to a depth — their premises'
number, and each new goal's terms and the theorem's variables down to depth `d`, with a
hole for everything below and for every variable of the tree. It never names the
assertion. How many variants pass it, at depths 1, 2 and 3, is how far a description of
the next goals narrows the choice. The known proof's variant always passes.
-/
import Whitehead.Prove.Replay
import Whitehead.Prove.Filter

namespace Whitehead.Prove

/-- The shape of `e` to depth `d`: its terms and constants down to depth `d`, a hole for
what is below and for every variable. -/
partial def Exp.shape (e : Exp) (d : Nat) : Exp :=
  go 0 d
where
  go (i d : Nat) : Exp :=
    let n := e.nodes[i]!
    if d == 0 || Node.isVar n then ⟨#[holeNode]⟩
    else if Node.isConst n then ⟨#[n]⟩
    else Exp.mkApp (Node.appId n) (Node.ty n) ((e.argStarts i).map (go · (d - 1)))

/-- The filter that describes assertion node `p` to depth `d`: its number of premises, and
the shape of each of its new goals. -/
def Env.shapeFilter (env : Env) (p : Nat) (d : Nat) : Filter :=
  let v := env.propView p
  .and (#[Filter.premises v.premises v.premises] ++ v.goals.get.map fun g => Filter.goal (g.shape d))

/-- What is measured at a goal node on the path of a known proof: its variants, and with
`depths`, how many of them pass the filter that describes the known proof's variant to
each depth, and whether that variant passes. -/
structure NodeCount where
  variants : Nat
  shaped : Array Nat := #[]
  kept : Bool := true
  /-- The number of premises of the known proof's variant. -/
  premises : Nat := 0
  /-- Where the known proof's variant is when the variants are ordered by their uses in
  the proofs before the theorem (`Session.select` with `byUses`), from 1: among all of
  them, and among those that pass its description to each depth. -/
  rankAll : Nat := 0
  ranks : Array Nat := #[]
  /-- The same, the variants ordered by the latest proof before the theorem that uses
  their assertion, then by uses (`Env.rankByRecency`): among all, and among those that
  pass the description to each depth. -/
  recentAll : Nat := 0
  recents : Array Nat := #[]
  deriving Inhabited

/-- Where variant `p` is among `set`, ordered by uses, the most first, the first made
first among equals; from 1. -/
def Env.rankByUses (env : Env) (set : Array Nat) (p : Nat) : Nat :=
  let u (q : Nat) : Nat := env.stepUses env.props[q]!.step
  1 + (set.filter fun q => u q > u p || u q == u p && q < p).size

/-- Where variant `p` is among `set`, ordered by the latest proof before the theorem that
uses its assertion, the latest first, then by uses; from 1. -/
def Env.rankByRecency (env : Env) (set : Array Nat) (p : Nat) : Nat :=
  let l (q : Nat) : Nat := match env.props[q]!.step with
    | .assertion id => env.uses.latest id env.task.limit
    | .conv .. => 0
  let u (q : Nat) : Nat := env.stepUses env.props[q]!.step
  1 + (set.filter fun q => l q > l p || l q == l p && (u q > u p || u q == u p && q < p)).size

/-- The goal nodes on the path of the known proof of statement `i` of the file, a theorem,
where a step is chosen: what `NodeCount` says of each. `none` for a proof with a shared
conversion; and whether the replay stopped at a limit, in which case the nodes are those
reached. -/
def nodeCounts (db : Db) (index : Index Nat) (limits : Limits) (depths : Array Nat) (i : Nat)
    (uses : Uses := {}) : IO (Option (Array NodeCount × Bool)) := do
  let s := db.file.stmts[i]!
  match db.skeleton s with
  | .error _ | .ok none => return none
  | .ok (some skel) =>
    let env := { Env.init db index (db.task s.index) with uses }
    let r ← searchWith acceptAny env (oracleAll skel (some 0)) limits
    let env := r.env
    let mut seen : Std.HashSet Nat := {}
    let mut out := #[]
    for p in [0:env.props.size] do
      let prop := env.props[p]!
      if prop.expanded && !seen.contains prop.parent then
        seen := seen.insert prop.parent
        let kids := env.hyps[prop.parent]!.children
        let mut shaped := #[]
        let mut ranks := #[]
        let mut recents := #[]
        let mut kept := true
        for d in depths do
          let f := env.shapeFilter p d
          let passing := kids.filter fun q => f.eval (env.propView q)
          shaped := shaped.push passing.size
          ranks := ranks.push (env.rankByUses passing p)
          recents := recents.push (env.rankByRecency passing p)
          kept := kept && f.eval (env.propView p)
        out := out.push { variants := kids.size, shaped, kept, premises := prop.rule.hyps.size,
                          rankAll := env.rankByUses kids p, ranks,
                          recentAll := env.rankByRecency kids p, recents }
    return some (out, r.ending == .limit)

/-- `nodeCounts` without the filters: how many variants each node has. -/
def variantCounts (db : Db) (index : Index Nat) (limits : Limits) (i : Nat) :
    IO (Option (Array Nat × Bool)) := do
  return (← nodeCounts db index limits #[] i).map fun (cs, limited) => (cs.map (·.variants), limited)

/-- Where the known variants rank: the share of nodes at which it is first, in the first
5, and in the first 10. -/
def rankSummary (ranks : Array Nat) : String :=
  let n := ranks.size
  if n == 0 then "no nodes" else
  let pct (k : Nat) : String := s!"{k * 1000 / n / 10}.{k * 1000 / n % 10}%"
  let within (k : Nat) : Nat := (ranks.filter (· ≤ k)).size
  s!"{n} nodes; first {pct (within 1)}, in the first 5 {pct (within 5)}, in the first 10 {pct (within 10)}"

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
  let few := (sorted.filter (· ≤ 5)).size
  return s!"{n} nodes; variants per node: mean {sum / n}, median {q 1 2}, 90% {q 9 10}, 99% {q 99 100}, \
    largest {sorted.back!}; 5 or fewer: {pct few}\n  {", ".intercalate parts.toList}"

end Whitehead.Prove
