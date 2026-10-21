/-
A prior per theorem for the learned rank (`docs/DESIGN.md`, "The learned ranking layer",
step 6): the assertions that the proofs of earlier theorems with a statement like this one
use. It is premise selection as MaSh does it for Sledgehammer: the k nearest earlier
theorems by the terms of their statements, weighted by how rare each term is, and each
neighbour votes for the assertions of its proof with its similarity.

The rank's other features are local to a step: what it brings, what it shares with the
goal, how often the file uses it. At a goal with metavariables thousands of variants look
alike by them, and the right one is the lemma the proof is about — which the theorems that
resemble this one tell. Only earlier theorems count, as everywhere in the features, so a
model tested on later theorems is tested out of sample.
-/
import Whitehead.Prove.Features
import Whitehead.Prove.Uses

namespace Whitehead.Prove

/-- The statements of the file as weighted term vectors, an inverted index of them, and
the assertions each proof uses. -/
structure Prior where
  /-- For each assertion, the terms of its statement with their weights, the vector of
  length 1. -/
  vectors : Array (Array (Nat × Float)) := #[]
  /-- For each term, the assertions whose statements have it, with the weight there, in
  the order of the assertions. -/
  postings : Array (Array (Nat × Float)) := #[]
  /-- For each theorem, the assertions its proof uses. -/
  used : Array (Array Nat) := #[]
  deriving Inhabited

namespace Prior

/-- The prior of a file: `stats` for the weights, `uses` for the proofs. A term in more
than a fifth of the statements is left out of the index: it tells little and its posting
list is long. -/
def ofDb (db : Db) (stats : SymbolStats) (uses : Uses) : Prior := Id.run do
  let n := db.asserts.size
  let common := stats.statements / 5
  let mut vectors : Array (Array (Nat × Float)) := Array.mkEmpty n
  let mut postings : Array (Array (Nat × Float)) := Array.replicate db.terms.size #[]
  for a in db.asserts do
    if a.pseudo.isSome then
      vectors := vectors.push #[]
      continue
    let terms := a.terms.filter fun t => (stats.df[t]?.getD 0) ≤ common
    let ws := terms.map fun t => (t, stats.idf t)
    let norm := Float.sqrt (ws.foldl (init := 0) fun acc (_, w) => acc + w * w)
    let v := if norm == 0 then #[] else ws.map fun (t, w) => (t, w / norm)
    vectors := vectors.push v
    for (t, w) in v do
      if t < postings.size then postings := postings.modify t (·.push (a.id, w))
  let mut used : Array (Array Nat) := Array.replicate n #[]
  for a in [0:uses.byAssertion.size] do
    for thm in uses.byAssertion[a]! do
      if thm < n then used := used.modify thm (·.push a)
  return { vectors, postings, used }

/-- The prior of theorem `thm`: for each assertion, the sum of the similarities of the `k`
nearest theorems before `thm` whose proofs use it. -/
def query (p : Prior) (thm : Nat) (k : Nat := 100) : Std.HashMap Nat Float := Id.run do
  let some v := p.vectors[thm]? | return {}
  let mut sims : Std.HashMap Nat Float := {}
  for (t, w) in v do
    for (b, w') in p.postings[t]?.getD #[] do
      if b ≥ thm then break
      if (p.used[b]?.getD #[]).isEmpty then continue
      sims := sims.alter b fun s => some (s.getD 0 + w * w')
  let top := (sims.toArray.qsort fun a b => a.2 > b.2 || a.2 == b.2 && a.1 > b.1).extract 0 k
  let mut out : Std.HashMap Nat Float := {}
  for (b, s) in top do
    for a in p.used[b]?.getD #[] do
      out := out.alter a fun x => some (x.getD 0 + s)
  return out

end Prior

end Whitehead.Prove
