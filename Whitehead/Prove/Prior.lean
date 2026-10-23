/-
A prior per theorem for the learned rank (`docs/DESIGN.md`, "The learned ranking layer",
step 6): the assertions that the proofs of earlier theorems with a statement like this one
use. It is premise selection as MaSh does it for Sledgehammer: the k nearest earlier
theorems by the terms of their statements, weighted by how rare each term is, and each
neighbour votes for the assertions of its proof with its similarity; or, as MaSh's other
learner, a naive Bayes estimate of how likely each assertion is used under the statement's
terms.

The rank's other features are local to a step: what it brings, what it shares with the
goal, how often the file uses it. At a goal with metavariables thousands of variants look
alike by them, and the right one is the lemma the proof is about — which the theorems that
resemble this one tell. Only earlier theorems count, as everywhere in the features, so a
model tested on later theorems is tested out of sample.

The variants here are compared by `prove prior`, which ranks the assertions of a file by
the prior alone and asks where the ones the known proof uses come (`docs/EXPERIMENTS.md`).
-/
import Whitehead.Prove.Features
import Whitehead.Prove.Uses
import Whitehead.Prove.Contexts

namespace Whitehead.Prove

/-- How a neighbour's vote for the assertions of its proof is weighted. -/
inductive Vote where
  /-- By its similarity. -/
  | sim
  /-- By 1: a count of the neighbours that use the assertion. -/
  | count
  /-- By its similarity divided by the number of assertions its proof uses, as MaSh does
  (`k_nearest_neighbors` in `sledgehammer_mash.ML`): a neighbour's vote is one vote, shared. -/
  | norm
  deriving BEq, Repr, Inhabited

/-- The choices the prior is built and asked with. The defaults are what `prove prior`
chose on 2026-10-22 (`docs/EXPERIMENTS.md`, "The prior tuned"): of the assertions set.mm's
test theorems use, 54.9% come in the prior's first 100 against 47.0% with 100 neighbours
voting their similarity for the terms alone, and the other files gain as much. -/
structure PriorOptions where
  /-- How many nearest theorems vote. -/
  k : Nat := 1000
  vote : Vote := .sim
  /-- The neighbour itself is a candidate too: it gets its similarity times this. -/
  self : Float := 3
  /-- A vote by similarity is the similarity to this power: above 1, the nearest count
  more, so a large `k` adds coverage without blurring the top. -/
  power : Float := 4
  /-- Besides the terms of a statement, its parent–child term pairs are features: the
  shape of the statement, not only its vocabulary. -/
  pairs : Bool := true
  /-- Naive Bayes in place of the nearest neighbours: for each assertion used before, the
  log odds of its use given the features of the statement. -/
  nb : Bool := false
  /-- Naive Bayes: the weight of a feature of the statement the assertion was never used
  with (`def_val` of MaSh, −18 there), and the factor of one it was (`pos_weight`, 5). The
  features weigh their idf, as in MaSh, not their share of the statement's vector. -/
  nbAbsent : Float := -18
  nbPresent : Float := 5
  deriving Repr, Inhabited

/-- The statements of the file as weighted feature vectors, an inverted index of them, and
the assertions each proof uses. -/
structure Prior where
  opts : PriorOptions := {}
  /-- For each assertion, the features of its statement with their weights, the vector of
  length 1. -/
  vectors : Array (Array (Nat × Float)) := #[]
  /-- The length of each vector before it was normalized: the idf weights are these times
  the vector's. -/
  norms : Array Float := #[]
  /-- For each feature, the assertions whose statements have it, with the weight there, in
  the order of the assertions. -/
  postings : Array (Array (Nat × Float)) := #[]
  /-- For each theorem, the assertions its proof uses. -/
  used : Array (Array Nat) := #[]
  /-- The pairs' numbers (after the terms) and the weights of the features, for the
  contexts of use, which vectorize goals as the prior does statements (`Contexts.lean`);
  a feature too common has weight 0. -/
  pairIds : Std.HashMap (Nat × Nat) Nat := {}
  termIdf : Array Float := #[]
  pairIdf : Array Float := #[]
  deriving Inhabited

namespace Prior

/-- The pairs of a statement: of its conclusion and its hypotheses (`Exp.termPairs`,
`Contexts.lean`). -/
def Assertion.termPairs (a : Assertion) : Array (Nat × Nat) :=
  (a.hyps.push a.concl).foldl (init := #[]) fun acc e =>
    (Exp.termPairs e).foldl (init := acc) fun acc p => if acc.contains p then acc else acc.push p

/-- The prior of a file: `stats` for the weights, `uses` for the proofs. A feature in more
than a fifth of the statements is left out of the index: it tells little and its posting
list is long. With `opts.pairs`, the term pairs are features after the terms, numbered as
they are met. -/
def ofDb (db : Db) (stats : SymbolStats) (uses : Uses) (opts : PriorOptions := {}) : Prior := Id.run do
  let n := db.asserts.size
  let common := stats.statements / 5
  -- the pairs: their numbers and how many statements have each
  let mut pairIds : Std.HashMap (Nat × Nat) Nat := {}
  let mut pairDf : Array Nat := #[]
  if opts.pairs then
    for a in db.asserts do
      if a.pseudo.isSome then continue
      for p in Assertion.termPairs a do
        match pairIds[p]? with
        | some id => pairDf := pairDf.modify id (· + 1)
        | none =>
          pairIds := pairIds.insert p pairDf.size
          pairDf := pairDf.push 1
  let nFeats := db.terms.size + pairDf.size
  let idfOf (df : Nat) : Float := Float.log ((stats.statements.toFloat + 1) / (df.toFloat + 1))
  let mut vectors : Array (Array (Nat × Float)) := Array.mkEmpty n
  let mut norms : Array Float := Array.mkEmpty n
  let mut postings : Array (Array (Nat × Float)) := Array.replicate nFeats #[]
  for a in db.asserts do
    if a.pseudo.isSome then
      vectors := vectors.push #[]
      norms := norms.push 0
      continue
    let terms := a.terms.filter fun t => (stats.df[t]?.getD 0) ≤ common
    let mut ws := terms.map fun t => (t, stats.idf t)
    if opts.pairs then
      for p in Assertion.termPairs a do
        let some id := pairIds[p]? | continue
        if pairDf[id]! ≤ common then ws := ws.push (db.terms.size + id, idfOf pairDf[id]!)
    let norm := Float.sqrt (ws.foldl (init := 0) fun acc (_, w) => acc + w * w)
    let v := if norm == 0 then #[] else ws.map fun (t, w) => (t, w / norm)
    vectors := vectors.push v
    norms := norms.push norm
    for (t, w) in v do
      if t < postings.size then postings := postings.modify t (·.push (a.id, w))
  let mut used : Array (Array Nat) := Array.replicate n #[]
  for a in [0:uses.byAssertion.size] do
    for thm in uses.byAssertion[a]! do
      if thm < n then used := used.modify thm (·.push a)
  let termIdf := (Array.range db.terms.size).map fun t => if (stats.df[t]?.getD 0) ≤ common then stats.idf t else 0
  let pairIdf := pairDf.map fun df => if df ≤ common then idfOf df else 0
  return { opts, vectors, norms, postings, used, pairIds, termIdf, pairIdf }

/-- The theorems before `thm` by their similarity to it, the nearest first. Only theorems
with a proof read count: the others have nothing to vote for. -/
def neighbours (p : Prior) (thm : Nat) : Array (Nat × Float) := Id.run do
  let some v := p.vectors[thm]? | return #[]
  let mut sims : Std.HashMap Nat Float := {}
  for (t, w) in v do
    for (b, w') in p.postings[t]?.getD #[] do
      if b ≥ thm then break
      if (p.used[b]?.getD #[]).isEmpty then continue
      sims := sims.alter b fun s => some (s.getD 0 + w * w')
  return sims.toArray.qsort fun a b => a.2 > b.2 || a.2 == b.2 && a.1 > b.1

/-- The nearest-neighbour prior of theorem `thm`: for each assertion, the votes of the `k`
nearest theorems before `thm` whose proofs use it. -/
def knn (p : Prior) (thm : Nat) : Std.HashMap Nat Float := Id.run do
  let top := (p.neighbours thm).extract 0 p.opts.k
  let mut out : Std.HashMap Nat Float := {}
  for (b, s) in top do
    let ds := p.used[b]?.getD #[]
    let s := if p.opts.power == 1 then s else Float.pow s p.opts.power
    let w := match p.opts.vote with
      | .sim => s
      | .count => 1
      | .norm => s / ds.size.toFloat
    for a in ds do
      out := out.alter a fun x => some (x.getD 0 + w)
    if p.opts.self > 0 then
      out := out.alter b fun x => some (x.getD 0 + p.opts.self * s)
  return out

/-- The naive Bayes prior of theorem `thm` (`naive_bayes` in `sledgehammer_mash.ML`,
without its term for the features the assertion's users have and the statement lacks): for
each assertion `a` used by a theorem before `thm`, with `t` such theorems and `s f` of them
whose statements have feature `f`,
`ln t + Σ_f w_f · (if s f > 0 then ln (present · s f / t) else absent)`
over the weighted features `f` of the statement, shifted so that the lowest is 1: the
rank's features read 0 as "no prior". -/
def nb (p : Prior) (thm : Nat) : Std.HashMap Nat Float := Id.run do
  let some v := p.vectors[thm]? | return {}
  if v.isEmpty then return {}
  let m := v.size
  let norm := p.norms[thm]?.getD 1
  -- the position of each feature of the statement
  let mut pos : Std.HashMap Nat Nat := {}
  for i in [0:m] do
    pos := pos.insert v[i]!.1 i
  let n := p.used.size
  let mut t : Array Nat := Array.replicate n 0
  let mut s : Array Nat := Array.replicate (n * m) 0
  for b in [0:min thm n] do
    let ds := p.used[b]!
    if ds.isEmpty then continue
    -- the features this theorem's statement shares with `thm`'s
    let mut shared : Array Nat := #[]
    for (f, _) in p.vectors[b]?.getD #[] do
      if let some i := pos[f]? then shared := shared.push i
    for a in ds do
      if a ≥ n then continue
      t := t.modify a (· + 1)
      for i in shared do
        s := s.modify (a * m + i) (· + 1)
  let mut scores : Array (Nat × Float) := #[]
  for a in [0:n] do
    if t[a]! == 0 then continue
    let ta := t[a]!.toFloat
    let mut score := Float.log ta
    for i in [0:m] do
      let w := v[i]!.2 * norm
      let sf := s[a * m + i]!
      score := score + w * (if sf > 0 then Float.log (p.opts.nbPresent * sf.toFloat / ta) else p.opts.nbAbsent)
    scores := scores.push (a, score)
  let low := scores.foldl (init := (0 : Float)) fun acc (_, x) => if x < acc then x else acc
  let mut out : Std.HashMap Nat Float := {}
  for (a, x) in scores do
    out := out.insert a (x - low + 1)
  return out

/-- The prior of theorem `thm`: a positive value for each assertion with one, by `opts`. -/
def query (p : Prior) (thm : Nat) : Std.HashMap Nat Float :=
  if p.opts.nb then p.nb thm else p.knn thm

end Prior

/-- The contexts of use with the prior's weights and pair numbers, and no records yet
(`contextRecords` and `Contexts.withRecords` in `Dataset.lean` add them). With the prior's
`pairs` off, the pairs are empty and the contexts read terms alone. -/
def Contexts.ofPrior (p : Prior) : Contexts :=
  { idf := p.termIdf, pairIds := p.pairIds, pairIdf := p.pairIdf }

end Whitehead.Prove
