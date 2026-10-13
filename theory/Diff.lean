/-
`lake exe diff-test <file.mmb> <rounds> [--from A] [--to B] [--every K] [--meta I,J,...]
[--max-tuples N] [--max-nodes N] [--assertions K]`: the differential test of the production engine against the reference engine
(`docs/THEORY.md`, "The link to the production engine", milestone 6).

For each theorem of the range, both engines run for the same number of rounds: the
production engine breadth first, with no limit and no forward front, driven round by
round here so that every proof at the root is kept (`searchCore` stops at the first);
the reference engine by `State.run`. A proof at the root is compared by its *shape* —
the assertions of its steps and the hypotheses at its leaves — and its *answer*: the
goal and the metavariables under its substitution, with the variables renamed by first
occurrence, since the two engines name their fresh variables differently and a most
general unifier is unique up to renaming only. Checked:

- every proof the production engine has at the root is, by shape and answer, an entry
  of the reference engine (the production engine keeps one proof per key, so it has at
  most the reference engine's entries);
- every reference entry's answer is among the production engine's (the key at the
  root is the answer: all conditions on bound variables are judged there).

Proofs with a conversion step (`unfold`) have no counterpart in the reference engine,
which has no definitions (decision 6); they are counted and left out.

`--max-tuples N` (1,000,000 unless given) leaves out a theorem whose joins would visit
more than `N` tuples of proofs in either engine: the production engine's
`Counters.tuples`, the sum of the sizes of the products it joins, and the same sum over
the reference engine's enumeration, which builds every tuple as a list. On a corpus
file a premise that is a bare variable unifies with thousands of assertions, and the
product of two such premises is beyond memory. `--max-nodes N` (2,000,000 unless given)
leaves out a theorem for which the production engine makes more assertion nodes than
`N`. A theorem left out is reported and is not a disagreement.

`--assertions K` gives every theorem the first `K` assertions of the file as its
database instead of all those before it (the task's `limit`, which both engines
follow). The tuples of a theorem late in a file grow with the square of the assertions
before it, past what the reference engine can enumerate; with a database of a fixed
size the statement of every theorem of a file can be tested.
-/
import Whitehead
import Theory
import Theory.Convert

open Theory

namespace Diff

/-- Variables renamed by first occurrence, over a list of expressions together. -/
partial def canon (es : List Exp) : List Exp :=
  let rec go (m : List (Var × ℕ)) : Exp → Exp × List (Var × ℕ)
    | .var v =>
      match m.lookup v with
      | some k => (.var ⟨k, v.ty⟩, m)
      | none => (.var ⟨m.length, v.ty⟩, (v, m.length) :: m)
    | .const k t => (.const k t, m)
    | .app f t args =>
      let (args', m') := args.foldl (init := ([], m)) fun (acc, m) a =>
        let (a', m') := go m a
        (acc ++ [a'], m')
      (.app f t args', m')
  (es.foldl (init := ([], [])) fun (acc, m) e =>
    let (e', m') := go m e
    (acc ++ [e'], m')).1

/-- The shape of a reference proof. -/
partial def refShape (names : Array String) : PTree → String
  | .hyp h _ => s!"[h{h}]"
  | .step _ a _ [] => names[a]?.getD s!"a{a}"
  | .step _ a _ cs => s!"({names[a]?.getD s!"a{a}"} {" ".intercalate (cs.map (refShape names))})"

/-- The shape of a production proof; `none` for one with a conversion step. -/
partial def prodShape (db : Whitehead.Prove.Db) : Whitehead.Prove.ProofTree → Option String
  | .hyp h => some s!"[h{h}]"
  | .step a _ cs =>
    let name := db.asserts[a]!.name
    if cs.isEmpty then some name
    else
      let parts := cs.toList.mapM (prodShape db)
      parts.map fun ps => s!"({name} {" ".intercalate ps})"
  | .conv .. => none

/-- A proof at the root of either engine: its shape and its canonical answer. -/
structure Row where
  shape : String
  answer : String
  deriving BEq, Repr

def rowText (r : Row) : String := s!"{r.shape} with {r.answer}"

/-- The production engine for `n` rounds, breadth first, every proof at the root kept;
`none` when it made more than `maxNodes` assertion nodes, which stops it.
The root is expanded first, which makes the assertion nodes of depth 1; then `n` steps,
each expanding every assertion node made before it. The production engine makes the
children of an assertion node when it expands the node, matches them with the premises
then, and expands them against the assertions; so after `n` steps its proofs at the
root use the assertion nodes of depth up to `n` and the hypotheses at expression nodes
of depth up to `n` — the reference engine's entries after `n` rounds. The assertion
nodes of depth `n + 1` are not expanded within the `n` steps and give no proof, and on
a corpus file they are the bulk of the work; so the last step sees no assertions, and
makes none of them. -/
def runProduction (db : Whitehead.Prove.Db) (index : Whitehead.Prove.Index ℕ) (task : Whitehead.Prove.Task)
    (n cap maxNodes : ℕ) :
    IO (Option (Array Whitehead.Prove.Proof × Whitehead.Prove.Env × Array (Whitehead.Prove.Exp × ℕ × Whitehead.Prove.Subst))) := do
  let env := Whitehead.Prove.Env.init db index task
  -- the goal as a premise: the reference engine's leaf entries at the root
  let direct := (env.premises.unify env.task.goal).map fun u => (u.expr, u.data, u.sub)
  -- no (def, occurrence) steps: the reference engine has the judgment as assertions only
  let env := { env with tupleBudget := cap, workBudget := 0xFFFFFFFFFFFF, deadline := 0xFFFFFFFFFFFF,
                        convSteps := false }
  let mut env := (← (Whitehead.Prove.expandHyp 0 none).run env).2
  for k in [0:n] do
    if k + 1 == n then env := { env with assertions := {} }
    let leafs := env.leafs.filter fun p => !env.props[p]!.expanded
    env := env.dropExpanded
    for p in leafs do
      if env.props[p]!.expanded then continue
      env := (← (Whitehead.Prove.proveProp p none).run env).2
      if env.props.size > maxNodes then return none
  return some (env.rootProofs, env, direct)

/-- The rows of the production engine; and how many proofs had a conversion step. -/
def productionRows (db : Whitehead.Prove.Db) (env : Whitehead.Prove.Env) (proofs : Array Whitehead.Prove.Proof)
    (direct : Array (Whitehead.Prove.Exp × ℕ × Whitehead.Prove.Subst)) (terms : Array String) : Array Row × ℕ := Id.run do
  let mut rows : Array Row := #[]
  let mut convs := 0
  for (e, h, sub) in direct do
    let values := env.task.metas.toList.map fun m => Convert.exp (sub.apply (Whitehead.Prove.Exp.ofVar m))
    let answer := " ".intercalate ((canon (Convert.exp e :: values)).map (Convert.expText terms))
    rows := rows.push { shape := s!"[h{h}]", answer }
  for proof in proofs do
    let tree := Whitehead.Prove.makeProofTree env proof
    match prodShape db tree with
    | none => convs := convs + 1
    | some shape =>
      let values := (Whitehead.Prove.metaValues env proof).toList.map Convert.exp
      let answer := " ".intercalate ((canon (Convert.exp proof.expr :: values)).map (Convert.expText terms))
      rows := rows.push { shape, answer }
  return (rows, convs)

/-- The rows of the reference engine. -/
def referenceRows (dbm : Database) (names terms : Array String) (st : Statement) (metas : List Var)
    (s : State) (root : List Entry) : Array Row :=
  (root.map fun E =>
    let values := metas.map fun m => E.sub.apply (.var m)
    let answer := " ".intercalate ((canon (E.sub.apply st.concl :: values)).map (Convert.expText terms))
    { shape := refShape names (E.proof dbm s), answer }).toArray

/-- `State.sptE` of the reference engine with a cap on the tuples it visits: the entries
of an expression node down to a depth, together with the number of tuples of child
entries visited so far — the sum of the sizes of the products — or `none` once that
number passes the cap. The recursion is that of `sptE`, so where the cap is not reached
the entries are the same; the cap keeps a corpus theorem whose premises unify with
thousands of assertions from building millions of tuples as lists. -/
def sptEC (U : Unification) (st : Statement) (s : State) (cap : ℕ) :
    ℕ → ℕ → ℕ → Option (List Entry × ℕ)
  | 0, _, total => some ([], total)
  | fuel + 1, i, total => do
    let leaves := State.leafEntries U st i s.enodes[i]!.expr
    let (rest, total) ← (State.aChildren s i).foldlM (init := ([], total)) fun (acc, total) j => do
      let (childEntries, total) ← s.anodes[j]!.children.foldlM (init := ([], total)) fun (acc, total) c => do
        let (es, total) ← sptEC U st s cap fuel c total
        pure (acc ++ [es], total)
      let total := total + childEntries.foldl (· * ·.length) 1
      if total > cap then none
      else pure (acc ++ State.anodeEntries U st.consts j s.anodes[j]! childEntries, total)
    pure (leaves ++ rest, total)

/-- The reference engine for `n` rounds, and its entries at the root with the tuples
visited, or `none` when they passed the cap. Not inlined: the time is measured around
the call, and a pure value is otherwise computed where it is first used. -/
@[noinline] def runReference (dbm : Database) (st : Statement) (n cap : ℕ) :
    IO (State × Option (List Entry × ℕ)) := do
  let s := State.run Unify.postulate dbm st n
  let root := sptEC Unify.postulate st s cap s.enodes.size 0 0
  return (s, root)

structure Options where
  first : ℕ := 0
  last : ℕ := 1000000000
  every : ℕ := 1
  metas : Array ℕ := #[]
  maxTuples : ℕ := 1000000
  maxNodes : ℕ := 2000000
  assertions : ℕ := 1000000000
  verbose : Bool := false
  dump : Bool := false

def numOption (args : List String) (name : String) (default : ℕ) : ℕ :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => v.toNat?.getD default
  | _ => default

def numsOption (args : List String) (name : String) : Array ℕ :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => (v.splitOn ",").filterMap (·.toNat?) |>.toArray
  | _ => #[]

/-- What the test found for one theorem. -/
inductive Verdict where
  | agree
  | disagree
  /-- Over the limit of tuples or of assertion nodes in one of the engines: not run to
  the end. -/
  | leftOut

/-- One theorem. The production engine runs first, being the quicker, and says whether
the theorem is within the cap; then the reference engine. -/
def oneTheorem (db : Whitehead.Prove.Db) (index : Whitehead.Prove.Index ℕ) (idx n : ℕ) (opts : Options) : IO Verdict := do
  let name := db.asserts[idx]!.name
  let task := db.task idx opts.metas
  let task := { task with limit := min task.limit opts.assertions }
  let (dbm, names) := Convert.database db task
  let st := Convert.statement db task
  let terms := db.terms.map (·.name)
  let metas := task.metas.toList.map Convert.var
  let start ← IO.monoMsNow
  let some (proofs, env, direct) ← runProduction db index task n opts.maxTuples opts.maxNodes
    | IO.println s!"{name}: left out, the production engine over the limit of {opts.maxNodes} assertion nodes \
        ({(← IO.monoMsNow) - start} ms)"
      return .leftOut
  let prodMs := (← IO.monoMsNow) - start
  let (prodRows, convs) := productionRows db env proofs direct terms
  let prodText := s!"production {prodRows.size} proofs ({env.hyps.size} expression nodes, \
    {env.props.size} assertion nodes, {env.counters.tuples} tuples, {prodMs} ms)\
    {if convs > 0 then s!"; {convs} with a conversion step left out" else ""}"
  if env.overBudget || env.counters.tuples > opts.maxTuples then
    IO.println s!"{name}: left out, over the limit of {opts.maxTuples} tuples; {prodText}"
    return .leftOut
  let start ← IO.monoMsNow
  let (s, root?) ← runReference dbm st n opts.maxTuples
  let refMs := (← IO.monoMsNow) - start
  let some (root, refTuples) := root?
    | IO.println s!"{name}: left out, the reference engine over the limit of {opts.maxTuples} tuples \
        ({s.enodes.size} expression nodes, {s.anodes.size} assertion nodes, {refMs} ms); {prodText}"
      return .leftOut
  let refRows := referenceRows dbm names terms st metas s root
  -- the checks
  let missingRef := prodRows.filter fun r => !refRows.contains r
  let missingProd := refRows.filter fun r => !prodRows.any (·.answer == r.answer)
  let ok := missingRef.isEmpty && missingProd.isEmpty && prodRows.size ≤ refRows.size
  let verdict := if ok then "agree" else "DISAGREE"
  IO.println s!"{name}: {verdict}; reference {root.length} proofs at the root ({s.enodes.size} expression nodes, \
    {s.anodes.size} assertion nodes, {refTuples} tuples, {refMs} ms); {prodText}"
  if !ok || opts.verbose then
    for r in missingRef do
      IO.println s!"  production proof not a reference entry: {rowText r}"
    for r in missingProd do
      IO.println s!"  reference answer not among the production engine's: {rowText r}"
    if prodRows.size > refRows.size then
      IO.println s!"  the production engine has more proofs than the reference engine has entries"
  if opts.verbose then
    for r in refRows do IO.println s!"  reference: {rowText r}"
    for r in prodRows do IO.println s!"  production: {rowText r}"
  if opts.dump then
    IO.println s!"  production tree: {env.counters.duplicate} proofs dropped as duplicates by key"
    for i in [0:env.hyps.size] do
      let h := env.hyps[i]!
      IO.println s!"  e{i}: {Convert.expText terms (Convert.exp h.expr)}, parent {h.parent}, \
        {h.proofs.size} proofs, children {h.children}"
    for p in [0:env.props.size] do
      let pr := env.props[p]!
      IO.println s!"  a{p}: {pr.rule.name} at e{pr.parent}, children {pr.children}, {pr.proofs.size} proofs, \
        expanded {pr.expanded}"
  return (if ok then .agree else .disagree)

end Diff

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: rounds :: rest =>
    let file ←
      match Whitehead.Mmb.MmbFile.parse (← IO.FS.readBinFile path) with
      | .ok f => pure f
      | .error e =>
        IO.eprintln (e.format path)
        return 1
    let db ←
      match Whitehead.Prove.Db.ofFile file with
      | .ok d => pure d
      | .error m =>
        IO.eprintln s!"{path}: {m}"
        return 1
    let some n := rounds.toNat?
      | IO.eprintln "usage: diff-test <file.mmb> <rounds> [--from A] [--to B] [--every K] [--meta I,J,...] [--max-tuples N] [--max-nodes N] [--assertions K] [--verbose]"
        return 2
    let opts : Diff.Options :=
      { first := Diff.numOption rest "--from" 0, last := Diff.numOption rest "--to" 1000000000,
        every := max 1 (Diff.numOption rest "--every" 1), metas := Diff.numsOption rest "--meta",
        maxTuples := Diff.numOption rest "--max-tuples" 1000000, maxNodes := Diff.numOption rest "--max-nodes" 2000000,
        assertions := Diff.numOption rest "--assertions" 1000000000,
        verbose := rest.contains "--verbose", dump := rest.contains "--dump" }
    if !db.defs.isEmpty then
      match Convert.rulesMismatch db with
      | none => IO.println s!"{path}: {db.defs.size} definitions; the model's rules are the file's"
      | some m => IO.println s!"{path}: the model's rules are not the file's: {m}"
      for f in Convert.defsFaults db do IO.println s!"{path}: {f}"
    let index := db.index
    let mut total := 0
    let mut agreed := 0
    let mut leftOut := 0
    for i in [0:file.stmts.size] do
      let s := file.stmts[i]!
      let isThm := match s.kind with | .thm _ => true | _ => false
      if !(isThm && s.index ≥ opts.first && s.index < opts.last && s.index % opts.every == 0) then continue
      if !opts.metas.isEmpty then
        if let some _ := db.metasFault s.index opts.metas then continue
      total := total + 1
      match ← Diff.oneTheorem db index s.index n opts with
      | .agree => agreed := agreed + 1
      | .disagree => pure ()
      | .leftOut => leftOut := leftOut + 1
      -- a long run is read from a file as it goes
      (← IO.getStdout).flush
    IO.println s!"{path}: {total} theorems, {n} rounds\
      {if opts.assertions < 1000000000 then s!", the first {opts.assertions} assertions" else ""}: \
      {agreed} agree, {total - agreed - leftOut} disagree, \
      {leftOut} left out over the limits of {opts.maxTuples} tuples and {opts.maxNodes} assertion nodes"
    return (if agreed + leftOut == total then 0 else 1)
  | _ =>
    IO.eprintln "usage: diff-test <file.mmb> <rounds> [--from A] [--to B] [--every K] [--meta I,J,...] [--max-tuples N] [--max-nodes N] [--assertions K] [--verbose]"
    return 2
