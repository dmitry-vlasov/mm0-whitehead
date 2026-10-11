/-
The replay test: every proof of a file is reduced to the tree of the assertions it uses
(`Db.skeleton`), and the engine reconstructs it, finding all expressions by unification
(`oracle` in `Prove.lean`). The result is the file with the reconstructed proof bodies
in the place of the original ones.
-/
import Whitehead.Mmb.Write
import Whitehead.Prove.Prove

namespace Whitehead.Prove

open Whitehead.Mmb

structure ReplayOptions where
  /-- The theorems to replay: those with numbers in `[first, last)`. -/
  first : Nat := 0
  last : Nat := 1000000000
  /-- Proofs with more steps than this, counted as a tree, are left out. -/
  maxSteps : Nat := 1000000000
  /-- Report every theorem that is not reconstructed. -/
  verbose : Bool := false
  /-- Over the full expansion (`oracleAll`): every node gets all its variants, the
  known proof's are clicked, and only the known proof is accepted. Otherwise each node
  gets the known proof's variant alone (`oracle`). -/
  full : Bool := false
  /-- With `full`: how many other variants of each node on the path are expanded too
  (`none`: all). -/
  others : Option Nat := some 0
  /-- The limits per theorem. -/
  limits : Limits := {}
  /-- How many theorems are replayed at once. -/
  jobs : Nat := 1
  /-- Say every ten seconds how far the replay has got. -/
  progress : Bool := false

structure ReplayStats where
  /-- Theorems with a proof in the range. -/
  theorems : Nat := 0
  replayed : Nat := 0
  failed : Nat := 0
  /-- Left out: the proof shares a conversion (`ConvCut`), or is larger than `maxSteps`. -/
  conversions : Nat := 0
  /-- Among those not replayed: the known proof unfolds a def at a place that the tree
  has as a variable, where the expansion offers no unfolding. -/
  convInVariable : Nat := 0
  tooLarge : Nat := 0
  /-- Steps of the known proofs that were replayed, and of the reconstructed ones. -/
  stepsIn : Nat := 0
  stepsOut : Nat := 0
  /-- Bytes of the original bodies of the replayed theorems, and of the new ones. -/
  bytesIn : Nat := 0
  bytesOut : Nat := 0
  /-- Proofs that reached the root and that the verifier did not accept. -/
  rejected : Nat := 0
  /-- With `full`: proofs found that are not the known one, and theorems stopped at a
  limit. -/
  otherProofs : Nat := 0
  limited : Nat := 0
  counters : Counters := {}

/-- For a replay that found no proof: does a step of the known proof unfold a def at a
place that the tree has as a variable? The tree is walked along the known proof, as the
oracle expanded it. -/
partial def convInVariable (env : Env) (h : Nat) (s : Skeleton) : Bool :=
  let hyp := env.hyps[h]!
  let under (p : Nat) (children : Array Skeleton) : Bool :=
    let hyps := env.props[p]!.children
    (Array.range (min children.size hyps.size)).any fun i => convInVariable env hyps[i]! children[i]!
  match s with
  | .hyp _ => false
  | .conv t path unfold child =>
    match hyp.expr.nodeAt path with
    | none => true
    | some pos =>
      if Node.isVar hyp.expr.nodes[pos]! then true
      else match hyp.children.find? fun p => env.props[p]!.step == .conv t pos unfold with
        | some p => under p #[child]
        | none => false
  | .step t children =>
    match hyp.children.find? fun p => env.props[p]!.step == .assertion t with
    | some p => under p children
    | none => false

namespace Counters

def add (a b : Counters) : Counters :=
  { props := a.props + b.props, expanded := a.expanded + b.expanded, tuples := a.tuples + b.tuples,
    notUnified := a.notUnified + b.notUnified, disjoint := a.disjoint + b.disjoint,
    inconsistent := a.inconsistent + b.inconsistent, duplicate := a.duplicate + b.duplicate,
    facts := a.facts + b.facts, joins := a.joins + b.joins }

end Counters

namespace ReplayStats

def add (a b : ReplayStats) : ReplayStats :=
  { theorems := a.theorems + b.theorems, replayed := a.replayed + b.replayed, failed := a.failed + b.failed,
    conversions := a.conversions + b.conversions, convInVariable := a.convInVariable + b.convInVariable,
    tooLarge := a.tooLarge + b.tooLarge, stepsIn := a.stepsIn + b.stepsIn, stepsOut := a.stepsOut + b.stepsOut,
    bytesIn := a.bytesIn + b.bytesIn, bytesOut := a.bytesOut + b.bytesOut, rejected := a.rejected + b.rejected,
    otherProofs := a.otherProofs + b.otherProofs, limited := a.limited + b.limited,
    counters := a.counters.add b.counters }

end ReplayStats

/-- Replays the proof of statement `i` of the file, a theorem. Returns what it adds to
the statistics, the new proof body, and the lines for the log. -/
def replayOne (db : Db) (vc : Verify.Ctx) (index : Index Nat) (opts : ReplayOptions) (i : Nat) :
    IO (ReplayStats × Option ByteArray × Array String) := do
  let f := db.file
  let s := f.stmts[i]!
  let mut stats : ReplayStats := { theorems := 1 }
  let mut lines : Array String := #[]
  let name := f.thmName s.index
  match db.skeleton s with
  | .error msg => throw (IO.userError s!"theorem {name}: {msg}")
  | .ok none => return ({ stats with conversions := 1 }, none, #[])
  | .ok (some skel) =>
    let steps := skel.size (opts.maxSteps + 1)
    if steps > opts.maxSteps then return ({ stats with tooLarge := 1 }, none, #[])
    let env := Env.init db index (db.task s.index)
    let result ←
      if opts.full then
        -- every proof that reaches the root is checked by the verifier, which tests the
        -- joins. The first that passes counts: it need not be the known proof, which
        -- may have been one of two with the same key (`proofKey`)
        searchWith (accept vc) env (oracleAll skel opts.others) opts.limits
      else search vc env (oracle skel) opts.limits
    let c := result.env.counters
    stats := { stats with
      rejected := result.rejected,
      otherProofs := (match result.proof with
        | some t => if sameShape t skel then 0 else 1
        | none => 0),
      limited := if result.ending == .limit then 1 else 0,
      counters := c }
    match result.body, result.proof with
    | some body, some tree =>
      return ({ stats with replayed := 1, stepsIn := steps, stepsOut := tree.size,
                           bytesIn := s.stop - s.bodyStart, bytesOut := body.size }, some body, #[])
    | _, _ =>
      let atVar := convInVariable result.env 0 skel
      stats := { stats with failed := 1, convInVariable := if atVar then 1 else 0 }
      if opts.verbose then
        let why := match result.ending with
          | .proved => "proved"
          | .exhausted => if atVar then "an unfolding where the tree has a variable" else "the tree has no proof"
          | .limit => "limit reached"
        lines := lines.push s!"not replayed: theorem {s.index} {name} ({steps} steps): {why}; \
          {c.props} assertion nodes, {c.tuples} tuples, {c.notUnified} not unified, {c.disjoint} disjointness, \
          {c.inconsistent} inconsistent, {result.rejected} rejected by the verifier\
          {if result.rejection.isEmpty then "" else ": " ++ result.rejection}"
        if let some tree := result.rejectedProof then
          lines := lines.push s!"  goal: {db.showExp env.task.goal}\n  premises: {env.task.premises.map (db.showExp ·)}\n{tree.render db "  "}"
      return (stats, none, lines)

/-- Replays the proofs of `db.file`. Returns the statistics and, for every statement of
the file, the new proof body if its proof was reconstructed.

With `jobs` above one, that many theorems are replayed at once, each on a thread of its
own: every theorem has a search state of its own, and the database and the index are
only read. A worker takes the next theorem when it has finished one. With `progress`,
a line every ten seconds says how far it has got. -/
def replay (db : Db) (opts : ReplayOptions) (log : String → IO Unit) :
    IO (ReplayStats × Array (Option ByteArray)) := do
  let f := db.file
  let vc := Verify.Ctx.ofFile f
  let index := db.index
  let todo := (Array.range f.stmts.size).filter fun i =>
    let s := f.stmts[i]!
    (match s.kind with | .thm _ => true | _ => false) && s.index ≥ opts.first && s.index < opts.last
  let next ← IO.mkRef 0
  let done ← IO.mkRef 0
  let worker : IO (Array (Nat × ReplayStats × Option ByteArray × Array String)) := do
    let mut out := #[]
    while true do
      let k ← next.modifyGet fun k => (k, k + 1)
      if k ≥ todo.size then break
      let r ← replayOne db vc index opts todo[k]!
      out := out.push (todo[k]!, r)
      done.modify (· + 1)
    return out
  let start ← IO.monoMsNow
  let tasks ← (Array.range (max 1 opts.jobs)).mapM fun _ => IO.asTask worker (prio := .dedicated)
  if opts.progress then
    let mut last := start
    while !(← tasks.allM fun t => (IO.hasFinished t : IO Bool)) do
      IO.sleep 200
      let now ← IO.monoMsNow
      if now - last ≥ 10000 then
        last := now
        log s!"  ... {← done.get} of {todo.size} theorems, {(now - start) / 1000} s"
  let mut results := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok r => results := results ++ r
    | .error e => throw e
  let mut stats : ReplayStats := {}
  let mut bodies : Array (Option ByteArray) := Array.replicate f.stmts.size none
  for (i, (st, body, lines)) in results.qsort (·.1 < ·.1) do
    stats := stats.add st
    if let some b := body then bodies := bodies.set! i (some b)
    for l in lines do log l
  return (stats, bodies)

/-! ### The search test -/

structure SearchOptions where
  first : Nat := 0
  last : Nat := 1000000000
  /-- Only every `every`-th theorem of the range: a sample. -/
  every : Nat := 1
  /-- `"bfs"`: the backward tree, breadth first; `"forward"`: the forward front alone;
  `"both"`: a round of the one and a wave of the other in turn. -/
  strategy : String := "bfs"
  limits : Limits := {}
  /-- The binders, by their numbers, that are metavariables in every theorem of the
  range (`Db.task`): the stub for a marking that MM0 has no syntax for. A proof found
  for such a task is reported, and not written or checked. -/
  metas : Array Nat := #[]
  /-- Report every theorem. -/
  verbose : Bool := false

/-- What the search test reports for one theorem. -/
structure SearchRow where
  thm : Nat
  name : String
  ending : Ending
  /-- The steps of the proof found, and of the proof in the file. -/
  steps : Nat
  knownSteps : Nat
  ms : Nat
  props : Nat
  rejected : Nat
  /-- Facts of the forward front, and joins of a fact with a subgoal or the goal. -/
  facts : Nat := 0
  joins : Nat := 0

/-- Searches for a proof of every theorem of `db.file` in the range, each from the
assertions before it, with the strategy of `opts`. Returns a row per theorem and the new
proof bodies. -/
def searchAll (db : Db) (opts : SearchOptions) (log : String → IO Unit) :
    IO (Array SearchRow × Array (Option ByteArray)) := do
  let f := db.file
  let vc := Verify.Ctx.ofFile f
  let index := db.index
  let hypIndexes := if opts.strategy == "bfs" then {} else db.hypIndexes
  let mut rows : Array SearchRow := #[]
  let mut bodies : Array (Option ByteArray) := Array.replicate f.stmts.size none
  for i in [0:f.stmts.size] do
    let s := f.stmts[i]!
    let isThm := match s.kind with
      | .thm _ => true
      | _ => false
    if !isThm || s.index < opts.first || s.index ≥ opts.last || s.index % opts.every != 0 then continue
    let known := match db.skeleton s with
      | .ok (some skel) => skel.size
      | _ => 0
    let start ← IO.monoMsNow
    let task := db.task s.index opts.metas
    let env := Env.init db index task hypIndexes
    -- with metavariables what is proved is an instance of the theorem: nothing to check
    -- against, and no body for the file
    let accept := if task.metas.isEmpty then accept vc else acceptAny
    let result ←
      if opts.strategy == "forward" then searchWith accept env forwardOnly opts.limits
      else if opts.strategy == "both" then searchWith accept env bidirectional opts.limits
      else searchWith accept env breadthFirst opts.limits
    let ms := (← IO.monoMsNow) - start
    let steps := (result.proof.map (·.size)).getD 0
    if task.metas.isEmpty then
      if let some body := result.body then bodies := bodies.set! i (some body)
    let row : SearchRow :=
      { thm := s.index, name := f.thmName s.index, ending := result.ending, steps, knownSteps := known, ms,
        props := result.env.props.size, rejected := result.rejected,
        facts := result.env.counters.facts, joins := result.env.counters.joins }
    rows := rows.push row
    if opts.verbose then
      let what := match result.ending with
        | .proved => s!"proved in {steps} steps (the file has {known})"
        | .exhausted => "nothing left to expand"
        | .limit => "limit reached"
      log s!"{row.name}: {what}; {row.props} assertion nodes, {ms} ms\
        {if row.rejected == 0 then "" else s!", {row.rejected} proofs rejected by the verifier"}\
        {if opts.strategy == "bfs" then "" else s!", {row.facts} facts, {row.joins} joins"}"
      if result.ending == .proved && !task.metas.isEmpty then
        let names := f.thmVarNames s.index
        let found := (Array.range task.metas.size).map fun j =>
          s!"{Db.varName (Node.varId task.metas[j]!)} := {db.showExp result.values[j]! names}"
        log s!"  found {", ".intercalate found.toList}; proved {(result.answer.map (db.showExp · names)).getD ""}"
  return (rows, bodies)

end Whitehead.Prove
