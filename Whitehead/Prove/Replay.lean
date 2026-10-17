/-
The replay test: every proof of a file is reduced to the tree of the assertions it uses
(`Db.skeleton`), and the engine reconstructs it, finding all expressions by unification
(`oracle` in `Prove.lean`). The result is the file with the reconstructed proof bodies
in the place of the original ones.
-/
import Whitehead.Mmb.Write
import Whitehead.Prove.Prove
import Whitehead.Prove.Combinators

namespace Whitehead.Prove

open Whitehead.Mmb

structure ReplayOptions where
  /-- The theorems to replay: those with numbers in `[first, last)`. -/
  first : Nat := 0
  last : Nat := 1000000000
  /-- Only every `every`-th theorem of the range: a sample. -/
  every : Nat := 1
  /-- Proofs with more steps than this, counted as a tree, are left out. -/
  maxSteps : Nat := 1000000000
  /-- Report every theorem that is not reconstructed. -/
  verbose : Bool := false
  /-- Over the full expansion (`oracleAll`): every node gets all its variants, the
  known proof's are clicked, and the first proof at the root that the verifier accepts
  counts, known or not (`otherProofs` says which). Otherwise each node gets the known
  proof's variant alone (`oracle`). -/
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
  /-- The memory the process may use, in bytes; 0 for no limit (`watchMemory`). -/
  memLimit : Nat := 0
  /-- The time of the whole replay, in milliseconds: it then runs in rounds, the first
  with `limits`, every next with `factor` times the limits of the one before, on the
  theorems that stopped at a limit; 0 for one round. The tuples of a join are made at
  once, so their budget is one of memory; it grows up to `tupleCap` (0: without end). -/
  total : Nat := 0
  factor : Nat := 4
  tupleCap : Nat := 0

structure ReplayStats where
  /-- Theorems with a proof in the range. -/
  theorems : Nat := 0
  replayed : Nat := 0
  failed : Nat := 0
  /-- Left out: the proof shares a conversion (`ConvCut`), or is larger than `maxSteps`. -/
  conversions : Nat := 0
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
  limit, of which those stopped for the memory of the process. -/
  otherProofs : Nat := 0
  limited : Nat := 0
  memoryLimited : Nat := 0
  /-- For one theorem: the limit that stopped it. -/
  stop : Option Stop := none
  /-- The rounds run (`ReplayOptions.total`). -/
  rounds : Nat := 0
  counters : Counters := {}
  deriving Inhabited

namespace Counters

def add (a b : Counters) : Counters :=
  { props := a.props + b.props, expanded := a.expanded + b.expanded, tuples := a.tuples + b.tuples,
    notUnified := a.notUnified + b.notUnified, disjoint := a.disjoint + b.disjoint,
    inconsistent := a.inconsistent + b.inconsistent, duplicate := a.duplicate + b.duplicate,
    work := a.work + b.work, badCandidates := a.badCandidates + b.badCandidates,
    facts := a.facts + b.facts, joins := a.joins + b.joins }

end Counters

namespace ReplayStats

def add (a b : ReplayStats) : ReplayStats :=
  { theorems := a.theorems + b.theorems, replayed := a.replayed + b.replayed, failed := a.failed + b.failed,
    conversions := a.conversions + b.conversions,
    tooLarge := a.tooLarge + b.tooLarge, stepsIn := a.stepsIn + b.stepsIn, stepsOut := a.stepsOut + b.stepsOut,
    bytesIn := a.bytesIn + b.bytesIn, bytesOut := a.bytesOut + b.bytesOut, rejected := a.rejected + b.rejected,
    otherProofs := a.otherProofs + b.otherProofs, limited := a.limited + b.limited,
    memoryLimited := a.memoryLimited + b.memoryLimited, rounds := a.rounds + b.rounds,
    counters := a.counters.add b.counters }

end ReplayStats

/-- The resident memory of this process, in bytes (`/proc/self/statm`); 0 if it cannot be
read. -/
def residentBytes : IO Nat := do
  try
    let text ← IO.FS.readFile "/proc/self/statm"
    match (text.splitOn " ")[1]? >>= String.toNat? with
    | some pages => return pages * 4096
    | none => return 0
  catch _ => return 0

/-- Watches the memory of the process until `stop` is set. Above 80% of `limit` bytes
the largest running search gives up as at a limit, above 90% every one does, which
frees their memory (`memoryLevel`). Above `limit`, every one gives up, and the process
ends if the memory has not come back under the limit within 15 s: a search looks at
the level between expansions and along a join, and one step can take more than the
memory left. -/
partial def watchMemory (limit : Nat) (stop : IO.Ref Bool) (log : String → IO Unit) : IO Unit := do
  if ← stop.get then return
  let mut rss ← residentBytes
  if rss > limit then
    memoryLevel.set 2
    log s!"memory: {rss / 1000000} MB in use, over the limit of {limit / 1000000} MB; every search gives up"
    let mut waited := 0
    while rss > limit && waited < 15000 do
      IO.sleep 250
      waited := waited + 250
      rss ← residentBytes
    if rss > limit then
      log s!"memory: {rss / 1000000} MB in use after {waited} ms, still over the limit; stopping"
      IO.Process.exit 3
  memoryLevel.set (if rss * 10 > limit * 9 then 2 else if rss * 10 > limit * 8 then 1 else 0)
  IO.sleep 250
  watchMemory limit stop log

/-- Runs `f` on `0 .. count-1` with `jobs` workers, each on a thread of its own; a worker
takes the next number when it has finished one. The results are in the order of the
numbers, whatever the order of the work. With `progress`, a line every ten seconds; with
`memLimit` (bytes, 0 for none), the memory is watched (`watchMemory`). -/
def runJobs {β : Type} [Inhabited β] (jobs count : Nat) (f : Nat → IO β) (progress : Bool) (memLimit : Nat)
    (log : String → IO Unit) (name : Nat → String := toString) : IO (Array β) := do
  let next ← IO.mkRef 0
  let done ← IO.mkRef 0
  let stop ← IO.mkRef false
  -- what each worker is doing, and since when
  let current ← IO.mkRef (Array.replicate (max 1 jobs) (none : Option (Nat × Nat)))
  let watcher ← if memLimit > 0 then some <$> IO.asTask (watchMemory memLimit stop log) (prio := .dedicated)
    else pure none
  let worker (w : Nat) : IO (Array (Nat × β)) := do
    let mut out := #[]
    while true do
      let k ← next.modifyGet fun k => (k, k + 1)
      if k ≥ count then break
      let t ← IO.monoMsNow
      current.modify (·.set! w (some (k, t)))
      out := out.push (k, ← f k)
      current.modify (·.set! w none)
      done.modify (· + 1)
    return out
  let start ← IO.monoMsNow
  let tasks ← (Array.range (max 1 jobs)).mapM fun w => IO.asTask (worker w) (prio := .dedicated)
  if progress then
    let mut last := start
    while !(← tasks.allM fun t => (IO.hasFinished t : IO Bool)) do
      IO.sleep 200
      let now ← IO.monoMsNow
      if now - last ≥ 10000 then
        last := now
        -- the items that have run for more than a minute
        let long := (← current.get).filterMap fun c => c.bind fun (k, t) =>
          if now - t > 60000 then some s!"{name k} for {(now - t) / 1000} s" else none
        log s!"  ... {← done.get} of {count}, {(now - start) / 1000} s\
          {if long.isEmpty then "" else "; running long: " ++ ", ".intercalate long.toList}"
  let mut results : Array β := Array.replicate count default
  for t in tasks do
    match ← IO.wait t with
    | .ok r => for (k, b) in r do results := results.set! k b
    | .error e => stop.set true; throw e
  stop.set true
  if let some w := watcher then discard <| IO.wait w
  return results

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
    let start ← IO.monoMsNow
    let result ←
      if opts.full then
        -- every proof that reaches the root is checked by the verifier, which tests the
        -- joins. The first that passes counts: it need not be the known proof, which
        -- may have been one of two with the same key (`proofKey`)
        searchWith (accept vc) env (oracleAll skel opts.others) opts.limits
      else search vc env (oracle skel) opts.limits
    let c := result.env.counters
    let ms := (← IO.monoMsNow) - start
    if opts.verbose && ms ≥ 5000 then
      lines := lines.push s!"slow: theorem {s.index} {name} ({steps} steps): {ms} ms, \
        {c.props} assertion nodes, {c.expanded} expanded, {c.tuples} tuples"
    stats := { stats with
      rejected := result.rejected,
      otherProofs := (match result.proof with
        | some t => if sameShape t skel then 0 else 1
        | none => 0),
      limited := if result.ending == .limit then 1 else 0,
      memoryLimited := if result.ending == .limit && result.stop == some .memory then 1 else 0,
      stop := if result.ending == .limit then result.stop else none,
      counters := c }
    match result.body, result.proof with
    | some body, some tree =>
      return ({ stats with replayed := 1, stepsIn := steps, stepsOut := tree.size,
                           bytesIn := s.stop - s.bodyStart, bytesOut := body.size }, some body, #[])
    | _, _ =>
      stats := { stats with failed := 1 }
      if opts.verbose then
        let why := match result.ending with
          | .proved => "proved"
          | .exhausted => "the tree has no proof"
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
a line every ten seconds says how far it has got.

With `total`, the replay runs in rounds: the first with `limits` per theorem, every
next with `factor` times the limits of the one before (time, nodes, tuples, work), on
the theorems that stopped at a limit in the round before — until none is left, or the
time `total` is out, which also ends the searches of the round under way. Most proofs
are replayed within a small budget; the few that need more get it without the rest
waiting for them, and without a budget chosen in advance. A theorem's statistics are
those of its last round.

Only a theorem whose limit grows in the next round is tried again: the tuple budget
stops at `tupleCap`. A theorem stopped for the memory of the process was stopped by
what ran beside it (the largest of those running, or all of them when memory was very
short): it waits, and when nothing else is left, a round with a quarter as many at
once takes the waiting ones, down to one at once, where memory is the limit and the
rounds end. -/
def replay (db : Db) (opts : ReplayOptions) (log : String → IO Unit) :
    IO (ReplayStats × Array (Option ByteArray)) := do
  let f := db.file
  let vc := Verify.Ctx.ofFile f
  let index := db.index
  let todo := (Array.range f.stmts.size).filter fun i =>
    let s := f.stmts[i]!
    (match s.kind with | .thm _ => true | _ => false) && s.index ≥ opts.first && s.index < opts.last &&
      s.index % opts.every == 0
  let name (i : Nat) := s!"theorem {f.stmts[i]!.index} {f.thmName f.stmts[i]!.index}"
  let start ← IO.monoMsNow
  let deadline := if opts.total == 0 then none else some (start + opts.total)
  let mut results : Array (ReplayStats × Option ByteArray × Array String) := Array.replicate todo.size default
  -- the places in `todo` still to replay
  let mut pending := Array.range todo.size
  let mut limits := opts.limits
  let mut jobs := opts.jobs
  let mut rounds := 0
  -- stopped for memory, to be tried again with fewer at once
  let mut waiting : Array Nat := #[]
  while true do
    rounds := rounds + 1
    let roundStart ← IO.monoMsNow
    let roundOpts := { opts with limits := { limits with deadline } }
    let round ← runJobs jobs pending.size (fun k => do
        -- past the time of the whole run a theorem is not started: it stays at a limit
        if let some d := deadline then
          if (← IO.monoMsNow) ≥ d then return ({ theorems := 1, failed := 1, limited := 1 }, none, #[])
        -- nor while memory is short: it would give up at once
        while (← memoryLevel.get) ≥ 1 do IO.sleep 100
        replayOne db vc index roundOpts todo[pending[k]!]!)
      opts.progress opts.memLimit log (fun k => name todo[pending[k]!]!)
    let nextTuples := if opts.tupleCap == 0 then limits.maxTuples * opts.factor
      else min (limits.maxTuples * opts.factor) opts.tupleCap
    -- the theorems at a limit: those whose limit grows next round, and those stopped
    -- for memory
    let mut left := 0
    let mut growing := #[]
    let mut byMemory := #[]
    let mut replayed := 0
    for k in [0:pending.size] do
      let r := round[k]!
      results := results.set! pending[k]! r
      replayed := replayed + r.1.replayed
      if r.1.limited == 1 then
        left := left + 1
        match r.1.stop with
        | some .memory => byMemory := byMemory.push pending[k]!
        | some .tuples => if nextTuples > limits.maxTuples then growing := growing.push pending[k]!
        | _ => growing := growing.push pending[k]!
    let now ← IO.monoMsNow
    if deadline.isSome then
      log s!"  round {rounds}: {limits.maxMs} ms, {limits.maxProps} nodes, {limits.maxTuples} tuples, \
        {limits.maxWork} work per theorem, {jobs} at once: {pending.size} theorems, {replayed} replayed, \
        {left} at a limit, {byMemory.size} of them by memory, in {now - roundStart} ms"
    waiting := waiting ++ byMemory
    if (left == 0 && waiting.isEmpty) || deadline.all (now ≥ ·) then break
    if growing.isEmpty then
      -- memory is what stopped everything left: fewer at once, or the end
      if waiting.isEmpty || jobs == 1 then break
      jobs := max 1 (jobs / 4)
      pending := waiting
      waiting := #[]
    else pending := growing
    limits := { limits with maxMs := limits.maxMs * opts.factor, maxProps := limits.maxProps * opts.factor,
                            maxTuples := nextTuples, maxWork := limits.maxWork * opts.factor }
  let mut stats : ReplayStats := { rounds }
  let mut bodies : Array (Option ByteArray) := Array.replicate f.stmts.size none
  for k in [0:todo.size] do
    let (st, body, lines) := results[k]!
    stats := stats.add st
    if let some b := body then bodies := bodies.set! todo[k]! (some b)
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
  /-- How many theorems are searched at once, progress lines, the memory limit: as in
  `ReplayOptions`. With several jobs the time limit of a theorem is wall-clock time
  shared with the others. -/
  jobs : Nat := 1
  progress : Bool := false
  memLimit : Nat := 0

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
  deriving Inhabited

/-- Searches for a proof of every theorem of `db.file` in the range, each from the
assertions before it, with the strategy of `opts`, or with the tactic that `custom` gives
for the theorem (a tactic of the language, `Dsl.lean`). `uses` is for the `used` filters
of a tactic. Returns a row per theorem and the new proof bodies. -/
def searchAll (db : Db) (opts : SearchOptions) (log : String → IO Unit)
    (custom : Option (Nat → AnyStrategy) := none) (uses : Uses := {}) :
    IO (Array SearchRow × Array (Option ByteArray)) := do
  let f := db.file
  let vc := Verify.Ctx.ofFile f
  let index := db.index
  let hypIndexes := if opts.strategy == "bfs" && custom.isNone then {} else db.hypIndexes
  let todo := (Array.range f.stmts.size).filter fun i =>
    let s := f.stmts[i]!
    (match s.kind with | .thm _ => true | _ => false) && s.index ≥ opts.first && s.index < opts.last &&
      s.index % opts.every == 0
  let one (i : Nat) : IO (SearchRow × Option ByteArray × Array String) := do
    let s := f.stmts[i]!
    let known := match db.skeleton s with
      | .ok (some skel) => skel.size
      | _ => 0
    let start ← IO.monoMsNow
    let task := db.task s.index opts.metas
    let env := { Env.init db index task hypIndexes with uses }
    -- with metavariables what is proved is an instance of the theorem: nothing to check
    -- against, and no body for the file
    let accept := if task.metas.isEmpty then accept vc else acceptAny
    let result ← match custom with
      | some mk =>
        let t := mk s.index
        searchWith accept env t.strategy opts.limits
      | none =>
        if opts.strategy == "forward" then searchWith accept env forwardOnly opts.limits
        else if opts.strategy == "both" then searchWith accept env bidirectional opts.limits
        else searchWith accept env breadthFirst opts.limits
    let ms := (← IO.monoMsNow) - start
    let steps := (result.proof.map (·.size)).getD 0
    let body := if task.metas.isEmpty then result.body else none
    let row : SearchRow :=
      { thm := s.index, name := f.thmName s.index, ending := result.ending, steps, knownSteps := known, ms,
        props := result.env.props.size, rejected := result.rejected,
        facts := result.env.counters.facts, joins := result.env.counters.joins }
    let mut lines := #[]
    if opts.verbose then
      let what := match result.ending with
        | .proved => s!"proved in {steps} steps (the file has {known})"
        | .exhausted => s!"nothing left to expand (the file has {known})"
        | .limit => s!"limit reached (the file has {known})"
      let c := result.env.counters
      lines := lines.push s!"{row.name}: {what}; {row.props} assertion nodes, {ms} ms; \
        {c.expanded} expanded, {result.env.hyps.size} expression nodes, {c.tuples} tuples, {c.work} work\
        {if row.rejected == 0 then "" else s!", {row.rejected} proofs rejected by the verifier"}\
        {if opts.strategy == "bfs" then "" else s!", {row.facts} facts, {row.joins} joins"}"
      if result.ending == .proved && !task.metas.isEmpty then
        let names := f.thmVarNames s.index
        let found := (Array.range task.metas.size).map fun j =>
          s!"{Db.varName (Node.varId task.metas[j]!)} := {db.showExp result.values[j]! names}"
        lines := lines.push s!"  found {", ".intercalate found.toList}; proved {(result.answer.map (db.showExp · names)).getD ""}"
    return (row, body, lines)
  let results ← runJobs opts.jobs todo.size (fun k => one todo[k]!) opts.progress opts.memLimit log
  let mut rows : Array SearchRow := #[]
  let mut bodies : Array (Option ByteArray) := Array.replicate f.stmts.size none
  for k in [0:todo.size] do
    let (row, body, lines) := results[k]!
    rows := rows.push row
    if let some b := body then bodies := bodies.set! todo[k]! (some b)
    for l in lines do log l
  return (rows, bodies)

end Whitehead.Prove
