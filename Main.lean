import Whitehead

open Whitehead

def usage : String :=
  "usage: mm0-whitehead <command> [arguments]

  dump <file.mm0>                print the parsed statements of a specification file
  join <file.mm0>                print a specification with its imports included
  dump <file.mmb>                print a decoded proof file: statements and proofs
  verify <file.mmb>              check the proofs of a proof file, without a specification
  verify <file.mm0> <file.mmb>   check that a proof file proves a specification
  prove replay <file.mmb> [-o out.mmb] [--from A] [--to B] [--every K] [--verbose]
               [--full [--others N|all]] [--ms T] [--max-nodes N] [--max-tuples N]
               [--total S [--factor F]] [--max-steps N]
                                 reconstruct the proofs of a file from the assertions they use
                                 (--every K: every K-th theorem of the range, a sample);
                                 --full: every node gets all its variants, the known proof's are
                                 expanded, and N (or all) others of each node on the way too
                                 (limits per theorem by default: 60 s, 2,000,000 nodes,
                                 300,000 joined proofs, 20,000,000 proofs looked at in joins
                                 (--max-work N)); --total S: rounds within S seconds, the first
                                 with the limits given (then 1 s, 100,000 nodes, 10,000 proofs,
                                 1,000,000 by default), each next with F (4) times those, on the
                                 theorems stopped at a limit; --max-steps N: proofs of more than N
                                 steps are left out
  dsl                            list the tactics and filters of the language of sessions
  mcp <file.mm0> <file.mmb> [--log FILE] [--anonymous]
                                 the MCP server for an AI agent, on stdin and stdout: sessions
                                 to prove the theorems of the file; --log: a trace of every
                                 message; --anonymous: assertions are shown as A and their
                                 number, but for the theorem a session starts on
  prove variants <file.mmb> [--from A] [--to B] [--every K] [--ms T] [--max-nodes N] [--shapes]
                                 how many variants the goal nodes on the paths of the known
                                 proofs have, each node expanded against the whole database:
                                 what a filter has to narrow; --shapes: and how many pass the
                                 filter that describes the known proof's new goals to depth 1,
                                 2 and 3
  prove subproofs <file.mmb> [--variants [--every K] [--ms T]]
                                 the distinct subproofs of the proofs (what is below a node), the
                                 most general lemma of each, and how much of each proof the
                                 proofs before it cover; --variants: what the lemmas of earlier
                                 proofs add to the variants at the nodes of known proofs
  prove rails <file.mmb> [--every K] [--to B] [--rank occurrences|size|small|reach]
                                 how far the subproofs of earlier proofs that fit the goal of a
                                 theorem agree with its known proof, for the first 1, 3 and 10
  prove search <file.mmb> [-o out.mmb] [--from A] [--to B] [--every K] [--ms T] [--max-nodes N]
               [--strategy bfs|forward|both] [--tactic T] [--max-facts N] [--join-cap N|all]
               [--meta I,J,...] [--verbose]
                                 prove the theorems of a file from scratch: backward breadth first,
                                 forward from the premises, or both in turn. --max-facts: the
                                 size of the forward front (512); --join-cap: how many facts a
                                 new subgoal is joined with when it is made (4). --meta: the binders
                                 with these numbers are metavariables, for which values are found;
                                 --tactic: a tactic of the language for every theorem (`dsl`),
                                 such as `seq(limited(replay(3), size=5000), bfs)`
                                 replay and search: [--jobs N] theorems at once (default: one per
                                 processor), [--max-mem GB] memory limit (default 32; above 80%
                                 the largest running theorem gives up, above 90% all running ones,
                                 above the limit all do and the process stops if memory does not
                                 come back within 15 s), [--quiet]
  prove db <file.mmb>            what the prover reads from a proof file
  prove chains <file.mmb> [--max-len K] [--min N] [--top T] [--mm0 file.mm0]
                                 mine the chains of steps of the proofs: how often each occurs, by
                                 length (up to K, 6), keeping those that occur N times (2), the T
                                 (10) most frequent listed; and the share of the steps on a chain.
                                 --mm0: the names from the specification, for a file without an index
  bench <file> ...               time the .mm0 front end or the .mmb reader on the given files"

-- Exit codes: 0 success, 1 the input was rejected, 2 the command line is wrong.

def dumpMm0 (path : String) : IO UInt32 := do
  let src ← IO.FS.readBinFile path
  match Mm0.parse src with
  | .ok stmts =>
    IO.print (Mm0.printStmts stmts)
    return 0
  | .error e =>
    IO.eprintln (e.format path src)
    return 1

def joinMm0 (path : String) : IO UInt32 := do
  match ← Mm0.load path with
  | .ok spec =>
    IO.print (Mm0.printStmts (spec.stmts.map (·.stmt)))
    return 0
  | .error e =>
    IO.eprintln e.format
    return 1

def dumpMmb (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let out ← IO.getStdout
  let result ←
    match Mmb.MmbFile.parse bytes with
    | .error e => pure (.error e)
    | .ok file => (Mmb.dump file fun line => out.putStrLn line).run
  match result with
  | .ok () => return 0
  | .error e =>
    out.flush
    IO.eprintln (e.format path)
    return 1

def dump (path : String) : IO UInt32 :=
  match (path : System.FilePath).extension with
  | some "mm0" => dumpMm0 path
  | some "mmb" => dumpMmb path
  | _ => do
    IO.eprintln s!"mm0-whitehead: dump: expected a .mm0 or .mmb file, got {path}"
    return 2

def benchMm0 (path : String) : IO UInt32 := do
  let src ← IO.FS.readBinFile path
  let start ← IO.monoNanosNow
  let result := Mm0.parse src
  let count ←
    match result with
    | .ok stmts => pure stmts.size
    | .error e =>
      IO.eprintln (e.format path src)
      return 1
  let nanos := (← IO.monoNanosNow) - start
  let micros := nanos / 1000
  let mbPerSec := if nanos == 0 then 0 else src.size * 1000 / nanos
  IO.println s!"{path}: {src.size} bytes, {count} statements, \
    parse {micros / 1000}.{(micros % 1000) / 100} ms, {mbPerSec} MB/s"
  -- the whole front end: imports resolved, every formula parsed
  let start ← IO.monoNanosNow
  let spec ←
    match ← Mm0.load path with
    | .ok spec => pure spec
    | .error e =>
      IO.eprintln e.format
      return 1
  match Mm0.elaborate spec with
  | .error e =>
    IO.eprintln e.format
    return 1
  | .ok env =>
    let micros := ((← IO.monoNanosNow) - start) / 1000
    IO.println s!"{path}: load and elaborate {micros / 1000}.{(micros % 1000) / 100} ms: \
      {env.sorts.size} sorts, {env.terms.size} terms, {env.thms.size} axioms and theorems"
  return 0

/-- Times opening a `.mmb` file and decoding every stream in it. -/
def benchMmb (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let start ← IO.monoNanosNow
  let file ←
    match Mmb.MmbFile.parse bytes with
    | .ok file => pure file
    | .error e =>
      IO.eprintln (e.format path)
      return 1
  let opened ← IO.monoNanosNow
  if let .error e := file.checkStreams then
    IO.eprintln (e.format path)
    return 1
  let done ← IO.monoNanosNow
  let ms (nanos : Nat) : String := s!"{nanos / 1000000}.{(nanos % 1000000) / 100000} ms"
  let nanos := done - start
  let mbPerSec := if nanos == 0 then 0 else bytes.size * 1000 / nanos
  IO.println s!"{path}: {bytes.size} bytes, {file.stmts.size} statements, \
    open {ms (opened - start)}, decode all streams {ms (done - opened)}, {mbPerSec} MB/s"
  return 0

/-- Checks the proofs of a `.mmb` file on their own. -/
def verifyMmb (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let start ← IO.monoNanosNow
  match Mmb.MmbFile.parse bytes with
  | .error e =>
    IO.eprintln (e.format path)
    return 1
  | .ok file =>
    match Verify.checkProofs file with
    | .error e =>
      IO.eprintln (e.format file path)
      return 1
    | .ok () =>
      let micros := ((← IO.monoNanosNow) - start) / 1000
      IO.println s!"{path}: {file.stmts.size} statements verified in {micros / 1000}.{(micros % 1000) / 100} ms \
        (proofs only: no specification was given)"
      return 0

/-- The verifier: the proofs of `mmb` are valid, and they prove what `mm0` states. -/
def verifyPair (mm0 mmb : String) : IO UInt32 := do
  let start ← IO.monoNanosNow
  let env ←
    match ← Mm0.load mm0 with
    | .error e =>
      IO.eprintln e.format
      return 1
    | .ok spec =>
      match Mm0.elaborate spec with
      | .error e =>
        IO.eprintln e.format
        return 1
      | .ok env => pure env
  let elaborated ← IO.monoNanosNow
  let bytes ← IO.FS.readBinFile mmb
  let file ←
    match Mmb.MmbFile.parse bytes with
    | .error e =>
      IO.eprintln (e.format mmb)
      return 1
    | .ok file => pure file
  if let .error e := Verify.checkProofs file then
    IO.eprintln (e.format file mmb)
    return 1
  let checked ← IO.monoNanosNow
  match Verify.matchSpec env file with
  | .error e =>
    IO.eprintln (e.format file mmb)
    return 1
  | .ok n =>
    let done ← IO.monoNanosNow
    let ms (a b : Nat) : String := s!"{(b - a) / 1000000}.{((b - a) % 1000000) / 100000} ms"
    IO.println s!"verified: {mmb} proves the {n} statements of {mm0}"
    IO.println s!"  specification {ms start elaborated}, proofs {ms elaborated checked}, \
      matching {ms checked done}, total {ms start done}"
    return 0

/-- `prove db`: what the prover reads from a proof file, with timings. -/
def proveDb (path : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let t0 ← IO.monoNanosNow
  let file ←
    match Mmb.MmbFile.parse bytes with
    | .ok file => pure file
    | .error e =>
      IO.eprintln (e.format path)
      return 1
  let db ←
    match Prove.Db.ofFile file with
    | .ok db => pure db
    | .error msg =>
      IO.eprintln s!"{path}: {msg}"
      return 1
  let t1 ← IO.monoNanosNow
  let ms (a b : Nat) : String := s!"{(b - a) / 1000000} ms"
  let nodes := db.asserts.foldl (init := 0) fun n a => a.hyps.foldl (init := n + a.concl.size) (· + ·.size)
  let pairs := db.asserts.foldl (init := 0) fun n a => n + a.disjs.size
  IO.println s!"{path}: {db.terms.size} terms, {db.asserts.size} assertions, {nodes} expression nodes, \
    {pairs} pairs of binders to keep apart ({ms t0 t1})"
  -- the index is built when its size is printed: a pure value is computed where it is used
  let t1 ← IO.monoNanosNow
  let index := db.index
  IO.print s!"index of the conclusions: {index.nodes.size} nodes"
  let t2 ← IO.monoNanosNow
  IO.println s!" ({ms t1 t2})"
  -- the proofs as trees of assertions
  let mut steps := 0
  let mut proofs := 0
  let mut withConv := 0
  let mut biggest := 0
  let mut over : Array Nat := #[0, 0, 0, 0]
  for s in file.stmts do
    if let .thm _ := s.kind then
      match db.skeleton s with
      | .error msg =>
        IO.eprintln s!"{path}: theorem {file.thmName s.index}: {msg}"
        return 1
      | .ok none => withConv := withConv + 1
      | .ok (some sk) =>
        let n := sk.size 100000000
        proofs := proofs + 1
        steps := steps + n
        biggest := max biggest n
        for k in [0:4] do
          if n > #[100, 1000, 10000, 100000][k]! then over := over.modify k (· + 1)
  let t3 ← IO.monoNanosNow
  IO.println s!"proofs: {proofs} as trees of {steps} steps, the largest {biggest}, {withConv} with a shared conversion left out; \
    more than 100 steps: {over[0]!}, 1,000: {over[1]!}, 10,000: {over[2]!}, 100,000: {over[3]!} ({ms t2 t3})"
  return 0

/-- A line of a report, written at once also when the output is a file: a search can
run for an hour. -/
def logLine (line : String) : IO Unit := do
  IO.println line
  (← IO.getStdout).flush

/-- The value of the option `name` among `args`, as a number. -/
def numOption (args : List String) (name : String) (default : Nat) : Nat :=
  match args.dropWhile (· != name) with
  | _ :: value :: _ => value.toNat?.getD default
  | _ => default

def strOption (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: value :: _ => some value
  | _ => none

/-- The number of processors (`nproc`); 1 if it cannot be found. -/
def processors : IO Nat := do
  try
    let out ← IO.Process.output { cmd := "nproc" }
    return (out.stdout.trimAscii.toString.toNat?).getD 1
  catch _ => return 1

/-- The options that `prove replay` and `prove search` share: how many theorems at once
(`--jobs`, by default one per processor), progress lines (`--quiet` turns them off), and
the memory the process may use (`--max-mem` in GB, by default 32; 0 for no limit). -/
def jobOptions (args : List String) : IO (Nat × Bool × Nat) := do
  let jobs := match strOption args "--jobs" with
    | some n => n.toNat?.getD 1
    | none => 0
  let jobs ← if jobs == 0 then processors else pure jobs
  return (max 1 jobs, !args.contains "--quiet", numOption args "--max-mem" 32 * 1000000000)

/-- `prove variants`: how many variants the goal nodes on the paths of the known proofs
have (`Prove/Measure.lean`). -/
def proveVariants (path : String) (args : List String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let file ←
    match Mmb.MmbFile.parse bytes with
    | .ok f => pure f
    | .error e =>
      IO.eprintln (e.format path)
      return 1
  let db ←
    match Prove.Db.ofFile file with
    | .ok db => pure db
    | .error msg =>
      IO.eprintln s!"{path}: {msg}"
      return 1
  let (jobs, progress, memLimit) ← jobOptions args
  let first := numOption args "--from" 0
  let last := numOption args "--to" 1000000000
  let every := max 1 (numOption args "--every" 1)
  let limits : Prove.Limits :=
    { maxProps := numOption args "--max-nodes" 2000000, maxMs := numOption args "--ms" 60000,
      maxTuples := numOption args "--max-tuples" 300000, maxWork := numOption args "--max-work" 20000000 }
  let todo := (Array.range file.stmts.size).filter fun i =>
    let s := file.stmts[i]!
    (match s.kind with | .thm _ => true | _ => false) && s.index ≥ first && s.index < last && s.index % every == 0
  let index := db.index
  let start ← IO.monoMsNow
  let depths := if args.contains "--shapes" then #[1, 2, 3] else #[]
  let uses := Prove.Uses.ofFile file db.asserts.size
  let results ← Prove.runJobs jobs todo.size (fun k => Prove.nodeCounts db index limits depths todo[k]! uses)
    progress memLimit logLine
  let nodes := results.foldl (init := #[]) fun acc r => match r with
    | some (c, _) => acc ++ c
    | none => acc
  let limited := (results.filter fun r => r.any (·.2)).size
  let left := (results.filter (·.isNone)).size
  IO.println s!"{path}: {todo.size} theorems, {left} with a shared conversion left out, {limited} stopped at a limit \
    (their nodes up to there counted), in {(← IO.monoMsNow) - start} ms"
  IO.println s!"  all variants: {Prove.variantSummary (nodes.map (·.variants))}"
  for j in [0:depths.size] do
    IO.println s!"  described to depth {depths[j]!}: {Prove.variantSummary (nodes.map (·.shaped[j]!))}"
  if !depths.isEmpty then
    IO.println s!"  nodes where the known proof's variant does not pass its description: \
      {(nodes.filter (!·.kept)).size}"
    -- the order by the uses in the proofs before the theorem: where the known variant is
    let none0 := nodes.filter (·.premises == 0)
    IO.println s!"  ordered by uses, the known variant among all: {Prove.rankSummary (nodes.map (·.rankAll))}"
    for j in [0:depths.size] do
      IO.println s!"  ordered by uses, among those described to depth {depths[j]!}: \
        {Prove.rankSummary (nodes.map (·.ranks[j]!))}"
    IO.println s!"  steps without premises, ordered by uses, among all: {Prove.rankSummary (none0.map (·.rankAll))}; \
      among those described: {Prove.rankSummary (none0.map (·.ranks.back!))}"
  return 0

/-- `prove subproofs`: the distinct subproofs of a file, their lemmas, how much of the
proofs earlier proofs cover, and what the lemmas would add to the variants
(`Prove/Subproofs.lean`). -/
def proveSubproofs (path : String) (args : List String) : IO UInt32 := do
  let file ←
    match Mmb.MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e =>
      IO.eprintln (e.format path)
      return 1
  let db ←
    match Prove.Db.ofFile file with
    | .ok db => pure db
    | .error msg =>
      IO.eprintln s!"{path}: {msg}"
      return 1
  let (jobs, progress, memLimit) ← jobOptions args
  let t0 ← IO.monoMsNow
  let sp := Prove.Subproofs.ofDb db
  let lemmas := sp.lemmas db
  let r := sp.report lemmas
  let pct (n d : Nat) : String := if d == 0 then "0" else s!"{n * 1000 / d / 10}.{n * 1000 / d % 10}%"
  -- the report is computed when it is first used
  IO.println s!"{path}: {r.proofs} proofs, {r.distinct} distinct subproofs"
  IO.println s!"  lemmas: {r.failed} not made; {r.bare} with a bare variable for conclusion; \
    {r.statements} distinct statements"
  IO.println s!"  nodes of 2 steps or more, each subproof once per proof: {r.nodes}, \
    {r.coveredNodes} ({pct r.coveredNodes r.nodes}) a subproof of an earlier theorem's proof"
  IO.println s!"  steps: {r.steps}, {r.coveredSteps} ({pct r.coveredSteps r.steps}) inside such a subproof; \
    each subproof once per proof: {r.distinctSteps}, {r.coveredDistinct} ({pct r.coveredDistinct r.distinctSteps}); \
    proofs that are one, whole: {r.wholeCovered} ({pct r.wholeCovered r.proofs})"
  IO.println s!"  subproofs in 2 proofs or more: {r.recurring}, in 10 or more: {r.recurring10}; \
    steps inside a subproof that 2 earlier proofs have: {r.coveredRecurring} ({pct r.coveredRecurring r.steps}), \
    each subproof once per proof: {r.coveredRecurringDistinct} ({pct r.coveredRecurringDistinct r.distinctSteps})"
  IO.println s!"  in {(← IO.monoMsNow) - t0} ms"
  if args.contains "--variants" then
    let lemmaIx := sp.lemmaIndex lemmas
    let recurringIx := sp.lemmaIndex lemmas (recurring := true)
    let every := max 1 (numOption args "--every" 40)
    let limits : Prove.Limits := { maxProps := numOption args "--max-nodes" 2000000, maxMs := numOption args "--ms" 10000 }
    let todo := (Array.range file.stmts.size).filter fun i =>
      (match file.stmts[i]!.kind with | .thm _ => true | _ => false) && file.stmts[i]!.index % every == 0
    let index := db.index
    let results ← Prove.runJobs jobs todo.size (fun k => Prove.lemmaCounts db index lemmaIx recurringIx limits todo[k]!)
      progress memLimit logLine
    let rows := results.foldl (init := #[]) fun acc r => acc ++ r.getD #[]
    IO.println s!"  at the goal nodes of the known proofs of every {every}th theorem:"
    IO.println s!"    assertions: {Prove.variantSummary (rows.map (·.1))}"
    IO.println s!"    lemmas of earlier proofs: {Prove.variantSummary (rows.map (·.2.1))}"
    IO.println s!"    lemmas that 2 earlier proofs have: {Prove.variantSummary (rows.map (·.2.2))}"
    IO.println s!"    assertions and those lemmas: {Prove.variantSummary (rows.map fun (a, _, c) => a + c)}"
  return 0

/-- `prove rails`: how good the subproofs are that fit the goal of a theorem: how far the
best of the first `count` agrees with the theorem's known proof (`Rails.agree`). -/
def proveRails (path : String) (args : List String) : IO UInt32 := do
  let file ←
    match Mmb.MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e =>
      IO.eprintln (e.format path)
      return 1
  let db ←
    match Prove.Db.ofFile file with
    | .ok db => pure db
    | .error msg =>
      IO.eprintln s!"{path}: {msg}"
      return 1
  let rails := Prove.Rails.ofDb db
  let every := max 1 (numOption args "--every" 10)
  let last := numOption args "--to" 1000000000
  let index := db.index
  let pct (n d : Nat) : String := if d == 0 then "0" else s!"{n * 1000 / d / 10}.{n * 1000 / d % 10}%"
  let rank := match strOption args "--rank" with
    | some "reach" => Prove.RailRank.reach
    | some "size" => .size
    | some "small" => .small
    | _ => .occurrences
  for count in [1, 3, 10] do
    let cfg : Prove.ReplayConfig := { count, rank }
    let mut n := 0
    let mut fit := 0
    let mut top := 0
    let mut half := 0
    let mut whole := 0
    for (thm, root) in rails.sp.roots do
      if thm % every != 0 || thm ≥ last then continue
      n := n + 1
      let env := Prove.Env.init db index (db.task thm)
      let found := rails.at_ env 0 cfg
      if found.isEmpty then continue
      fit := fit + 1
      let best := found.foldl (init := 0) fun m k => max m (rails.agree k root)
      let size := rails.sp.sizes[root]!
      if best ≥ 1 then top := top + 1
      if 2 * best ≥ size then half := half + 1
      if best == size then whole := whole + 1
    IO.println s!"{path}: {n} theorems, every {every}th; the first {count} subproofs at the goal, by {repr rank}:"
    IO.println s!"  some fit: {fit} ({pct fit n}); the best agrees with the known proof in its first step: {top} \
      ({pct top n}), in half its steps or more: {half} ({pct half n}), in all: {whole} ({pct whole n})"
  return 0

/-- `prove replay`: reconstructs the proofs of a file from the assertions they use. -/
def proveReplay (path : String) (args : List String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let file ←
    match Mmb.MmbFile.parse bytes with
    | .ok file => pure file
    | .error e =>
      IO.eprintln (e.format path)
      return 1
  let db ←
    match Prove.Db.ofFile file with
    | .ok db => pure db
    | .error msg =>
      IO.eprintln s!"{path}: {msg}"
      return 1
  let (jobs, progress, memLimit) ← jobOptions args
  let total := numOption args "--total" 0
  let opts : Prove.ReplayOptions :=
    { first := numOption args "--from" 0, last := numOption args "--to" 1000000000,
      every := max 1 (numOption args "--every" 1),
      maxSteps := numOption args "--max-steps" 1000000000, verbose := args.contains "--verbose",
      full := args.contains "--full",
      others := if strOption args "--others" == some "all" then none else some (numOption args "--others" 0),
      jobs, progress, memLimit, total := total * 1000, factor := numOption args "--factor" 4,
      -- a join takes about 5 KB per tuple, and may have a tenth of the memory
      tupleCap := memLimit / 50000,
      -- the full expansion can grow without bound: it has limits unless told otherwise;
      -- in rounds, small ones to begin with
      limits := if args.contains "--full" then
          if total > 0 then
            { maxProps := numOption args "--max-nodes" 100000, maxMs := numOption args "--ms" 1000,
              maxTuples := numOption args "--max-tuples" 10000, maxWork := numOption args "--max-work" 1000000 }
          else
          { maxProps := numOption args "--max-nodes" 2000000, maxMs := numOption args "--ms" 60000,
            maxTuples := numOption args "--max-tuples" 300000, maxWork := numOption args "--max-work" 20000000 }
        else
          { maxProps := numOption args "--max-nodes" 1000000000, maxMs := numOption args "--ms" 1000000000,
            maxTuples := numOption args "--max-tuples" 0xFFFFFFFFFFFF } }
  let start ← IO.monoMsNow
  let (stats, bodies) ← Prove.replay db opts logLine
  let ms := (← IO.monoMsNow) - start
  IO.println s!"{path}: {stats.theorems} theorems, {stats.replayed} replayed, {stats.failed} not replayed\
, \
    {stats.conversions} with a shared conversion and {stats.tooLarge} too large left out, in {ms} ms\
    {if total > 0 then s!" over {stats.rounds} rounds" else ""}"
  IO.println s!"  steps of the known proofs {stats.stepsIn}, of the reconstructed ones {stats.stepsOut}; \
    proof bodies {stats.bytesIn} bytes before, {stats.bytesOut} after"
  let c := stats.counters
  IO.println s!"  assertion nodes {c.props}, expanded {c.expanded}; tuples of proofs {c.tuples}: \
    {c.notUnified} not unified, {c.disjoint} against a disjoint variable condition, \
    {c.inconsistent} inconsistent, {c.duplicate} with the key of another; root proofs rejected by the verifier {stats.rejected}"
  if opts.full then
    IO.println s!"  full expansion, {match opts.others with | none => "all" | some n => toString n} other variants \
      expanded per node: {stats.otherProofs} proofs found are not the known one; {stats.limited} theorems stopped at a limit\
      {if stats.memoryLimited == 0 then "" else s!", {stats.memoryLimited} of them by memory"}"
  if let some out := strOption args "-o" then
    IO.FS.writeBinFile out (file.withBodies bodies)
    IO.println s!"  written to {out}"
  return if stats.failed == 0 then 0 else 1

/-- The numbers of the option `name` among `args`, separated by commas. -/
def numsOption (args : List String) (name : String) : Array Nat :=
  match strOption args name with
  | some value => ((value.splitOn ",").filterMap (·.toNat?)).toArray
  | none => #[]

/-- `prove search`: proves the theorems of a file from scratch, breadth first. -/
def proveSearch (path : String) (args : List String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let file ←
    match Mmb.MmbFile.parse bytes with
    | .ok file => pure file
    | .error e =>
      IO.eprintln (e.format path)
      return 1
  let db ←
    match Prove.Db.ofFile file with
    | .ok db => pure db
    | .error msg =>
      IO.eprintln s!"{path}: {msg}"
      return 1
  let (jobs, progress, memLimit) ← jobOptions args
  let opts : Prove.SearchOptions :=
    { first := numOption args "--from" 0, last := numOption args "--to" 1000000000,
      every := max 1 (numOption args "--every" 1),
      strategy := (strOption args "--strategy").getD "bfs",
      limits := { maxProps := numOption args "--max-nodes" 100000, maxMs := numOption args "--ms" 1000,
                  maxFacts := numOption args "--max-facts" 512,
                  joinCap := if strOption args "--join-cap" == some "all" then 0xFFFFFFFFFFFF
                    else numOption args "--join-cap" 4 },
      metas := numsOption args "--meta",
      verbose := args.contains "--verbose", jobs, progress, memLimit }
  -- the marks must fit every theorem of the range
  for a in db.asserts do
    if a.id ≥ opts.first && a.id < opts.last && a.id % opts.every == 0 then
      if let some why := db.metasFault a.id opts.metas then
        IO.eprintln s!"{path}: --meta: {why}"
        return 1
  -- a tactic of the language, for every theorem; with `replay`, the subproofs of the file
  let tactic := strOption args "--tactic"
  let rails : Option Prove.Rails :=
    if tactic.any fun t => (t.splitOn "replay").length > 1 || (t.splitOn "rails").length > 1 then
      some (Prove.Rails.ofDb db) else none
  let ctx (thm : Nat) : Prove.Dsl.Ctx := { db, thm, rails }
  if let some text := tactic then
    if let .error e := Prove.Dsl.parseTactic (ctx 0) text then
      IO.eprintln (Prove.Dsl.ParseError.show text e)
      return 1
  -- read again for each theorem, whose variables a pattern may name
  let custom : Option (Nat → Prove.AnyStrategy) := tactic.map fun text thm =>
    match Prove.Dsl.parseTactic (ctx thm) text with
    | .ok t => t
    | .error _ => ⟨Prove.Strategy.done⟩
  let uses := Prove.Uses.ofFile file db.asserts.size
  let start ← IO.monoMsNow
  let (rows, bodies) ← Prove.searchAll db opts logLine custom uses
  let ms := (← IO.monoMsNow) - start
  let proved := rows.filter (·.ending == .proved)
  let steps := proved.foldl (init := 0) (· + ·.steps)
  let known := proved.foldl (init := 0) (· + ·.knownSteps)
  IO.println s!"{path}: {rows.size} theorems, {proved.size} proved, \
    {(rows.filter (·.ending == .limit)).size} stopped at the limit \
    ({opts.limits.maxProps} assertion nodes, {opts.limits.maxMs} ms), \
    {(rows.filter (·.ending == .exhausted)).size} with nothing left to expand, in {ms} ms"
  IO.println s!"  steps of the proofs found {steps}, of the proofs in the file for the same theorems {known}; \
    proofs rejected by the verifier {rows.foldl (init := 0) (· + ·.rejected)}"
  if !opts.metas.isEmpty then
    IO.println "  with metavariables a proof proves an instance of its theorem: it is not written or checked"
  if let some out := strOption args "-o" then
    IO.FS.writeBinFile out (file.withBodies bodies)
    IO.println s!"  written to {out}"
  return 0

/-- `prove chains`: the chains of steps of the proofs and how often each occurs. -/
def proveChains (path : String) (args : List String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let file ←
    match Mmb.MmbFile.parse bytes with
    | .ok file => pure file
    | .error e =>
      IO.eprintln (e.format path)
      return 1
  let db ←
    match Prove.Db.ofFile file with
    | .ok db => pure db
    | .error msg =>
      IO.eprintln s!"{path}: {msg}"
      return 1
  -- the set.mm translation has no index: its names are in the specification
  let db ←
    match strOption args "--mm0" with
    | none => pure db
    | some mm0 =>
      match ← Mm0.load mm0 with
      | .error e =>
        IO.eprintln e.format
        return 1
      | .ok spec =>
        match Mm0.elaborate spec with
        | .error e =>
          IO.eprintln e.format
          return 1
        | .ok env =>
          pure <| (Verify.specNames env file).foldl (init := db) fun db (i, name) =>
            if i < db.asserts.size then { db with asserts := db.asserts.modify i fun a => { a with name } } else db
  let opts : Prove.ChainOptions :=
    { maxLen := max 2 (numOption args "--max-len" 6), min := max 1 (numOption args "--min" 2),
      top := numOption args "--top" 10 }
  let start ← IO.monoMsNow
  let stats ←
    match Prove.mineChains db opts with
    | .ok s => pure s
    | .error msg =>
      IO.eprintln s!"{path}: {msg}"
      return 1
  let pct (n d : Nat) : String := if d == 0 then "0" else s!"{n * 1000 / d / 10}.{n * 1000 / d % 10}"
  IO.println s!"{path}: {stats.proofs} proofs, {stats.steps} steps; chains of 2 to {opts.maxLen} steps, \
    frequent from {opts.min} occurrences, in {(← IO.monoMsNow) - start} ms"
  for l in stats.lengths do
    IO.println s!"length {l.len}: {l.occurrences} occurrences, {l.counted} counted (the upper part frequent), \
      {l.toRoot} of them to the root and {l.fromHyp} from a hypothesis; \
      {l.frequent} frequent chains with {l.frequentOccurrences} occurrences ({pct l.frequentOccurrences l.occurrences}%)"
    for (key, n, proofs) in l.top do
      IO.println s!"  {n} in {proofs} proofs  {Prove.chainText db key}"
  for (t, n) in stats.covered do
    IO.println s!"steps on a chain of 2 or more steps that occurs at least {t} times: {n} ({pct n stats.steps}%)"
  return 0

/-- `mcp`: the MCP server for an agent, on stdin and stdout (`Mcp/Server.lean`). -/
def mcpServe (mm0 mmb : String) (args : List String) : IO UInt32 := do
  match ← Mcp.Ctx.load mm0 mmb (anonymous := args.contains "--anonymous") with
  | .error msg =>
    IO.eprintln msg
    return 1
  | .ok c =>
    match strOption args "--log" with
    | some path =>
      IO.FS.withFile path .append fun h => Mcp.serve c (some h)
    | none => Mcp.serve c
    return 0

def bench (path : String) : IO UInt32 :=
  if (path : System.FilePath).extension == some "mmb" then benchMmb path else benchMm0 path

def main (args : List String) : IO UInt32 := do
  match args with
  | ["dump", path] => dump path
  | ["join", path] => joinMm0 path
  | "bench" :: path :: paths =>
    let mut code : UInt32 := 0
    for p in path :: paths do
      code := max code (← bench p)
    return code
  | ["verify", path] => verifyMmb path
  | ["verify", mm0, mmb] => verifyPair mm0 mmb
  | ["prove", "db", path] => proveDb path
  | ["dsl"] =>
    IO.print Prove.Dsl.help
    return 0
  | "mcp" :: mm0 :: mmb :: rest => mcpServe mm0 mmb rest
  | "prove" :: "replay" :: path :: rest => proveReplay path rest
  | "prove" :: "search" :: path :: rest => proveSearch path rest
  | "prove" :: "chains" :: path :: rest => proveChains path rest
  | "prove" :: "variants" :: path :: rest => proveVariants path rest
  | "prove" :: "subproofs" :: path :: rest => proveSubproofs path rest
  | "prove" :: "rails" :: path :: rest => proveRails path rest
  | _ =>
    IO.eprintln usage
    return 2
