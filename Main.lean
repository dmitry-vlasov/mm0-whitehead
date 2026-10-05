import Whitehead

open Whitehead

def usage : String :=
  "usage: mm0-whitehead <command> [arguments]

  dump <file.mm0>                print the parsed statements of a specification file
  join <file.mm0>                print a specification with its imports included
  dump <file.mmb>                print a decoded proof file: statements and proofs
  verify <file.mmb>              check the proofs of a proof file, without a specification
  verify <file.mm0> <file.mmb>   check that a proof file proves a specification
  prove replay <file.mmb> [-o out.mmb] [--from A] [--to B] [--verbose]
                                 reconstruct the proofs of a file from the assertions they use
  prove search <file.mmb> [-o out.mmb] [--from A] [--to B] [--every K] [--ms T] [--max-nodes N]
               [--strategy bfs|forward|both] [--max-facts N] [--meta I,J,...] [--verbose]
                                 prove the theorems of a file from scratch: backward breadth first,
                                 forward from the premises, or both in turn. --meta: the binders
                                 with these numbers are metavariables, for which values are found
  prove db <file.mmb>            what the prover reads from a proof file
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
  IO.println s!"proofs: {proofs} without conversions, {withConv} with; as trees {steps} steps, the largest {biggest}; \
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
  let opts : Prove.ReplayOptions :=
    { first := numOption args "--from" 0, last := numOption args "--to" 1000000000,
      maxSteps := numOption args "--max-steps" 1000000000, verbose := args.contains "--verbose" }
  let start ← IO.monoMsNow
  let (stats, bodies) ← Prove.replay db opts logLine
  let ms := (← IO.monoMsNow) - start
  IO.println s!"{path}: {stats.theorems} theorems, {stats.replayed} replayed, {stats.failed} not replayed, \
    {stats.conversions} with conversions and {stats.tooLarge} too large left out, in {ms} ms"
  IO.println s!"  steps of the known proofs {stats.stepsIn}, of the reconstructed ones {stats.stepsOut}; \
    proof bodies {stats.bytesIn} bytes before, {stats.bytesOut} after"
  let c := stats.counters
  IO.println s!"  assertion nodes {c.props}, expanded {c.expanded}; tuples of proofs {c.tuples}: \
    {c.notUnified} not unified, {c.disjoint} against a disjoint variable condition, \
    {c.inconsistent} inconsistent, {c.duplicate} duplicates; root proofs rejected by the verifier {stats.rejected}"
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
  let opts : Prove.SearchOptions :=
    { first := numOption args "--from" 0, last := numOption args "--to" 1000000000,
      every := max 1 (numOption args "--every" 1),
      strategy := (strOption args "--strategy").getD "bfs",
      limits := { maxProps := numOption args "--max-nodes" 100000, maxMs := numOption args "--ms" 1000,
                  maxFacts := numOption args "--max-facts" 512 },
      metas := numsOption args "--meta",
      verbose := args.contains "--verbose" }
  -- the marks must fit every theorem of the range
  for a in db.asserts do
    if a.id ≥ opts.first && a.id < opts.last && a.id % opts.every == 0 then
      if let some why := db.metasFault a.id opts.metas then
        IO.eprintln s!"{path}: --meta: {why}"
        return 1
  let start ← IO.monoMsNow
  let (rows, bodies) ← Prove.searchAll db opts logLine
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
  IO.println s!"  proofs of assertion nodes made {rows.foldl (init := 0) (· + ·.made)}, of them not kept, \
    having the whole substitution of another, {rows.foldl (init := 0) (· + ·.duplicate)}"
  if !opts.metas.isEmpty then
    IO.println "  with metavariables a proof proves an instance of its theorem: it is not written or checked"
  if let some out := strOption args "-o" then
    IO.FS.writeBinFile out (file.withBodies bodies)
    IO.println s!"  written to {out}"
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
  | "prove" :: "replay" :: path :: rest => proveReplay path rest
  | "prove" :: "search" :: path :: rest => proveSearch path rest
  | _ =>
    IO.eprintln usage
    return 2
