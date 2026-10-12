/-
`lake exe thorough`: the thorough layer of the tests, for the prover. `lake test` is the
fast layer: fixtures and samples, in seconds. This layer runs the prover over every
proof file there is, within a time (`--minutes`, 30 by default):

1. the replay test on every file in full: every proof reconstructed from the assertions
   it uses, and the file with the new bodies accepted by our verifier, matched against
   its specification where one lies beside it, and accepted by `mm0-rs`;
2. the search test on samples: every K-th theorem (`--every`, 10 by default) of the
   first two parts of set.mm, backward and in both directions, and of `peano`, proved
   from scratch in 1 s each, one search per physical core as `scripts/search-baseline.sh`
   runs them; every proof found is checked as above, and the fraction proved has a floor
   that only a gross regression would go under;
3. the replay over the full expansion (`prove replay --full --total`), in rounds within
   a share of the time: the small files in full, the large ones (`bigFile` theorems and
   more) with the stride, smallest first and each with the share of the time left that
   its sample is of the samples left, so that what a file gives back goes to the larger
   ones. No tuple of the known proof may fail to unify and no proof may be rejected; a
   few theorems may stop at a limit (`limitedPercent`), and are named.

Needs the corpus of `scripts/build-corpus.sh`; `MM0_REPO` adds the proof files of the
MM0 repository; `.tools/bin/mm0-rs` (`scripts/build-oracles.sh`) adds its verdicts. The
files with the new bodies are left in `--out` (`.tools/thorough`).

    lake exe thorough [--minutes M] [--every K] [--jobs N] [--cores N] [--max-mem GB]
                      [--out DIR] [--mm0-rs PATH]
-/
import Std.Data.HashSet
import Whitehead
import Tests.Harness
import Tests.Mmb.Corpus

open Whitehead Whitehead.Mmb Whitehead.Prove Tests

namespace Tests.Thorough

structure Options where
  minutes : Nat := 30
  every : Nat := 10
  /-- Theorems at once in the replays (0: one per processor) and in the searches (0:
  one per physical core: a search with a time limit gets less done when two share a
  core). -/
  jobs : Nat := 0
  cores : Nat := 0
  /-- The memory the process may use, in bytes (`--max-mem`, in GB). -/
  memLimit : Nat := 32 * 1000000000
  out : String := ".tools/thorough"
  mm0rs : String := ".tools/bin/mm0-rs"

def usage : String :=
  "usage: lake exe thorough [--minutes M] [--every K] [--jobs N] [--cores N] [--max-mem GB] [--out DIR] [--mm0-rs PATH]"

partial def parseArgs (o : Options) : List String → Except String Options
  | [] => .ok o
  | "--minutes" :: n :: rest => parseArgs { o with minutes := n.toNat! } rest
  | "--every" :: n :: rest => parseArgs { o with every := max 1 n.toNat! } rest
  | "--jobs" :: n :: rest => parseArgs { o with jobs := n.toNat! } rest
  | "--cores" :: n :: rest => parseArgs { o with cores := n.toNat! } rest
  | "--max-mem" :: n :: rest => parseArgs { o with memLimit := n.toNat! * 1000000000 } rest
  | "--out" :: p :: rest => parseArgs { o with out := p } rest
  | "--mm0-rs" :: p :: rest => parseArgs { o with mm0rs := p } rest
  | arg :: _ => .error s!"unexpected argument {arg}"

/-- The number of processors (`nproc`); 1 if it cannot be found. -/
def processors : IO Nat := do
  try
    let out ← IO.Process.output { cmd := "nproc", args := #[] }
    return (out.stdout.trimAscii.toString.toNat?).getD 1
  catch _ => return 1

/-- The number of physical cores (`lscpu`); the processors if it cannot be found. -/
def physicalCores : IO Nat := do
  try
    let out ← IO.Process.output { cmd := "lscpu", args := #["-p=Core,Socket"] }
    let lines := (out.stdout.splitOn "\n").filter fun l => !l.isEmpty && !l.startsWith "#"
    let distinct := lines.foldl (init := ({} : Std.HashSet String)) (·.insert ·)
    if distinct.size > 0 then return distinct.size
  catch _ => pure ()
  processors

/-- A proof file the layer runs on. -/
structure Input where
  /-- The name in the reports: the file's stem, with its directory for a file of the
  MM0 repository. -/
  name : String
  path : System.FilePath
  file : MmbFile
  db : Db
  /-- Matches a file with new bodies against the specification beside the input, if
  there is one: `none` if it matches, else the message. -/
  spec : Option (MmbFile → Option String)
  /-- Theorems with a proof. -/
  theorems : Nat

/-- Reads a proof file. A file that the verifier rejects (`hello_assembler`, proved with
`sorry`) is skipped: its proofs cannot all be replayed. -/
def load (name : String) (path : System.FilePath) (mm0 : Option System.FilePath) : TestM (Option Input) := do
  let file ←
    match MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e =>
      check s!"{name}: the file is read" false (e.format path.toString)
      return none
  if let .error e := Verify.checkProofs file then
    skip name s!"the verifier rejects the file: {e.format file path.toString}"
    return none
  let db ←
    match Db.ofFile file with
    | .ok db => pure db
    | .error msg =>
      check s!"{name}: the file becomes a database" false msg
      return none
  let mut spec : Option (MmbFile → Option String) := none
  if let some mm0 := mm0 then
    match ← Mm0.load mm0 with
    | .error e => check s!"{name}: the specification is read" false e.format
    | .ok s =>
      match Mm0.elaborate s with
      | .error e => check s!"{name}: the specification elaborates" false e.format
      | .ok env =>
        spec := some fun f =>
          match Verify.matchSpec env f with
          | .ok _ => none
          | .error e => some (e.format f name)
  let theorems := file.stmts.foldl (init := 0) fun n s => match s.kind with | .thm _ => n + 1 | _ => n
  return some { name, path, file, db, spec, theorems }

/-- A file with new bodies is written to `out`, read, accepted by our verifier, matched
against the specification, and accepted by `mm0-rs` if it is there. -/
def validate (o : Options) (mm0rs : Option String) (inp : Input) (kind : String) (bytes : ByteArray) : TestM Unit := do
  let what := s!"{kind} {inp.name}"
  let out : System.FilePath := o.out / s!"{inp.name.replace "/" "_"}.{kind}.mmb"
  IO.FS.writeBinFile out bytes
  match MmbFile.parse bytes with
  | .error e => check s!"{what}: the file with the new bodies is read" false e.msg
  | .ok f2 =>
    match Verify.checkProofs f2 with
    | .ok () => check s!"{what}: the file with the new bodies is valid" true
    | .error e => check s!"{what}: the file with the new bodies is valid" false (e.format f2 out.toString)
    if let some spec := inp.spec then
      match spec f2 with
      | none => check s!"{what}: the file with the new bodies proves its specification" true
      | some msg => check s!"{what}: the file with the new bodies proves its specification" false msg
  if let some rs := mm0rs then
    let r ← IO.Process.output { cmd := rs, args := #["compile", "-q", out.toString] }
    check s!"{what}: mm0-rs accepts the file with the new bodies" (r.exitCode == 0) (r.stdout ++ r.stderr)

/-- 1. The replay of every proof of a file: each node with the known proof's variant. -/
def replayAll (o : Options) (mm0rs : Option String) (jobs : Nat) (inp : Input) : TestM Unit := do
  let start ← IO.monoMsNow
  let (stats, bodies) ← replay inp.db { jobs, progress := true, memLimit := o.memLimit } IO.println
  check s!"replay {inp.name}: every proof without a shared conversion is reconstructed"
    (stats.failed == 0 && stats.rejected == 0 && stats.replayed + stats.conversions == stats.theorems)
    s!"{stats.replayed} of {stats.theorems} replayed, {stats.failed} not, {stats.rejected} rejected, \
      {stats.conversions} with a shared conversion"
  checkEq s!"replay {inp.name}: step for step" stats.stepsOut stats.stepsIn
  validate o mm0rs inp "replay" (inp.file.withBodies bodies)
  IO.println s!"replay {inp.name}: {stats.replayed} of {stats.theorems} proofs reconstructed, \
    {stats.conversions} with a shared conversion left out, in {(← IO.monoMsNow) - start} ms"

/-- The end of predicate calculus in the set.mm translation: the number of `ax_ext`, as
`scripts/search-baseline.sh` has it (for the translation that `scripts/build-corpus.sh`
was run on; `mm0-whitehead dump` shows the numbers of another). -/
def setmmPredicateEnd : Nat := 2825

/-- 2. The search test on a sample: every `every`-th theorem of the range, 1 s each. The
floor on the fraction proved is well under what the baseline measures (`STATUS.md`:
about 46% of this sample of set.mm backward, 55% in both directions, 36% of `peano`),
and catches a gross regression only: the number proved in a second varies with the
machine. -/
def searchSample (o : Options) (mm0rs : Option String) (cores : Nat) (inp : Input) (strategy : String)
    (last : Nat) (floorPercent : Nat) : TestM Unit := do
  let what := s!"search {inp.name} {strategy} every {o.every}th"
  let start ← IO.monoMsNow
  let (rows, bodies) ← searchAll inp.db
    { last, every := o.every, strategy, limits := { maxProps := 2000000, maxMs := 1000 },
      jobs := cores, progress := true, memLimit := o.memLimit } IO.println
  let proved := rows.filter (·.ending == .proved)
  check s!"{what}: no proof is rejected by the verifier" (rows.all (·.rejected == 0))
    s!"{rows.foldl (init := 0) (· + ·.rejected)} rejected"
  check s!"{what}: at least {floorPercent}% of the sample is proved"
    (proved.size * 100 ≥ floorPercent * rows.size) s!"{proved.size} of {rows.size}"
  validate o mm0rs inp s!"search-{strategy}" (inp.file.withBodies bodies)
  let steps := proved.foldl (init := 0) (· + ·.steps)
  let known := proved.foldl (init := 0) (· + ·.knownSteps)
  IO.println s!"{what}: {proved.size} of {rows.size} proved in 1 s each; {steps} steps found, \
    {known} in the file for the same theorems; in {(← IO.monoMsNow) - start} ms"

/-- The limits of the first round of a replay over the full expansion, as
`prove replay --full --total` has them; each next round has four times those. -/
def roundLimits : Limits := { maxProps := 100000, maxMs := 1000, maxTuples := 10000, maxWork := 1000000 }

/-- A file with this many theorems or more gets the stride in the full replay. -/
def bigFile : Nat := 6000

/-- How many theorems of a full replay, in percent, may stop at a limit within their
share of the time. The whole of set.mm has 2.9% at a limit after two hours, and every
tenth theorem 3.7% after 13 minutes and 2.1% after 25 (`DESIGN.md`, "The replay over
the full expansion", "Two layers"); the example files with definitions stay under 1%. -/
def limitedPercent : Nat := 5

/-- 3. The replay over the full expansion of every `every`-th proof of a file, in rounds
within `totalMs`. -/
def fullReplay (o : Options) (mm0rs : Option String) (jobs : Nat) (inp : Input) (every : Nat) (totalMs : Nat) :
    TestM Unit := do
  let what := s!"full replay {inp.name}{if every > 1 then s!" every {every}th" else ""}"
  let start ← IO.monoMsNow
  -- `verbose`: every theorem not reconstructed is reported, with the limit that stopped it
  let (stats, bodies) ← replay inp.db
    { full := true, others := some 0, every, jobs, progress := true, memLimit := o.memLimit,
      total := totalMs, factor := 4, tupleCap := o.memLimit / 50000, limits := roundLimits, verbose := true }
    IO.println
  check s!"{what}: every tuple of the known proof unifies and no proof is rejected"
    (stats.failed == stats.limited && stats.rejected == 0)
    s!"{stats.failed - stats.limited} not reconstructed for another reason than a limit, {stats.rejected} rejected"
  let allowed := (stats.theorems * limitedPercent + 99) / 100
  check s!"{what}: at most {limitedPercent}% of the theorems stop at a limit in {totalMs / 1000} s"
    (stats.limited ≤ allowed) s!"{stats.limited} of {stats.theorems} at a limit, {stats.memoryLimited} of them by memory"
  validate o mm0rs inp (if every > 1 then "full-sample" else "full") (inp.file.withBodies bodies)
  IO.println s!"{what}: {stats.replayed} of {stats.theorems} proofs found, {stats.otherProofs} of them not the known one, \
    {stats.limited} at a limit ({stats.memoryLimited} by memory), {stats.conversions} with a shared conversion left out, \
    {stats.rounds} rounds, in {(← IO.monoMsNow) - start} ms"

def run (o : Options) (mm0rs : Option String) (jobs cores : Nat) (deadline : Nat) : TestM Unit := do
  -- the inputs: the corpus, with the specification beside each file, and the proof
  -- files of the MM0 repository
  let mut inputs : Array Input := #[]
  let corpus ← Tests.Mmb.mmbFiles ".tools/corpus"
  if corpus.isEmpty then skip "the corpus" "run scripts/build-corpus.sh"
  for p in corpus do
    let mm0 := p.withExtension "mm0"
    match ← load (p.fileStem.getD p.toString) p (if ← mm0.pathExists then some mm0 else none) with
    | some inp => inputs := inputs.push inp
    | none => pure ()
  match ← IO.getEnv "MM0_REPO" with
  | none => skip "the proof files of the MM0 repository" "set MM0_REPO to a checkout"
  | some repo =>
    for dir in Tests.Mmb.acceptDirs do
      for p in ← Tests.Mmb.mmbFiles ((repo : System.FilePath) / dir) do
        match ← load s!"{dir}/{p.fileStem.getD ""}" p none with
        | some inp => inputs := inputs.push inp
        | none => pure ()
  if mm0rs.isNone then skip "the verdicts of mm0-rs" "no mm0-rs: run scripts/build-oracles.sh"
  IO.println s!"thorough: {inputs.size} proof files, {(deadline - (← IO.monoMsNow)) / 60000} min, \
    every {o.every}th theorem where a sample is taken, {jobs} theorems at once, {cores} searches at once"
  -- 1. the replay of every file in full
  for inp in inputs do
    replayAll o mm0rs jobs inp
  -- 2. the search samples
  for inp in inputs do
    if inp.name == "setmm" then
      searchSample o mm0rs cores inp "bfs" setmmPredicateEnd 30
      searchSample o mm0rs cores inp "both" setmmPredicateEnd 35
    else if inp.name == "peano" then
      searchSample o mm0rs cores inp "bfs" 1000000000 20
  -- 3. the full expansion: the small files in full, each within an equal share of half
  -- the time left (most end in seconds); then the large ones with the stride, smallest
  -- first, each with the share of what is left — but a reserve for checking the last
  -- output — that its sample is of the samples left, so that the time a file gives
  -- back goes to the larger ones after it
  let small := inputs.filter (·.theorems < bigFile)
  let large := (inputs.filter (·.theorems ≥ bigFile)).qsort (·.theorems < ·.theorems)
  let reserve := 60000
  let now ← IO.monoMsNow
  let smallShare := if small.isEmpty then 0 else ((deadline - now) / 2) / small.size
  for inp in small do
    fullReplay o mm0rs jobs inp 1 (min smallShare (deadline - (← IO.monoMsNow) - reserve))
  let mut samplesLeft := large.foldl (init := 0) (· + ·.theorems / o.every)
  for inp in large do
    let left := deadline - (← IO.monoMsNow) - reserve
    let sample := inp.theorems / o.every
    fullReplay o mm0rs jobs inp o.every (left * sample / max 1 samplesLeft)
    samplesLeft := samplesLeft - sample

end Tests.Thorough

open Tests.Thorough in
def main (args : List String) : IO UInt32 := do
  let o ←
    match parseArgs {} args with
    | .ok o => pure o
    | .error msg =>
      IO.eprintln s!"thorough: {msg}\n{usage}"
      return 2
  let jobs ← if o.jobs > 0 then pure o.jobs else processors
  let cores ← if o.cores > 0 then pure o.cores else physicalCores
  IO.FS.createDirAll o.out
  let mm0rs ← if ← System.FilePath.pathExists o.mm0rs then pure (some o.mm0rs) else pure none
  let start ← IO.monoMsNow
  let ((), stats) ← (run o mm0rs jobs cores (start + o.minutes * 60000)).run {}
  IO.println s!"{stats.passed} passed, {stats.failed} failed, {stats.skipped} skipped, in {((← IO.monoMsNow) - start) / 1000} s"
  return if stats.failed == 0 then 0 else 1
