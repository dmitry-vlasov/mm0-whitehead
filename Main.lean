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
  dsl [--tactics DIR]            list the tactics, costs, guides and filters of the language of
                                 sessions, and the definitions of DIR (tactics/ by default:
                                 here, or in the repository the program was built in)
  mcp <file.mm0> <file.mmb> [--log FILE] [--anonymous] [--tactics DIR] [--export DIR]
               [--models DIR | --no-models] [--model FILE] [--cheap FILE] [--contexts FILE] [--value FILE]
                                 the MCP server for an AI agent, on stdin and stdout: sessions
                                 to prove the theorems of the file; --log: a trace of every
                                 message; --anonymous: assertions are shown as A and their
                                 number, but for the theorem a session starts on; --export: `proof`
                                 writes DIR/<theorem>.mmb, the file with the proof found put in;
                                 the learned models of `learned` are read from models/ (ranker.json,
                                 cheap.json, value.json) unless --models names another directory,
                                 --no-models reads none, or a file is named
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
  prove rails <file.mmb> [--every K] [--to B] [--rank occurrences|size|small|reach|specific|recent] [--dump FILE]
                                 how far the subproofs of earlier proofs that fit the goal of a
                                 theorem agree with its known proof, for the first 1, 3 and 10;
                                 --dump: every one that fits, with its features and how far it
                                 agrees, a row each
  prove export <file.mmb> -o OUT [--from A] [--to B] [--every K] [--negatives N] [--ms T]
               [--max-nodes N] [--search T [--tactics DIR] [--model FILE] [--cheap FILE] [--contexts FILE] [--value FILE] [--mm0 F]
               [--search-ms T] [--goals [--max-goals N]]]
                                 the data of the learned ranking layer: for each theorem, along
                                 its known proof, a row for each variant of each goal node, with
                                 its features and whether the known proof chose it (TSV);
                                 --negatives: the others kept a node (50; 0 for all); --hard: half
                                 of them the ones the cheap model (--cheap) scores highest; --search:
                                 along the proof that tactic T finds in --search-ms (1000) ms
                                 instead, for the theorems where it is not the known one's shape;
                                 --goals: the data of the value of goals instead, a row for each
                                 goal node of the tree the search grew (at most N, 200, drawn),
                                 with its features and whether the search proved it
  prove subgoals <file.mmb> --tactic T [--ms T] [--from A] [--to B] [--every K] [--tactics DIR]
               [--model FILE] [--cheap FILE] [--contexts FILE] [--value FILE] [--mm0 F] [--max-nodes N]
                                 the subgoal bench of the tactics system: each goal node on a
                                 known proof's path (not the root, nor one a premise proves) is a
                                 task of its own under the theorem's premises, which tactic T gets
                                 --ms (100) ms for; the share closed, by depth and by the head of
                                 the statement; --dump FILE: a line a subgoal, with its statement
  prove contexts <file.mmb> -o OUT [--from A] [--to B] [--every K] [--negatives N] [--cap N]
                                 the contexts of use of the assertions (Contexts.lean): the goals
                                 of the known proofs where each was used, and a sample of the
                                 goals it unified with where it was not; --contexts OUT gives them
                                 to the rank of prove export, search, subgoals and goal
  prove prior <file.mmb> [--from A] [--to B] [--every K] [--k N] [--vote sim|count|norm]
               [--self X] [--power X] [--pairs] [--nb] [--absent X] [--present X]
                                 how well the prior per theorem alone ranks the assertions the
                                 known proofs use: the share with a prior, in the first 10, 100
                                 and 1,000 of the assertions before the theorem, the median place
  prove score <data.tsv> --model FILE
                                 the scores of a model of the learned ranking layer for the rows
                                 of a file of `prove export`, one a line
  prove goal <file.mm0> <file.mmb> --theorem NAME --statement TEXT [--tactic T] [--ms T]
               [--models DIR | --no-models] [--model FILE] [--cheap FILE] [--contexts FILE] [--value FILE]
             [--max-nodes N] [--tactics DIR]
                                 a proof of TEXT, in the notation of the specification, under the
                                 hypotheses of theorem NAME, from the assertions before it,
                                 printed as an MM1 proof term (JSON): the gap filler of the agent
                                 bench. A metavariable ?a of MM1 is one of the search's. By
                                 default seq(bfs(size=20000, depth=2), guided), 5 s
  prove search <file.mmb> [-o out.mmb] [--from A] [--to B] [--every K] [--ms T] [--max-nodes N]
               [--strategy bfs|forward|both] [--tactic T] [--tactics DIR] [--model FILE] [--cheap FILE] [--value FILE]
               [--mm0 file.mm0] [--max-facts N]
               [--join-cap N|all] [--max-tuples N] [--max-work N]
               [--meta I,J,...] [--verbose]
                                 prove the theorems of a file from scratch: backward breadth first,
                                 forward from the premises, or both in turn. --max-facts: the
                                 size of the forward front (512); --join-cap: how many facts a
                                 new subgoal is joined with when it is made (4); --max-tuples,
                                 --max-work: the proofs joined and the work of the joins, as for
                                 replay (300,000 and 20,000,000). --meta: the binders
                                 with these numbers are metavariables, for which values are found;
                                 --tactic: a tactic of the language for every theorem (`dsl`),
                                 such as `rails(10, rank=reach, open=0, upto=1)`; --tactics: the
                                 directory of the definitions, as for `dsl`; --model, --value: the
                                 learned rank of variants and value of goals that tactics use;
                                 --mm0: the names from the specification, for a file without
                                 an index (set.mm), so that name(...) and scope(...) work
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

/-- A decimal number with an optional sign and fraction, as a `Float`. -/
def parseFloat (s : String) : Option Float := do
  let (neg, s) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let parts := s.splitOn "."
  let whole : Nat ← parts[0]?.bind String.toNat?
  let frac := parts[1]?.getD ""
  let fracVal : Float ← if frac.isEmpty then pure 0.0 else do
    let n : Nat ← frac.toNat?
    pure (n.toFloat / (10 : Float) ^ frac.length.toFloat)
  let v := whole.toFloat + fracVal
  return if neg then -v else v

/-- The value of the option `name` among `args`, as a `Float`. -/
def floatOption (args : List String) (name : String) (default : Float) : Float :=
  match args.dropWhile (· != name) with
  | _ :: value :: _ => (parseFloat value).getD default
  | _ => default

/-- The learned models of a front-end: the ranker (`--model FILE`), the cheap first stage
of its rank (`--cheap FILE`) and the value of goals (`--value FILE`). Where an option is
not given and `defaults` holds, the file of `--models DIR` (`models`, beside the
program's repository, or in the working directory) is read if it exists: `ranker.json`,
`cheap.json`, `value.json` — the best setting of the bench (`docs/STATUS.md`); `--no-models`
reads none. -/
def loadModels (args : List String) (defaults : Bool) :
    IO (Except String (Option Prove.Model × Option Prove.Model × Option Prove.Model)) := do
  let dir ← match strOption args "--models" with
    | some d =>
      if !(← System.FilePath.isDir d) then return .error s!"--models {d}: not a directory"
      pure (some (System.FilePath.mk d))
    | none =>
      if !defaults || args.contains "--no-models" then pure none
      else
        -- the repository of the program: `.lake/build/bin/mm0-whitehead` is four below it
        let app ← IO.appPath
        let repo := app.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)
        let candidates := (repo.map (· / "models")).toList ++ [System.FilePath.mk "models"]
        candidates.findM? fun d => d.isDir
  let load (option file : String) (names : Array String) : IO (Except String (Option Prove.Model)) := do
    let path ← match strOption args option with
      | some p => pure (some (System.FilePath.mk p))
      | none => match dir with
        | some d => do let p := d / file; pure (if ← p.pathExists then some p else none)
        | none => pure none
    match path with
    | none => return .ok none
    | some p => return (← Prove.Model.load p names).map some
  let model ← load "--model" "ranker.json" Prove.featureNames
  let cheap ← load "--cheap" "cheap.json" Prove.featureNames
  let value ← load "--value" "value.json" Prove.goalFeatureNames
  return do pure (← model, ← cheap, ← value)

/-- The contexts of use of a file's assertions (`Contexts.lean`), from the file that
`prove contexts` wrote (`--contexts FILE`): their weights are the prior's. -/
def loadContexts (args : List String) (prior : Prove.Prior) (asserts : Nat) : IO (Option Prove.Contexts) := do
  let some path := strOption args "--contexts" | return none
  let lines := ((← IO.FS.readFile path).splitOn "\n").toArray.filter (· != "")
  let c := (Prove.Contexts.ofPrior prior).withLines lines asserts
  let (np, nn, na) := c.counts
  IO.eprintln s!"{path}: {np} positive and {nn} negative contexts of {na} assertions"
  return some c

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

/-- `--mm0 FILE`: the assertions and terms named from the specification, and its notation
for the patterns of a tactic (`at($ _ < _ $)`, `goal($ … $)`). The set.mm translation has
no index, so its `.mmb` names them `T` and a number; `name(...)` and `scope(...)` in a
tactic, and the reports, want the real names. Without `--mm0`, the file's own names and no
notation. -/
def withSpecNames (db : Prove.Db) (file : Mmb.MmbFile) (args : List String) :
    IO (Option (Prove.Db × Option Prove.Notation)) := do
  let some mm0 := strOption args "--mm0" | return some (db, none)
  match ← Mm0.load mm0 with
  | .error e =>
    IO.eprintln e.format
    return none
  | .ok spec =>
    match Mm0.elaborateState spec with
    | .error e =>
      IO.eprintln e.format
      return none
    | .ok st =>
      let env := st.env
      let db := (Verify.specNames env file).foldl (init := db) fun db (i, name) =>
        if i < db.asserts.size then { db with asserts := db.asserts.modify i fun a => { a with name } } else db
      let db := (Verify.specTermNames env file).foldl (init := db) fun db (i, name) =>
        if i < db.terms.size then { db with terms := db.terms.modify i fun t => { t with name } } else db
      return some (db, some (Prove.Notation.ofSpec st file))

/-- `prove db`: what the prover reads from a proof file, with timings. -/
def proveDb (path : String) (args : List String) : IO UInt32 := do
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
  let some (db, _) ← withSpecNames db file args | return 1
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
  -- the congruence procedure's table (`Prove/Congr.lean`)
  let t4 ← IO.monoNanosNow
  let tb := Prove.CongrTable.ofDb db
  let n := tb.lemmas.fold (init := 0) fun acc _ ls => acc + ls.size
  let terms := tb.lemmas.fold (init := ({} : Std.HashSet Nat)) fun acc k _ => acc.insert k.1
  let ded := tb.lemmas.fold (init := 0) fun acc k ls => if k.2.2 then acc + ls.size else acc
  IO.println s!"congruence lemmas: {n} for {terms.size} terms, {ded} in the deduction form; {tb.refl.size} reflexivity lemmas ({ms t4 (← IO.monoNanosNow)})"
  -- the ring procedure's table (`Prove/Ring.lean`)
  let t5 ← IO.monoNanosNow
  let rt := Prove.RingTable.ofDb db
  let tn (k : Nat) : String := (db.terms[k]?.map (·.name)).getD s!"t{k}"
  let an (k : Nat) : String := (db.asserts[k]?.map (·.name)).getD s!"a{k}"
  let sh (e : Prove.Exp) : String := if e.nodes.isEmpty then "none" else db.showExp e
  let op (o : Prove.RingOp) : String :=
    tn o.term ++ (if o.fixed.isEmpty then "" else s!"[{", ".intercalate (o.fixed.map fun (_, f) => sh f).toList}]")
  for rg in rt.rings do
    IO.println s!"ring: {tn rg.eq} over {op rg.add} and {op rg.mul}, zero {sh rg.zero}, one {sh rg.one}, \
      negation {(rg.neg.map op).getD "none"}, subtraction {(rg.sub.map op).getD "none"}, \
      carrier {(rg.carrier.map fun (_, c) => sh c).getD "none"}; {rg.rules.size} rules, transitivity \
      {(rg.trans.toList.map fun (d, k) => s!"{an k}{if d then "/d" else ""}") ++ (rg.trans4.toList.map fun (d, k) => s!"{an k}{if d then "/d" else ""}")}, \
      symmetry {rg.symm.toList.map fun (d, k) => s!"{an k}{if d then "/d" else ""}"}"
  IO.println s!"ring tables: {rt.rings.size} rings, lift {(rt.lift.map an).getD "none"}, {rt.closure.size} closure lemmas of operations, \
    {rt.constClosure.size} of constants ({ms t5 (← IO.monoNanosNow)})"
  return 0

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
    -- the order by the latest proof that uses the assertion
    IO.println s!"  ordered by recency, the known variant among all: {Prove.rankSummary (nodes.map (·.recentAll))}"
    for j in [0:depths.size] do
      IO.println s!"  ordered by recency, among those described to depth {depths[j]!}: \
        {Prove.rankSummary (nodes.map (·.recents[j]!))}"
  return 0

/-- The prior's options from the command line: `--k N`, `--vote sim|count|norm`,
`--self X`, `--power X`, `--pairs`, `--nb`, `--absent X`, `--present X`. -/
def priorOptions (args : List String) : Prove.PriorOptions :=
  { k := numOption args "--k" 100,
    vote := match strOption args "--vote" with
      | some "count" => .count
      | some "norm" => .norm
      | _ => .sim,
    self := floatOption args "--self" 0,
    power := floatOption args "--power" 1,
    pairs := args.contains "--pairs",
    nb := args.contains "--nb",
    nbAbsent := floatOption args "--absent" (-18),
    nbPresent := floatOption args "--present" 5 }

/-- `prove prior`: how well the prior alone ranks the assertions a proof uses
(`Prove/Prior.lean`). For each theorem of the range, the assertions before it are ordered
by the theorem's prior, and the places of the ones its known proof uses are read: how many
have a prior at all, how many come in the first 10, 100 and 1,000, and their median place.
Ties share their place (its mean); an assertion without a prior is tied with all the others
without one. -/
def provePrior (path : String) (args : List String) : IO UInt32 := do
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
  let first := numOption args "--from" 0
  let last := numOption args "--to" 1000000000
  let every := max 1 (numOption args "--every" 1)
  let opts := priorOptions args
  let uses := Prove.Uses.ofFile file db.asserts.size
  let t0 ← IO.monoMsNow
  let prior := Prove.Prior.ofDb db (Prove.SymbolStats.ofDb db) uses opts
  let todo := (Array.range file.stmts.size).filter fun i =>
    let s := file.stmts[i]!
    (match s.kind with | .thm _ => true | _ => false) && s.index ≥ first && s.index < last && s.index % every == 0
      && !(prior.used[s.index]?.getD #[]).isEmpty
  -- a theorem: how many assertions its proof uses, how many of them have a prior, and their
  -- places
  let results ← Prove.runJobs jobs todo.size (fun k => do
      let thm := file.stmts[todo[k]!]!.index
      let pr := prior.query thm
      -- the candidates with a prior, before the theorem, the highest first
      let scored := (pr.toArray.filter fun (a, v) => a < thm && v > 0).qsort fun a b => a.2 > b.2
      let zeros := thm - scored.size
      -- the place of a value: those above it, and half of the others with it
      let placeOf (v : Float) : Float := Id.run do
        let mut above := 0
        let mut same := 0
        for (_, x) in scored do
          if x > v then above := above + 1 else if x == v then same := same + 1 else break
        return above.toFloat + (same.toFloat + 1) / 2
      let mut out : Array Float := #[]
      let mut covered := 0
      for a in prior.used[thm]! do
        let v := pr.getD a 0
        if v > 0 then
          covered := covered + 1
          out := out.push (placeOf v)
        else
          out := out.push (scored.size.toFloat + (zeros.toFloat + 1) / 2)
      return (out.size, covered, out))
    progress memLimit logLine
  let ms := (← IO.monoMsNow) - t0
  let mut used := 0
  let mut covered := 0
  let mut places : Array Float := #[]
  for (u, c, ps) in results do
    used := used + u
    covered := covered + c
    places := places ++ ps
  let within (n : Nat) : Nat := places.foldl (init := 0) fun acc p => if p ≤ n.toFloat then acc + 1 else acc
  let pct (a : Nat) : String := s!"{a * 1000 / max 1 used / 10}.{a * 1000 / max 1 used % 10}%"
  let sorted := places.qsort (· < ·)
  let median := if sorted.isEmpty then 0 else sorted[sorted.size / 2]!
  IO.println s!"prior {repr opts}"
  IO.println s!"  {todo.size} theorems, {used} used assertions \
    ({used * 10 / max 1 todo.size / 10}.{used * 10 / max 1 todo.size % 10} a theorem); built and asked in {ms} ms"
  IO.println s!"  with a prior {pct covered}; in the first 10: {pct (within 10)}, 100: {pct (within 100)}, \
    1000: {pct (within 1000)}; median place {median.toUInt64}"
  return 0

/-- `prove contexts`: the contexts of use of the file's assertions (`Contexts.lean`): for
each theorem of the range, its known proof replayed with every variant of each goal; each
goal is a positive context of the assertion the proof applies and a negative one of
`--negatives` (2) of the other variants; at most `--cap` (256) of each an assertion. Written
to `-o OUT`, read back by `--contexts OUT`. -/
def proveContexts (path : String) (args : List String) : IO UInt32 := do
  let some out := strOption args "-o"
    | IO.eprintln "prove contexts: -o OUT is needed"; return 2
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
  let first := numOption args "--from" 0
  let last := numOption args "--to" 1000000000
  let every := max 1 (numOption args "--every" 1)
  let negatives := numOption args "--negatives" 2
  let cap := numOption args "--cap" 256
  let limits : Prove.Limits :=
    { maxProps := numOption args "--max-nodes" 500000, maxMs := numOption args "--ms" 20000,
      maxTuples := numOption args "--max-tuples" 300000, maxWork := numOption args "--max-work" 20000000 }
  let todo := (Array.range file.stmts.size).filter fun i =>
    let s := file.stmts[i]!
    (match s.kind with | .thm _ => true | _ => false) && s.index ≥ first && s.index < last && s.index % every == 0
  let index := db.index
  let uses := Prove.Uses.ofFile file db.asserts.size
  let stats := Prove.SymbolStats.ofDb db
  let c := Prove.Contexts.ofPrior (Prove.Prior.ofDb db stats uses)
  let start ← IO.monoMsNow
  let results ← Prove.runJobs jobs todo.size (fun k => Prove.contextRecords db index limits uses c negatives todo[k]!)
    progress memLimit logLine
  let records := results.foldl (· ++ ·) #[]
  let c := c.withRecords records db.asserts.size cap
  let (np, nn, na) := c.counts
  let h ← IO.FS.Handle.mk out .write
  for l in c.toLines do h.putStrLn l
  h.flush
  logLine s!"{path}: {todo.size} theorems, {records.size} records; kept {np} positive and {nn} negative contexts \
    of {na} assertions (at most {cap} each), written to {out}, in {(← IO.monoMsNow) - start} ms"
  return 0

/-- `prove export`: the data of the learned ranking layer (`Prove/Dataset.lean`): for each
theorem of the range, a row for each variant of each goal node of its known proof's
path, with its features and whether the known proof chose it. -/
def proveExport (path : String) (args : List String) : IO UInt32 := do
  let some out := strOption args "-o"
    | IO.eprintln "prove export: -o OUT is needed"; return 2
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
  let some (db, nt) ← withSpecNames db file args | return 1
  let (jobs, progress, memLimit) ← jobOptions args
  let first := numOption args "--from" 0
  let last := numOption args "--to" 1000000000
  let every := max 1 (numOption args "--every" 1)
  let negatives := numOption args "--negatives" 50
  -- --hard: half the negatives are the ones the cheap model (--cheap) scores highest
  let hardNegatives := args.contains "--hard"
  let limits : Prove.Limits :=
    { maxProps := numOption args "--max-nodes" 500000, maxMs := numOption args "--ms" 20000,
      maxTuples := numOption args "--max-tuples" 300000, maxWork := numOption args "--max-work" 20000000 }
  let todo := (Array.range file.stmts.size).filter fun i =>
    let s := file.stmts[i]!
    (match s.kind with | .thm _ => true | _ => false) && s.index ≥ first && s.index < last && s.index % every == 0
  let index := db.index
  let uses := Prove.Uses.ofFile file db.asserts.size
  let stats := Prove.SymbolStats.ofDb db
  let prior := Prove.Prior.ofDb db stats uses
  let start ← IO.monoMsNow
  -- --search T: along the proofs that tactic T finds (expert iteration), those that are not
  -- the known one's shape; otherwise along the known proofs
  let searchTactic := strOption args "--search"
  let defs ← match ← Prove.Dsl.loadTactics (strOption args "--tactics") with
    | .ok defs => pure defs
    | .error msg => IO.eprintln msg; return 1
  let model ← match strOption args "--model" with
    | none => pure none
    | some p => match ← Prove.Model.load p with
      | .ok m => pure (some m)
      | .error e => IO.eprintln e; return 1
  let cheap ← match strOption args "--cheap" with
    | none => pure none
    | some p => match ← Prove.Model.load p with
      | .ok m => pure (some m)
      | .error e => IO.eprintln e; return 1
  let value ← match strOption args "--value" with
    | none => pure none
    | some p => match ← Prove.Model.load p Prove.goalFeatureNames with
      | .ok m => pure (some m)
      | .error e => IO.eprintln e; return 1
  -- --goals: the goal nodes of the searches' trees, for the value of goals
  let goals := args.contains "--goals"
  if goals && searchTactic.isNone then
    IO.eprintln "prove export: --goals needs --search"
    return 2
  let maxGoals := numOption args "--max-goals" 200
  let rails : Thunk Prove.Rails := Thunk.mk fun _ => Prove.Rails.ofDb db
  let vc := Verify.Ctx.ofFile file
  let hypIndexes := if searchTactic.isSome then db.hypIndexes else {}
  -- the joins have the budgets of the rows' expansion: one join can run long, past the time
  let searchLimits : Prove.Limits := { maxProps := 20000000, maxMs := numOption args "--search-ms" 1000,
                                       maxTuples := limits.maxTuples, maxWork := limits.maxWork }
  let found ← IO.mkRef (0, 0, 0)
  let hard : Option Prove.Model := if hardNegatives then cheap else none
  if hardNegatives && hard.isNone then
    IO.eprintln "prove export: --hard needs the cheap model (--cheap FILE)"
    return 2
  let contexts ← loadContexts args prior db.asserts.size
  let rowsFor (k : Nat) : IO (Option (Array String)) := do
    let i := todo[k]!
    let thmPrior := prior.query file.stmts[i]!.index
    match searchTactic with
    | none => Prove.datasetRows db index limits uses stats negatives i thmPrior hard contexts
    | some text =>
      let thm := file.stmts[i]!.index
      let ctx : Prove.Dsl.Ctx := { db, spec := nt, thm, rails := some rails, defs, model, cheap, value }
      match Prove.Dsl.parseTactic ctx text with
      | .error e =>
        if k == 0 then IO.eprintln (Prove.Dsl.ParseError.show text e)
        return none
      | .ok t =>
        let env := { Prove.Env.init db index (db.task thm) hypIndexes with uses, prior := thmPrior, contexts }
        let r ← Prove.searchWith (Prove.accept vc) env t.strategy searchLimits
        if goals then
          if r.proof.isSome then found.modify fun (a, b, c) => (a + 1, b, c)
          return some (Prove.goalRows r.env stats thm r.proof.isSome maxGoals)
        let some proof := r.proof | return none
        let known := match db.skeleton file.stmts[i]! with
          | .ok (some sk) => Prove.sameShape proof sk
          | _ => false
        match proof.skeleton? with
        | none =>
          found.modify fun (a, b, c) => (a + 1, b, c + 1)
          return none
        | some sk =>
          found.modify fun (a, b, c) => (a + 1, b + (if known then 1 else 0), c)
          if known then return none
          return some (← Prove.datasetRowsOf db index limits uses stats negatives i sk thmPrior hard contexts)
  let results ← Prove.runJobs jobs todo.size rowsFor progress memLimit logLine
  let h ← IO.FS.Handle.mk out .write
  h.putStrLn (if goals then Prove.goalHeader else Prove.datasetHeader)
  let mut rows := 0
  let mut positives := 0
  for r in results do
    if let some lines := r then
      for l in lines do
        h.putStrLn l
        rows := rows + 1
        if (l.splitOn "\t")[3]? == some "1" then positives := positives + 1
  if goals then
    let (n, _, _) ← found.get
    IO.println s!"{path}: {todo.size} theorems, {n} proved by the search; {rows} goal rows, {positives} of them \
      proved, written to {out}, in {(← IO.monoMsNow) - start} ms"
  else if searchTactic.isSome then
    let (n, same, conv) ← found.get
    IO.println s!"{path}: {todo.size} theorems, {n} proved by the search, {same} as the known proof, {conv} with an \
      unfolding of its own; {rows} rows along the {(results.filter (·.isSome)).size} others, written to {out}, \
      in {(← IO.monoMsNow) - start} ms"
  else
    IO.println s!"{path}: {todo.size} theorems, {(results.filter (·.isNone)).size} left out (a shared conversion); \
      {rows} rows, {positives} of them the known proof's, written to {out}, in {(← IO.monoMsNow) - start} ms"
  return 0

/-- The subgoals of a proof tree, each with its depth: for each step, the hypotheses of its
assertion under its arguments; `none` for one that a premise of the theorem proves. A
conversion's own statement is that of the hypothesis it proves, and its steps below are
walked too. -/
partial def subgoalStatements (db : Prove.Db) (depth : Nat) : Prove.ProofTree → Array (Nat × Option Prove.Exp)
  | .hyp _ => #[]
  | .conv _ _ _ _ _ child => subgoalStatements db depth child
  | .step a args children =>
    let asn := db.asserts[a]!
    let map := (Array.range (min asn.vars.size args.size)).foldl (init := ({} : Std.HashMap Nat Prove.SubExp))
      fun m k => m.insert (Prove.Node.varId asn.vars[k]!) (Prove.SubExp.mk' asn.vars[k]! args[k]!)
    let s : Prove.Subst := { map }
    (Array.range children.size).foldl (init := #[]) fun acc i =>
      let acc := match children[i]! with
        | .hyp _ => acc.push (depth + 1, none)
        | _ => acc.push (depth + 1, some (s.apply asn.hyps[i]!))
      acc ++ subgoalStatements db (depth + 1) children[i]!

/-- `prove subgoals`: what a tactic closes of the goals that occur in known proofs, within a
small budget: the subgoal bench of the tactics system (`docs/DESIGN.md`, "The tactics
system"). For each theorem of the range, the known proof is replayed over the full
expansion (`oracleAll`), and each subgoal of the proof found — the statement of each step
below the root, as the whole proof fixes it, not one that a premise proves, nor one that a
dummy is left in — is a task of its own under the theorem's premises, which the tactic gets
`--ms` for. The share closed is reported by the depth of the goal and by the head term of
its statement, its implications stripped (`->`, `=`, `e.`, `<->` and the class relations
named through anchor assertions, since set.mm's terms have no names of their own).

A subgoal is measured as the proof fixes it: in a search, the step above it may leave
metavariables in it that only a sibling's proof decides, so this is what a tactic closes
of determined goals, the regime of a decision procedure. -/
def proveSubgoals (path : String) (args : List String) : IO UInt32 := do
  let file ← match Mmb.MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e => IO.eprintln (e.format path); return 1
  let db ← match Prove.Db.ofFile file with
    | .ok db => pure db
    | .error msg => IO.eprintln s!"{path}: {msg}"; return 1
  let some (db, nt) ← withSpecNames db file args | return 1
  let some text := strOption args "--tactic" | IO.eprintln "prove subgoals: --tactic T is needed"; return 2
  let (jobs, progress, memLimit) ← jobOptions args
  let first := numOption args "--from" 0
  let last := numOption args "--to" 1000000000
  let every := max 1 (numOption args "--every" 1)
  let ms := numOption args "--ms" 100
  let replayLimits : Prove.Limits := { maxProps := 500000, maxMs := 20000, maxTuples := 300000, maxWork := 20000000 }
  let searchLimits : Prove.Limits := { maxProps := numOption args "--max-nodes" 20000000, maxMs := ms,
                                       maxTuples := 300000, maxWork := 20000000 }
  let defs ← match ← Prove.Dsl.loadTactics (strOption args "--tactics") with
    | .ok defs => pure defs
    | .error msg => IO.eprintln msg; return 1
  let model ← match strOption args "--model" with
    | none => pure none
    | some p => match ← Prove.Model.load p with
      | .ok m => pure (some m)
      | .error e => IO.eprintln e; return 1
  let cheap ← match strOption args "--cheap" with
    | none => pure none
    | some p => match ← Prove.Model.load p with
      | .ok m => pure (some m)
      | .error e => IO.eprintln e; return 1
  let value ← match strOption args "--value" with
    | none => pure none
    | some p => match ← Prove.Model.load p Prove.goalFeatureNames with
      | .ok m => pure (some m)
      | .error e => IO.eprintln e; return 1
  let rails : Thunk Prove.Rails := Thunk.mk fun _ => Prove.Rails.ofDb db
  let index := db.index
  let uses := Prove.Uses.ofFile file db.asserts.size
  let hypIndexes := db.hypIndexes
  let prior := Prove.Prior.ofDb db (Prove.SymbolStats.ofDb db) uses
  let contexts ← loadContexts args prior db.asserts.size
  -- the terms by which the statements are grouped, through assertions whose conclusions
  -- are known to have them: `->` from ax-1, `=` from eqid, `e.` from vex, `<->` from biid,
  -- and a class relation from breq1
  let conclOf (names : List String) : Option Prove.Exp :=
    names.findSome? fun n => (db.asserts.find? (·.name == n)).map (·.concl)
  let head (e : Prove.Exp) : Nat := Prove.Node.appId e.nodes[0]!
  let wi := (conclOf ["ax-1", "ax_1"]).map head
  let strip (e : Prove.Exp) : Prove.Exp := Id.run do
    let some wi := wi | return e
    let mut e := e
    for _ in [0:16] do
      if !Prove.Node.isVar e.nodes[0]! && head e == wi && e.nodes.size > 1 then e := e.sub (e.argStarts 0)[1]! else break
    return e
  let mut termNames : Std.HashMap Nat String := {}
  for (names, shown) in [(["ax-1", "ax_1"], "->"), (["eqid"], "="), (["vex"], "e."), (["biid"], "<->")] do
    if let some c := conclOf names then termNames := termNames.insert (head (strip c)) shown
  if let some c := conclOf ["breq1"] then
    let inner := strip c
    if inner.nodes.size > 1 then
      let arg := inner.sub (inner.argStarts 0)[0]!
      if !Prove.Node.isVar arg.nodes[0]! then termNames := termNames.insert (head arg) "class relation"
  let headName (e : Prove.Exp) : String :=
    let s := strip e
    let n := s.nodes[0]!
    if Prove.Node.isVar n then "a variable" else if Prove.Node.isConst n then "a variable of the theorem"
    else termNames.getD (head s) (db.terms[head s]?.map (·.name) |>.getD "?")
  let todo := (Array.range file.stmts.size).filter fun i =>
    let s := file.stmts[i]!
    (match s.kind with | .thm _ => true | _ => false) && s.index ≥ first && s.index < last && s.index % every == 0
  -- a tactic that does not read is reported once, with the first theorem's context
  if let some i := todo[0]? then
    let ctx : Prove.Dsl.Ctx := { db, spec := nt, thm := file.stmts[i]!.index, rails := some rails, defs, model, cheap, value }
    if let .error e := Prove.Dsl.parseTactic ctx text then
      IO.eprintln (Prove.Dsl.ParseError.show text e)
      return 1
  let skipped ← IO.mkRef (0, 0)
  let start ← IO.monoMsNow
  -- --dump FILE: a line a subgoal, the theorem, the depth, the head, closed, the ms, the statement
  let dump ← IO.mkRef (#[] : Array String)
  -- a subgoal: its depth, the head of its statement, whether it was closed, and the ms
  let results ← Prove.runJobs jobs todo.size (fun k => do
      let s := file.stmts[todo[k]!]!
      let thm := s.index
      let .ok (some skel) := db.skeleton s | return (#[] : Array (Nat × String × Bool × Nat))
      let env := { Prove.Env.init db index (db.task thm) with uses }
      let r ← Prove.searchWith Prove.acceptAny env (Prove.oracleAll skel (some 0)) replayLimits
      let some tree := r.proof | return #[]
      -- the proof with its leftover variables fixed, as the emitted proof has them
      let tree := (Prove.closings r.env tree)[0]?.getD tree
      let ctx : Prove.Dsl.Ctx := { db, spec := nt, thm, rails := some rails, defs, model, cheap, value }
      let .ok t := Prove.Dsl.parseTactic ctx text | return #[]
      let thmPrior := prior.query thm
      let mut out := #[]
      for (depth, e) in subgoalStatements db 0 tree do
        let some e := e | skipped.modify fun (m, p) => (m, p + 1); continue
        if e.hasVars then
          skipped.modify fun (m, p) => (m + 1, p)
          continue
        let task := { db.task thm with goal := e }
        let env' := { Prove.Env.init db index task hypIndexes with uses, prior := thmPrior, contexts }
        let t0 ← IO.monoMsNow
        -- a subgoal is not a statement of the file, so the verifier cannot check it: as
        -- `prove goal`, any proof of the tree counts
        let r' ← Prove.searchWith Prove.acceptAny env' t.strategy searchLimits
        let took := (← IO.monoMsNow) - t0
        out := out.push (depth, headName e, r'.proof.isSome, took)
        if (strOption args "--dump").isSome then
          dump.modify (·.push ("\t".intercalate [db.asserts[thm]!.name, toString depth, headName e,
            if r'.proof.isSome then "1" else "0", toString took,
            -- the theorem's variables as $k, apart from set.mm's numerals c1, c2, ...
            db.showExp e ((Array.range 128).map fun k => s!"${k}")]))
      return out)
    progress memLimit logLine
  let all : Array (Nat × String × Bool × Nat) := results.foldl (· ++ ·) #[]
  let closed := all.filter (·.2.2.1)
  let (metas, premises) ← skipped.get
  let pct (a b : Nat) : String := s!"{a} of {b} ({if b == 0 then 0 else a * 100 / b}%)"
  let times := (closed.map (·.2.2.2)).qsort (· < ·)
  IO.println s!"{path}: {todo.size} theorems, {all.size} subgoals ({metas} with a dummy left and {premises} \
    premises left out); closed by `{text}` within {ms} ms: {pct closed.size all.size}, median \
    {times[times.size / 2]?.getD 0} ms; in {(← IO.monoMsNow) - start} ms"
  let bucket (d : Nat) : String := if d ≤ 1 then "1" else if d ≤ 3 then "2-3" else if d ≤ 7 then "4-7" else "8+"
  let line := #["1", "2-3", "4-7", "8+"].map fun b =>
    let xs := all.filter fun r => bucket r.1 == b
    s!"{b}: {pct (xs.filter (·.2.2.1)).size xs.size}"
  IO.println s!"  by depth: {"; ".intercalate line.toList}"
  let heads := all.foldl (init := (#[] : Array String)) fun acc r => if acc.contains r.2.1 then acc else acc.push r.2.1
  let counted := (heads.map fun hd => (hd, (all.filter (·.2.1 == hd)).size)).qsort fun a b => a.2 > b.2
  let line := (counted.extract 0 10).map fun (hd, _) =>
    let xs := all.filter (·.2.1 == hd)
    s!"{hd}: {pct (xs.filter (·.2.2.1)).size xs.size}"
  IO.println s!"  by the head of the statement: {"; ".intercalate line.toList}"
  if let some f := strOption args "--dump" then
    IO.FS.writeFile f ("thm\tdepth\thead\tclosed\tms\tstatement\n" ++ "\n".intercalate (← dump.get).toList ++ "\n")
  return 0

/-- `prove featbench`: where the time of a learned rank goes. For each theorem of the range,
a tree grown by breadth-first search to `--max-nodes`, then the features of every
variant of every goal node, and the model's scores of them, each timed. -/
def proveFeatbench (path : String) (args : List String) : IO UInt32 := do
  let file ← match Mmb.MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e => IO.eprintln (e.format path); return 1
  let db ← match Prove.Db.ofFile file with
    | .ok db => pure db
    | .error msg => IO.eprintln msg; return 1
  let some mp := strOption args "--model" | IO.eprintln "--model FILE is needed"; return 2
  let m ← match ← Prove.Model.load mp with
    | .ok m => pure m
    | .error e => IO.eprintln e; return 1
  let uses := Prove.Uses.ofFile file db.asserts.size
  let stats := Prove.SymbolStats.ofDb db
  let index := db.index
  let first := numOption args "--from" 0
  let every := max 1 (numOption args "--every" 1000)
  let limits : Prove.Limits := { maxProps := numOption args "--max-nodes" 20000, maxMs := 60000 }
  let mut variants := 0
  let mut tf := 0
  let mut tm := 0
  let mut sink : Float := 0
  for s in file.stmts do
    let .thm _ := s.kind | continue
    if s.index < first || s.index % every != 0 then continue
    let env := { Prove.Env.init db index (db.task s.index) with uses }
    let r ← Prove.searchWith Prove.acceptAny env Prove.breadthFirst limits
    let env := r.env
    let props := (Array.range env.props.size)
    let t0 ← IO.monoNanosNow
    let infos := (Array.range env.hyps.size).map env.goalInfo
    let fs := props.map fun p => env.variantFeatures stats infos[env.props[p]!.parent]! p
    sink := sink + fs.foldl (init := 0) fun a x => a + x[0]!
    let t1 ← IO.monoNanosNow
    let sc := fs.map m.score
    sink := sink + sc.foldl (init := 0) (· + ·)
    let t2 ← IO.monoNanosNow
    variants := variants + props.size
    tf := tf + (t1 - t0)
    tm := tm + (t2 - t1)
  let per (t : Nat) : String := if variants == 0 then "-" else s!"{t / variants / 1000}.{t / variants % 1000 / 100} µs"
  IO.println s!"{path}: {variants} variants; features {tf / 1000000} ms ({per tf} each), model {tm / 1000000} ms ({per tm} each) [{sink}]"
  return 0

/-- `prove score`: the scores of a model (`Prove/Model.lean`) for the rows of a file of
`prove export`, one a line: what `learn/parity.py` compares with the scores in Python. A
file of goal rows (`--goals`) is scored by a value of goals, its log-odds. -/
def proveScore (path : String) (args : List String) : IO UInt32 := do
  let some mp := strOption args "--model" | IO.eprintln "prove score: --model FILE is needed"; return 2
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· != "")
  let some head := lines.head? | return 0
  let cols := (head.splitOn "\t").toArray
  let names := if Prove.featureNames.all cols.contains then Prove.featureNames else Prove.goalFeatureNames
  let m ← match ← Prove.Model.load mp names with
    | .ok m => pure m
    | .error e =>
      IO.eprintln e
      return 1
  let idx := names.filterMap fun n => cols.findIdx? (· == n)
  if idx.size != names.size then
    IO.eprintln s!"{path}: its columns are not the features of this program"
    return 1
  let out ← IO.getStdout
  for l in lines.tail do
    let fs := (l.splitOn "\t").toArray
    let x := idx.map fun i => (Prove.parseFloat fs[i]!).getD 0
    out.putStrLn (toString (m.score x))
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
    | some "specific" => .specific
    | some "recent" => .recent
    | _ => .occurrences
  -- --dump: every subproof that fits the goal, with what a rank could use, and how far it
  -- agrees with the known proof, one row each (for ranks tried outside)
  if let some out := strOption args "--dump" then
    let uses := Prove.Uses.ofFile file db.asserts.size
    let thms := (rails.sp.roots.filter fun (thm, _) => thm % every == 0 && thm < last)
    let rowsOf (thm root : Nat) : String := Id.run do
      let env := Prove.Env.init db index (db.task thm)
      let goal := env.task.goal
      let found := rails.at_ env 0 { count := 1000000000, minSize := 2 }
      let mut out := ""
      for k in found do
        let n := rails.sp.occBefore k thm
        let last := if n == 0 then thm else rails.sp.occ[k]![n - 1]!
        let concl := rails.concl[k]!
        let conclNon := (concl.nodes.filter (!Prove.Node.isVar ·)).size
        let top := rails.sp.nodes[k]!.1
        out := out ++ s!"{thm}\t{k}\t{rails.sp.sizes[k]!}\t{n}\t{thm - last}\t{rails.openHyps env goal k}\t\
          {rails.hyps[k]!.size}\t{conclNon}\t{concl.size}\t{goal.size}\t{top}\t{uses.before top thm}\t\
          {rails.agree k root}\t{rails.sp.sizes[root]!}\t{found.size}\n"
      return out
    let jobs := 12
    let tasks := (List.range jobs).map fun j => Task.spawn fun _ =>
      (Array.range thms.size).foldl (init := "") fun acc i =>
        if i % jobs == j then acc ++ rowsOf thms[i]!.1 thms[i]!.2 else acc
    let h ← IO.FS.Handle.mk out .write
    h.putStr "thm\tk\tsize\tocc\trecency\topen\thyps\tconclNon\tconclSize\tgoalSize\ttop\ttopUses\tagree\trootSize\tfit\n"
    for t in tasks do h.putStr t.get
    IO.println s!"{path}: {thms.size} theorems, every {every}th, written to {out}"
    return 0
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
  let some (db, nt) ← withSpecNames db file args | return 1
  let (jobs, progress, memLimit) ← jobOptions args
  let prior := Prove.Prior.ofDb db (Prove.SymbolStats.ofDb db) (Prove.Uses.ofFile file db.asserts.size)
  let contexts ← loadContexts args prior db.asserts.size
  let opts : Prove.SearchOptions :=
    { first := numOption args "--from" 0, last := numOption args "--to" 1000000000,
      every := max 1 (numOption args "--every" 1),
      strategy := (strOption args "--strategy").getD "bfs",
      limits := { maxProps := numOption args "--max-nodes" 100000, maxMs := numOption args "--ms" 1000,
                  maxFacts := numOption args "--max-facts" 512,
                  maxTuples := numOption args "--max-tuples" 300000, maxWork := numOption args "--max-work" 20000000,
                  joinCap := if strOption args "--join-cap" == some "all" then 0xFFFFFFFFFFFF
                    else numOption args "--join-cap" 4 },
      metas := numsOption args "--meta",
      verbose := args.contains "--verbose", jobs, progress, memLimit,
      prior := some prior, contexts }
  -- the marks must fit every theorem of the range
  for a in db.asserts do
    if a.id ≥ opts.first && a.id < opts.last && a.id % opts.every == 0 then
      if let some why := db.metasFault a.id opts.metas then
        IO.eprintln s!"{path}: --meta: {why}"
        return 1
  -- a tactic of the language, for every theorem; the subproofs of the file are made if it
  -- follows them
  let tactic := strOption args "--tactic"
  let defs ← match ← Prove.Dsl.loadTactics (strOption args "--tactics") with
    | .ok defs => pure defs
    | .error msg =>
      IO.eprintln msg
      return 1
  let rails : Thunk Prove.Rails := Thunk.mk fun _ => Prove.Rails.ofDb db
  let model ← match strOption args "--model" with
    | none => pure none
    | some p => match ← Prove.Model.load p with
      | .ok m => pure (some m)
      | .error e =>
        IO.eprintln e
        return 1
  let cheap ← match strOption args "--cheap" with
    | none => pure none
    | some p => match ← Prove.Model.load p with
      | .ok m => pure (some m)
      | .error e => IO.eprintln e; return 1
  let value ← match strOption args "--value" with
    | none => pure none
    | some p => match ← Prove.Model.load p Prove.goalFeatureNames with
      | .ok m => pure (some m)
      | .error e =>
        IO.eprintln e
        return 1
  let ctx (thm : Nat) : Prove.Dsl.Ctx := { db, spec := nt, thm, rails := some rails, defs, model, cheap, value }
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
  let some (db, _) ← withSpecNames db file args | return 1
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

/-- `prove goal`: a proof of a statement under the hypotheses of a theorem of the file,
from the assertions before it, printed as an MM1 proof term (`Prove/Mm1.lean`): the gap
filler of the agent bench. A metavariable `?a` of MM1 is a metavariable of the search,
the same name the same one. One JSON object is printed. -/
def proveGoal (mm0 mmb : String) (args : List String) : IO UInt32 := do
  let defs ← match ← Prove.Dsl.loadTactics (strOption args "--tactics") with
    | .ok defs => pure defs
    | .error msg =>
      IO.eprintln msg
      return 1
  let c ← match ← Mcp.Ctx.load mm0 mmb with
    | .ok c => pure c
    | .error msg =>
      IO.eprintln msg
      return 1
  let say (kvs : Array (String × Json)) : IO UInt32 := do
    IO.println (Json.obj kvs).compress
    return 0
  let (some name, some text) := (strOption args "--theorem", strOption args "--statement")
    | IO.eprintln "prove goal: --theorem NAME and --statement TEXT are needed"; return 2
  let thm ← match c.theorem name with
    | .ok t => pure t
    | .error e => return ← say #[("error", Json.str e)]
  let db := c.db
  let (holed, names) := Prove.mm1Holes text
  -- a name the statement has that the theorem does not is the agent's own variable (one
  -- of an induction it started, say): it becomes a variable of the task, of the first
  -- sort, regular then bound, with which the statement reads further
  let nb := db.asserts[thm]!.vars.size
  let varsWith (extra : Array Mm0.VarDecl) (i : Nat) : Prove.Exp :=
    if i < nb then db.binderImage thm #[] (db.asserts[thm]!.vars[i]?.getD 0)
    else match extra[i - nb]? with
      | some vd => ⟨#[Prove.Node.const i (Prove.Ty.mk vd.sort vd.bound)]⟩
      | none => default
  let unknown (msg : String) : Option String :=
    if msg.startsWith "unknown variable or term" then (msg.splitOn "`")[1]? else none
  -- an unknown name becomes a variable with a provisional sort, and the sorts of all of
  -- them are then tried in order, regular before bound, the last name's moving fastest,
  -- until the statement reads: the parser meets a name before it checks the sorts around
  -- it, so a name's sort cannot be told from one error, and a wrong sort hides the names
  -- after it
  let options := c.spec.st.env.sorts.size * 2
  let mut extra : Array Mm0.VarDecl := #[]
  let mut assignment : Array Nat := #[]
  let mut read : Except String (Prove.Exp × Nat) := .error "the statement does not read"
  let mut tries := 0
  while tries < 4096 do
    tries := tries + 1
    let extra' := (Array.range extra.size).map fun k =>
      { extra[k]! with sort := assignment[k]! / 2, bound := assignment[k]! % 2 == 1 }
    match c.spec.formula thm (varsWith extra') holed 0 Prove.freshBase extra' with
    | .ok r =>
      read := .ok r
      extra := extra'
      break
    | .error e =>
      read := .error s!"the statement does not read: {e.msg}"
      match unknown e.msg with
      | some x =>
        if extra.any (·.name == some x) then break
        extra := extra.push { name := some x, sort := 0, bound := false, deps := #[] }
        assignment := assignment.push 0
      | none =>
        if extra.isEmpty then break
        -- the next assignment
        let mut k := extra.size
        let mut carried := true
        while carried && k > 0 do
          k := k - 1
          if assignment[k]! + 1 < options then
            assignment := assignment.set! k (assignment[k]! + 1)
            carried := false
          else assignment := assignment.set! k 0
        if carried then break
  let (goal, _) ← match read with
    | .ok r => pure r
    | .error msg => return ← say #[("error", Json.str msg)]
  let vars := varsWith extra
  let extraConsts : Array Prove.ConstInfo := (Array.range extra.size).map fun k =>
    { ty := Prove.Ty.mk extra[k]!.sort extra[k]!.bound, names := if extra[k]!.bound then #[nb + k] else #[] }
  -- the holes of one name are one metavariable, numbered from freshBase in order
  let distinct := names.foldl (init := #[]) fun acc n => if acc.contains n then acc else acc.push n
  let holeNodes := goal.nodes.filter fun n => Prove.Node.isVar n && Prove.Node.varId n ≥ Prove.freshBase
  let byHole : Std.HashMap Nat Nat := holeNodes.foldl (init := {}) fun m n => m.insert (Prove.Node.varId n) (Prove.Node.ty n)
  let same : Std.HashMap Nat Prove.SubExp := (Array.range names.size).foldl (init := {}) fun m j =>
    let k := (distinct.findIdx? (· == names[j]!)).getD j
    let ty := byHole[Prove.freshBase + j]?.getD 0
    m.insert (Prove.freshBase + j) (Prove.SubExp.mk' (Prove.Node.var (Prove.freshBase + j) ty)
      (Prove.Exp.ofVar (Prove.Node.var (Prove.freshBase + k) ty)))
  let s : Prove.Subst := { map := same }
  let goal := s.apply goal
  let metas := (Array.range distinct.size).filterMap fun k =>
    (names.findIdx? (· == distinct[k]!)).bind fun j =>
      byHole[Prove.freshBase + j]?.map fun ty => Prove.Node.var (Prove.freshBase + k) ty
  let task := { db.task thm with goal, metas, consts := (db.task thm).consts ++ extraConsts }
  let contexts ← loadContexts args c.prior db.asserts.size
  let env := { Prove.Env.init db c.index task c.hypIndexes with uses := c.uses, prior := c.prior.query thm, contexts }
  let (model, cheap, value) ← match ← loadModels args true with
    | .ok ms => pure ms
    | .error e => IO.eprintln e; return 1
  -- by default the procedures at the root first (ring, congruence: a hole that is an
  -- identity closes in milliseconds), then the learned search with the models found
  -- (`learned(value=4)`, the bench's best setting), or without a ranker the proofs of one
  -- or two steps, which guided may miss for a longer one that a rail gives: a gap is
  -- short, and its term is read
  let tacticText := (strOption args "--tactic").getD <|
    "first(follow(ring, at=root), follow(congr, at=root), " ++
      (match model, value with
        | some _, some _ => "learned(value=4))"
        | some _, none => "learned)"
        | none, _ => "seq(bfs(size=20000, depth=2), guided))")
  let dsl : Prove.Dsl.Ctx := { db, spec := some c.spec, thm, vars, rails := some c.rails, defs, model, cheap, value }
  let limits : Prove.Limits := { maxMs := numOption args "--ms" 5000, maxProps := numOption args "--max-nodes" 2000000 }
  let pr := c.spec.printer db (c.spec.binderNames thm ++ extra.map fun vd => vd.name.getD "_")
  let hyps := db.file.thmHypNames thm
  let extraJson : Array (String × Json) :=
    if extra.isEmpty then #[] else #[("extra", .arr (extra.map fun vd => Json.str (vd.name.getD "_")))]
  -- a strategy is one universe up: it is used where it is read
  match Prove.Dsl.parseTactic dsl tacticText with
  | .error e => say #[("error", Json.str (Prove.Dsl.ParseError.show tacticText e))]
  | .ok strategy =>
    let start ← IO.monoMsNow
    let r ← Prove.searchWith Prove.acceptAny env strategy.strategy limits
    let ms := (← IO.monoMsNow) - start
    match r.proof with
    | none =>
      say (#[("proved", .bool false), ("ms", Json.ofNat ms), ("nodes", Json.ofNat r.env.props.size)] ++ extraJson)
    | some t =>
      say (#[("proved", .bool true), ("ms", Json.ofNat ms), ("nodes", Json.ofNat r.env.props.size),
        ("steps", Json.ofNat t.size), ("term", Json.str (t.mm1 db pr hyps .short)),
        ("bound", Json.str (t.mm1 db pr hyps .bound)), ("explicit", Json.str (t.mm1 db pr hyps .explicit)),
        ("values", .arr (r.values.map fun e => Json.str (pr.render e Prove.mm1Dummy)))] ++ extraJson)

/-- `mcp`: the MCP server for an agent, on stdin and stdout (`Mcp/Server.lean`). -/
def mcpServe (mm0 mmb : String) (args : List String) : IO UInt32 := do
  let defs ← match ← Prove.Dsl.loadTactics (strOption args "--tactics") with
    | .ok defs => pure defs
    | .error msg =>
      IO.eprintln msg
      return 1
  let (model, cheap, value) ← match ← loadModels args true with
    | .ok ms => pure ms
    | .error e => IO.eprintln e; return 1
  match ← Mcp.Ctx.load mm0 mmb (anonymous := args.contains "--anonymous") with
  | .error msg =>
    IO.eprintln msg
    return 1
  | .ok c =>
    let c := { c with defs, exportDir := (strOption args "--export").map System.FilePath.mk, model, cheap, value }
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
  | "prove" :: "db" :: path :: rest => proveDb path rest
  | "dsl" :: rest =>
    match ← Prove.Dsl.loadTactics (strOption rest "--tactics") with
    | .ok defs =>
      IO.print (Prove.Dsl.helpWith defs)
      return 0
    | .error msg =>
      IO.eprintln msg
      return 1
  | "mcp" :: mm0 :: mmb :: rest => mcpServe mm0 mmb rest
  | "prove" :: "replay" :: path :: rest => proveReplay path rest
  | "prove" :: "search" :: path :: rest => proveSearch path rest
  | "prove" :: "chains" :: path :: rest => proveChains path rest
  | "prove" :: "variants" :: path :: rest => proveVariants path rest
  | "prove" :: "subproofs" :: path :: rest => proveSubproofs path rest
  | "prove" :: "rails" :: path :: rest => proveRails path rest
  | "prove" :: "goal" :: mm0 :: mmb :: rest => proveGoal mm0 mmb rest
  | "prove" :: "export" :: path :: rest => proveExport path rest
  | "prove" :: "prior" :: path :: rest => provePrior path rest
  | "prove" :: "contexts" :: path :: rest => proveContexts path rest
  | "prove" :: "score" :: path :: rest => proveScore path rest
  | "prove" :: "featbench" :: path :: rest => proveFeatbench path rest
  | "prove" :: "subgoals" :: path :: rest => proveSubgoals path rest
  | _ =>
    IO.eprintln usage
    return 2
