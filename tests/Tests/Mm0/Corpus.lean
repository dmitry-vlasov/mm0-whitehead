/-
Runs the `.mm0` parser over the `.mm0` files of a checkout of the MM0 repository.

The checkout is found through the environment variable `MM0_REPO`; without it these
tests are skipped. Nothing from that repository is copied here.
-/
import Whitehead.Mm0.Load
import Whitehead.Mm0.Print
import Tests.Harness

open Whitehead.Mm0

namespace Tests.Mm0

/-- Directories of the MM0 repository whose `.mm0` files must parse. -/
def acceptDirs : List String :=
  ["examples", "examples/tutorial", "examples/join", "tests/mm0_mmu/pass", "tests/mmb/pass",
   "tests/mmb/fail", "tests/mmb/run", "tests/spec-x86",
   "mm0-rs/components/mm1_parser/test_resources"]

/-- The directory whose `.mm0` files must be rejected. -/
def rejectDir : String := "tests/mm0_mmu/fail"

/-- Files in `rejectDir` that are grammatical: what is wrong with them is not something
the primary parser looks at. -/
def grammaticalFailures : List String := ["blank_binder_alias.mm0"]

/-- The `mm0-rs` executable to compare `import` resolution against: `$MM0_RS`, or the one
that `scripts/build-oracles.sh` puts in `.tools/bin`. -/
def findMm0Rs : IO (Option String) := do
  if let some p ← IO.getEnv "MM0_RS" then return some p
  let p : System.FilePath := ".tools/bin/mm0-rs"
  return if ← p.pathExists then some p.toString else none

/-- Our joined form of `path` against that of `mm0-rs join --bare`, both printed by our
printer so that layout and comments do not matter. -/
def checkJoin (mm0rs : String) (path : System.FilePath) : TestM Unit := do
  let name := s!"join: {path}"
  match ← load path with
  | .error e => check name false e.format
  | .ok spec =>
    let out ← IO.Process.output { cmd := mm0rs, args := #["join", "--bare", path.toString] }
    if out.exitCode != 0 then
      check name false s!"mm0-rs join failed: {out.stderr}"
    else
      match parseString out.stdout with
      | .error e => check name false s!"output of mm0-rs join rejected: {e.format "<join>" out.stdout.toUTF8}"
      | .ok theirs =>
        check name (printStmts theirs == printStmts (spec.stmts.map (·.stmt)))
          "our joined specification differs from that of mm0-rs join"

def mm0Files (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.isDir) then return #[]
  let entries ← dir.readDir
  let files := entries.filterMap fun e =>
    if e.path.extension == some "mm0" then some e.path else none
  return files.qsort (·.toString < ·.toString)

def corpusTests : TestM Unit := do
  let some repo ← IO.getEnv "MM0_REPO"
    | skip "mm0 corpus" "set MM0_REPO to a checkout of https://github.com/digama0/mm0"
  let root : System.FilePath := repo
  let mut files := 0
  let mut bytes := 0
  let mut stmts := 0
  let mut withImports := #[]
  -- the specifications of the MM0 repository, and the joined ones of the built corpus
  let mut paths := #[]
  for dir in acceptDirs do
    paths := paths ++ (← mm0Files (root / dir))
  paths := paths ++ (← mm0Files ".tools/corpus")
  for path in paths do
    do
      let src ← IO.FS.readBinFile path
      let name := s!"corpus: {path}"
      match parse src with
      | .error e => check name false (e.format path.toString src)
      | .ok ss =>
        files := files + 1
        bytes := bytes + src.size
        stmts := stmts + ss.size
        if ss.any (fun s => s.kind matches .importFile ..) then
          withImports := withImports.push path
        let printed := printStmts ss
        match parseString printed with
        | .error e => check name false s!"printed form rejected: {e.format "<printed>" printed.toUTF8}"
        | .ok ss' => check name (printStmts ss' == printed) "printing is not stable under re-parsing"
  for path in ← mm0Files (root / rejectDir) do
    let src ← IO.FS.readBinFile path
    let name := s!"corpus: {path}"
    let grammatical := grammaticalFailures.contains (path.fileName.getD "")
    match parse src with
    | .ok _ => check name grammatical "accepted, but it is in the fail corpus"
    | .error e => check name (!grammatical) s!"rejected, but it is grammatical: {e.msg}"
  IO.println s!"mm0 corpus: parsed {files} files, {bytes} bytes, {stmts} statements"
  -- import resolution, compared with mm0-rs on every file that has imports
  match ← findMm0Rs with
  | none => skip "join against mm0-rs" "no mm0-rs: run scripts/build-oracles.sh or set MM0_RS"
  | some mm0rs =>
    for path in withImports do
      checkJoin mm0rs path
    IO.println s!"mm0 corpus: joined {withImports.size} files with imports, same as mm0-rs join"

end Tests.Mm0
