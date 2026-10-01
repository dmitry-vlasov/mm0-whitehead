/-
Runs the `.mm0` parser over the `.mm0` files of a checkout of the MM0 repository.

The checkout is found through the environment variable `MM0_REPO`; without it these
tests are skipped. Nothing from that repository is copied here.
-/
import Whitehead.Mm0.Parser
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

/-- `import "file";` is an extension of `mm0-rs` (resolved by `mm0-rs join`) and is not
part of the grammar in `mm0.md`. To exercise the parser on the files that use it, lines
that start with `import "` are overwritten with spaces, which keeps all offsets. Returns
the new source and the number of lines blanked. -/
def blankImports (src : ByteArray) : ByteArray × Nat := Id.run do
  let key := "import \"".toUTF8
  let mut out := src
  let mut count := 0
  let mut lineStart := 0
  while lineStart < src.size do
    let mut lineEnd := lineStart
    while lineEnd < src.size && src.get! lineEnd != 0x0A do
      lineEnd := lineEnd + 1
    if lineEnd - lineStart ≥ key.size && src.extract lineStart (lineStart + key.size) == key then
      count := count + 1
      for i in [lineStart:lineEnd] do
        out := out.set! i 0x20
    lineStart := lineEnd + 1
  return (out, count)

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
  let mut withImports := 0
  for dir in acceptDirs do
    for path in ← mm0Files (root / dir) do
      let (src, imports) := blankImports (← IO.FS.readBinFile path)
      if imports > 0 then withImports := withImports + 1
      let name := s!"corpus: {path}"
      match parse src with
      | .error e => check name false (e.format path.toString src)
      | .ok ss =>
        files := files + 1
        bytes := bytes + src.size
        stmts := stmts + ss.size
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
  IO.println s!"mm0 corpus: parsed {files} files, {bytes} bytes, {stmts} statements \
    ({withImports} files with `import` lines blanked)"

end Tests.Mm0
