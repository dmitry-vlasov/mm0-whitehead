/-
The elaborator against proof files: for a `.mm0`/`.mmb` pair, every statement of the
specification, elaborated from its text, must be the statement that the proof file
declares at the same place (`Whitehead.Verify.matchSpec`).

This compares two independent routes to the same data: ours through the notations of
the `.mm0` file, and that of the tool that wrote the `.mmb` file (`mm0-rs` or `mm0-hs`).
-/
import Whitehead.Mm0.Elab
import Whitehead.Verify.Spec
import Tests.Harness

open Whitehead Whitehead.Mm0 Whitehead.Mmb

namespace Tests.Mm0

/-- Pairs of the corpus whose two files do not belong together. `hello_assembler.mm1` is
unfinished: where the specification declares `def hello`, the proof file has a theorem.
mm0-c rejects the pair at the same statement. -/
def knownMismatches : List String := ["hello_assembler"]

/-- Loads, elaborates and matches one pair. -/
def checkPair (mm0 mmb : System.FilePath) : TestM Nat := do
  let name := s!"pair: {mm0} = {mmb}"
  let mismatch := knownMismatches.contains (mm0.fileStem.getD "")
  match ← load mm0 with
  | .error e => check name false e.format; return 0
  | .ok spec =>
    match elaborate spec with
    | .error e => check name false e.format; return 0
    | .ok env =>
      match MmbFile.parse (← IO.FS.readBinFile mmb) with
      | .error e => check name false (e.format mmb.toString); return 0
      | .ok f =>
        match Verify.matchSpec env f with
        | .error e =>
          check name (mismatch && contains e.msg "different kind") (e.format f mmb.toString)
          return 0
        | .ok n =>
          check name (!mismatch) "matched, but it is listed as a known mismatch"
          return n

def pairTests : TestM Unit := do
  let mut total := 0
  let mut pairs := 0
  -- the fixtures of this repository
  let mut list : Array (System.FilePath × System.FilePath) := #[
    ("tests/fixtures/mmb/small.mm0", "tests/fixtures/mmb/small.mmb")]
  for n in ["bound_arg_vars", "regular_arg_vars", "sorry_expr", "sorry_conv", "local_term",
      "axiom_body_mismatch", "ret_sort_mismatch"] do
    list := list.push (s!"tests/fixtures/disputed/{n}.mm0", s!"tests/fixtures/disputed/{n}.mmb")
  -- the pairs of the MM0 repository that come with a compiled proof file
  match ← IO.getEnv "MM0_REPO" with
  | none => skip "pairs of the MM0 repository" "set MM0_REPO to a checkout"
  | some repo =>
    let root : System.FilePath := repo
    list := list ++ #[
      (root / "examples/hol.mm0", root / "mm0-js/test/hol.mmb"),
      (root / "examples/peano.mm0", root / "mm0-js/test/peano.mmb"),
      (root / "examples/tutorial/02-mm0-intro.mm0", root / "examples/tutorial/03-mm1-intro.mmb"),
      (root / "tests/mmb/pass/max_bound_vars.mm0", root / "tests/mmb/pass/max_bound_vars.mmb")]
  -- the built corpus
  let corpus : System.FilePath := ".tools/corpus"
  if ← corpus.isDir then
    let entries ← corpus.readDir
    let names := (entries.filterMap fun e =>
      if e.path.extension == some "mmb" then e.path.fileStem else none).qsort (· < ·)
    for n in names do
      list := list.push (corpus / s!"{n}.mm0", corpus / s!"{n}.mmb")
  else
    skip "pairs of .tools/corpus" "run scripts/build-corpus.sh"
  for (mm0, mmb) in list do
    let n ← checkPair mm0 mmb
    if n > 0 then
      pairs := pairs + 1
      total := total + n
  IO.println s!"pairs: {pairs} specifications elaborated and matched against their proof files, \
    {total} statements"

end Tests.Mm0
