/-
The proof checker over real proof files: those of the MM0 repository (`MM0_REPO`) and
those built by `scripts/build-corpus.sh` into `.tools/corpus`. Both are optional; what
is absent is skipped and reported.

Every valid file must be accepted: this is the first acceptance test of the verifier.
The mutants of the MM0 repository that the reader lets through must be rejected here,
each for its own reason.
-/
import Whitehead.Verify.Check
import Tests.Mmb.Corpus
import Tests.Harness

open Whitehead.Mmb Whitehead.Verify

namespace Tests.Verify

/-- Files of the corpus that are not valid, with a fragment of the expected error.
`hello_assembler.mm1` is an unfinished example: one of its theorems is proved with
`sorry`. -/
def knownInvalid : List (String × String) :=
  [("hello_assembler", "Sorry")]

/-- The mutants of `tests/mmb` that decode (`Tests.Mmb.readerAccepts`), with a fragment
of the error each must give. -/
def mutantErrors : List (String × String) :=
  [("fail/bad_return.mmb", "the term table gives the result sort"),
   ("fail/disjoint.mmb", "disjoint variable violation"),
   ("fail/gi_dummy_reserved_bit.mmb", "more than 55 bound variables"),
   ("fail/one_bad_decl.mmb", "the term table gives the result sort"),
   ("fail/pure_sort.mmb", "pure sort"),
   ("fail/unify_mismatch.mmb", "unify failure"),
   ("fail/uses_sorry.mmb", "Sorry")]

def corpusTests : TestM Unit := do
  let mut paths : Array System.FilePath := #[]
  match ← IO.getEnv "MM0_REPO" with
  | none => skip "verifier on the proof files of the MM0 repository" "set MM0_REPO to a checkout"
  | some repo =>
    let root : System.FilePath := repo
    for dir in Tests.Mmb.acceptDirs do
      paths := paths ++ (← Tests.Mmb.mmbFiles (root / dir))
    for (rel, part) in mutantErrors do
      let name := s!"verify mutant: {rel} is rejected"
      match MmbFile.parse (← IO.FS.readBinFile (root / "tests" / "mmb" / rel)) with
      | .error e => check name false s!"the reader rejects it: {e.msg}"
      | .ok f =>
        match checkProofs f with
        | .ok () => check name false "accepted"
        | .error e => check name (contains (e.format f rel) part) (e.format f rel)
  let built ← Tests.Mmb.mmbFiles ".tools/corpus"
  if built.isEmpty then
    skip "verifier on the proof files of .tools/corpus" "run scripts/build-corpus.sh"
  paths := paths ++ built
  let mut files := 0
  let mut stmts := 0
  for path in paths do
    let name := s!"verify corpus: {path}"
    match MmbFile.parse (← IO.FS.readBinFile path) with
    | .error e => check name false (e.format path.toString)
    | .ok f =>
      let invalid := knownInvalid.lookup (path.fileStem.getD "")
      match checkProofs f, invalid with
      | .ok (), none =>
        check name true
        files := files + 1
        stmts := stmts + f.stmts.size
      | .ok (), some _ => check name false "accepted, but it is listed as invalid"
      | .error e, none => check name false (e.format f path.toString)
      | .error e, some part => check name (contains e.msg part) (e.format f path.toString)
  if files > 0 then
    IO.println s!"verifier corpus: the proofs of {files} files are accepted, {stmts} statements"

end Tests.Verify
