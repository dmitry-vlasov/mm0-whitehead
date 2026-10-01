/-
Runs the `.mmb` reader over real proof files: those of the MM0 repository (`MM0_REPO`)
and those built by `scripts/build-corpus.sh` into `.tools/corpus`. Both are optional;
what is absent is skipped and reported.

For every file that must decode, the test also checks the round trip: each unify stream
and each proof body, decoded and encoded again, gives the original bytes; and `dump`
runs to the end.
-/
import Whitehead.Mmb.Reader
import Whitehead.Mmb.Encode
import Whitehead.Mmb.Dump
import Tests.Harness

open Whitehead.Mmb

namespace Tests.Mmb

/-- Directories of the MM0 repository whose `.mmb` files are well-formed. -/
def acceptDirs : List String :=
  ["mm0-js/test", "examples/tutorial", "mm0-rs/components/mm0b_parser/test_resources",
   "tests/mmb/pass"]

/-- The mutants of the MM0 repository (`tests/mmb/mutate.py`) that the reader must
reject: something in them cannot be decoded. With one exception these are the files
that `mm0-rs` rejects while reading, before its kernel sees anything. The exception is
`unknown_op`, whose bad opcode is in the proof body of an axiom, which `mm0-rs` does not
read. -/
def readerRejects : List String :=
  ["fail/bad_arg.mmb", "fail/bad_args_pointer.mmb", "fail/bad_magic.mmb", "fail/bad_step.mmb",
   "fail/bad_stream.mmb", "fail/capped.mmb", "fail/many_bad.mmb", "fail/underflow.mmb",
   "fail/unknown_op.mmb", "fail/unmatched.mmb", "fail/wrong_kind.mmb",
   "fail-index/bad_index_pointer.mmb", "fail-index/partial_index.mmb",
   "run/gi_header_p_index_overflow.mmb"]

/-- The mutants that decode: what is wrong with them is for the verifier to find. -/
def readerAccepts : List String :=
  ["fail/bad_return.mmb", "fail/disjoint.mmb", "fail/gi_dummy_reserved_bit.mmb",
   "fail/one_bad_decl.mmb", "fail/pure_sort.mmb", "fail/unify_mismatch.mmb",
   "fail/uses_sorry.mmb"]

def mmbFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  if !(← dir.isDir) then return #[]
  let entries ← dir.readDir
  let files := entries.filterMap fun e =>
    if e.path.extension == some "mmb" then some e.path else none
  return files.qsort (·.toString < ·.toString)

structure Counts where
  unifyStreams : Nat := 0
  proofCmds : Nat := 0
  dumpLines : Nat := 0

/-- Every stream of `f`, decoded and encoded again, must give the bytes it was read
from. Returns the number of unify streams and of proof commands. -/
def roundTrip (f : MmbFile) : Except String (Nat × Nat) := do
  let mut streams := 0
  let mut cmds := 0
  let unify (what : String) (pos : Nat) : Except String Unit :=
    match Reader.readUnify f.bytes pos #[] with
    | .error e => .error s!"{what}: 0x{hex e.pos}: {e.msg}"
    | .ok (cs, stop) =>
      if encodeUnify cs == f.bytes.extract pos stop then .ok ()
      else .error s!"{what}: the unify stream at 0x{hex pos} does not re-encode to the same bytes"
  for i in [0:f.terms.size] do
    if f.terms[i]!.isDef then
      unify s!"term {i}" (f.termUnifyPos i)
      streams := streams + 1
  for i in [0:f.thms.size] do
    unify s!"theorem {i}" (f.thmUnifyPos i)
    streams := streams + 1
  for s in f.stmts do
    if f.hasBody s then
      match f.proofCmds s with
      | .error e => throw s!"0x{hex e.pos}: {e.msg}"
      | .ok cs =>
        if encodeProof cs != f.bytes.extract s.bodyStart s.stop then
          throw s!"the proof body at 0x{hex s.bodyStart} does not re-encode to the same bytes"
        cmds := cmds + cs.size
  return (streams, cmds)

/-- `path` decodes completely, round-trips, and dumps. -/
def decodes (path : System.FilePath) : TestM (Option Counts) := do
  let name := s!"mmb corpus: {path}"
  let bytes ← IO.FS.readBinFile path
  match MmbFile.parse bytes with
  | .error e => check name false (e.format path.toString); return none
  | .ok f =>
    match f.checkStreams with
    | .error e => check name false (e.format path.toString); return none
    | .ok () =>
      match roundTrip f with
      | .error msg => check name false msg; return none
      | .ok (streams, cmds) =>
        let lines ← IO.mkRef 0
        match ← (dump f fun _ => lines.modify (· + 1)).run with
        | .error e => check name false s!"dump: {e.format path.toString}"; return none
        | .ok () =>
          check name true
          return some { unifyStreams := streams, proofCmds := cmds, dumpLines := ← lines.get }

def corpusTests : TestM Unit := do
  let mut files := 0
  let mut bytes := 0
  let mut total : Counts := {}
  let mut paths : Array System.FilePath := #[]
  match ← IO.getEnv "MM0_REPO" with
  | none => skip "mmb corpus of the MM0 repository" "set MM0_REPO to a checkout"
  | some repo =>
    let root : System.FilePath := repo
    for dir in acceptDirs do
      paths := paths ++ (← mmbFiles (root / dir))
    -- the mutants: the reader's verdict on each is fixed above
    for rel in readerRejects do
      let path := root / "tests" / "mmb" / rel
      let b ← IO.FS.readBinFile path
      let verdict := (MmbFile.parse b).bind fun f => f.checkStreams
      check s!"mmb mutant: {rel} is rejected by the reader" (verdict matches .error _)
    for rel in readerAccepts do
      let path := root / "tests" / "mmb" / rel
      let b ← IO.FS.readBinFile path
      match (MmbFile.parse b).bind fun f => f.checkStreams with
      | .ok () => check s!"mmb mutant: {rel} decodes" true
      | .error e => check s!"mmb mutant: {rel} decodes" false (e.format rel)
  let built ← mmbFiles ".tools/corpus"
  if built.isEmpty then
    skip "mmb corpus in .tools/corpus" "run scripts/build-corpus.sh"
  paths := paths ++ built
  for path in paths do
    if let some c ← decodes path then
      files := files + 1
      bytes := bytes + (← IO.FS.readBinFile path).size
      total := { unifyStreams := total.unifyStreams + c.unifyStreams,
                 proofCmds := total.proofCmds + c.proofCmds,
                 dumpLines := total.dumpLines + c.dumpLines }
  if files > 0 then
    IO.println s!"mmb corpus: decoded {files} files, {bytes} bytes: {total.unifyStreams} unify \
      streams and {total.proofCmds} proof commands round-trip; {total.dumpLines} lines of dump"

end Tests.Mmb
