/-
Tests for the proof checker on hand-assembled proof files.

`tests/fixtures/mmb/small.mmb` and `tests/fixtures/verify/*.mmb` are valid or invalid in
one known way each; `tests/fixtures/disputed/*.mmb` are the files on which `mm0-rs` and
mm0-c disagree with each other or with the formal semantics (`docs/MMB-NOTES.md`,
section 9). The expected verdict of each file is written here, with the statement it
must fail in and a fragment of the message.
-/
import Whitehead.Verify.Check
import Tests.Harness

open Whitehead.Mmb Whitehead.Verify

namespace Tests.Verify

/-- Opens and checks the proofs of a file. -/
def verdict (path : System.FilePath) : IO (Except String Unit) := do
  let bytes ← IO.FS.readBinFile path
  match MmbFile.parse bytes with
  | .error e => return .error s!"reader: 0x{hex e.pos}: {e.msg}"
  | .ok f =>
    match checkProofs f with
    | .ok () => return .ok ()
    | .error e => return .error (e.format f path.toString)

def accepted (name : String) (path : System.FilePath) : TestM Unit := do
  match ← verdict path with
  | .ok () => check name true
  | .error msg => check name false msg

/-- The file is rejected, and the formatted error contains every one of `parts`. -/
def rejected (name : String) (path : System.FilePath) (parts : List String) : TestM Unit := do
  match ← verdict path with
  | .ok () => check name false "accepted"
  | .error msg => check name (parts.all (contains msg ·)) msg

def proofTests : TestM Unit := do
  accepted "verify: small.mmb" "tests/fixtures/mmb/small.mmb"
  let d : System.FilePath := "tests/fixtures/disputed"
  -- point 1: a variable in a bound argument position is a variable of the term
  rejected "verify: variables of a bound argument count (mm0-c accepts this file)"
    (d / "bound_arg_vars.mmb") ["theorem T1", "0xed", "disjoint variable"]
  rejected "verify: the control for it" (d / "regular_arg_vars.mmb")
    ["theorem T1", "0xed", "disjoint variable"]
  -- point 6: Sorry is not a proof
  rejected "verify: Sorry on an expression (mm0-rs accepts this file)" (d / "sorry_expr.mmb")
    ["theorem T0", "Sorry"]
  rejected "verify: Sorry on an obligation (mm0-rs accepts this file)" (d / "sorry_conv.mmb")
    ["theorem T0", "Sorry"]
  -- point 7: a local statement must be a def or a theorem
  rejected "verify: a local term (mm0-c accepts this file)" (d / "local_term.mmb")
    ["term t1", "local"]
  -- point 8: the proof body of an axiom is checked against its unify stream
  rejected "verify: an axiom whose body is not its statement (mm0-rs accepts this file)"
    (d / "axiom_body_mismatch.mmb") ["axiom T0", "unify"]
  -- point 9: the sort in the term table is the sort of the return type
  rejected "verify: term table sort and return type differ (mm0-rs accepts this file)"
    (d / "ret_sort_mismatch.mmb") ["term t0", "sort"]

end Tests.Verify
