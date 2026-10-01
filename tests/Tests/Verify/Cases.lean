/-
One proof file per rule of the verifier: `tests/fixtures/verify`, assembled by `gen.py`
there. `cases.tsv` gives for each file our expected verdict (`OK` or a fragment of the
error message), the verdicts of `mm0-rs` and mm0-c (`A` accept, `R` reject), and, where
`mm0-rs` does not agree with us, the point of `docs/MMB-NOTES.md` section 9 that
explains it.

Our verdict is always checked. Those of the other two are checked when the tools are
there (`.tools/bin`, built by `scripts/build-oracles.sh`): this is the differential test
on hand-written cases.
-/
import Whitehead.Verify.Check
import Tests.Harness

open Whitehead.Mmb Whitehead.Verify

namespace Tests.Verify

def caseDir : System.FilePath := "tests/fixtures/verify"

/-- `A` or `R`: does the command exit with 0? -/
def oracleVerdict (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args, stdin := .null }
  return if out.exitCode == 0 then "A" else "R"

def findTool (name : String) : IO (Option String) := do
  let p : System.FilePath := ".tools/bin" / name
  return if ← p.pathExists then some p.toString else none

def caseTests : TestM Unit := do
  let table ← IO.FS.readFile (caseDir / "cases.tsv")
  let mm0rs ← findTool "mm0-rs"
  let mm0c ← findTool "mm0-c-np"
  if mm0rs.isNone || mm0c.isNone then
    skip "verdicts of mm0-rs and mm0-c on the verifier cases" "run scripts/build-oracles.sh"
  let mut differences := 0
  for line in table.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn "\t" with
    | [name, ours, rs, c, note] =>
      let path := caseDir / s!"{name}.mmb"
      let bytes ← IO.FS.readBinFile path
      -- ours
      let actual : Except String Unit :=
        match MmbFile.parse bytes with
        | .error e => .error s!"reader: {e.msg}"
        | .ok f =>
          match checkProofs f with
          | .ok () => .ok ()
          | .error e => .error (e.format f name)
      match actual with
      | .ok () => check s!"case {name}" (ours == "OK") s!"accepted; expected an error containing \"{ours}\""
      | .error msg => check s!"case {name}" (ours != "OK" && contains msg ours) msg
      -- a difference from the reference implementation must come with its explanation
      let oursAR := if ours == "OK" then "A" else "R"
      if rs != oursAR then
        differences := differences + 1
        check s!"case {name}: the difference from mm0-rs is explained" (!note.isEmpty)
      -- theirs
      if let some tool := mm0rs then
        checkEq s!"case {name}: mm0-rs" (← oracleVerdict tool #["compile", "-q", path.toString]) rs
      if let some tool := mm0c then
        checkEq s!"case {name}: mm0-c" (← oracleVerdict tool #[path.toString]) c
    | _ => check s!"cases.tsv: malformed line `{line}`" false
  IO.println s!"verifier cases: {differences} of them are judged differently by mm0-rs, each with its reason"

end Tests.Verify
