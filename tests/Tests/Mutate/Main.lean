/-
`lake exe mutate`: differential testing of the verifier on mutated proof files.

    lake exe mutate FILE.mmb [--count N] [--seed S] [--mm0-rs PATH] [--mm0-c PATH] [--dir DIR]

Makes N mutants of a valid proof file (`Tests/Mutate/Engine.lean`), checks each with our
verifier and with `mm0-rs compile`, and compares the two verdicts. Where they differ,
the difference must be one of the known ones (`docs/MMB-NOTES.md`, section 9); anything
else is reported with what was mutated and the mutant is kept in DIR, to be examined.
The exit code is 1 if there is anything unexplained.

Run it with `LEAN_ABORT_ON_PANIC=1`: a mutant must never make the verifier index out of
bounds, and that setting turns such a bug into a crash instead of a message.
-/
import Whitehead.Verify.Check
import Tests.Mutate.Engine

open Whitehead.Mmb Whitehead.Verify Tests.Mutate

/-- Our verdict: `none` if accepted, else the message and, for a failure inside a
statement, that statement and whether the failure is in its body. -/
structure Rejection where
  msg : String
  /-- The failing statement is an axiom or a definition, and the failure is in its
  proof body or in the checks at its end, not in its binders. -/
  inAxiomOrDefBody : Bool

def ourVerdict (bytes : ByteArray) : Option Rejection :=
  match MmbFile.parse bytes with
  | .error e => some ⟨s!"reader: {e.msg}", false⟩
  | .ok f =>
    match checkProofs f with
    | .ok () => none
    | .error e =>
      let inBody := match e.stmt.bind (f.stmts[·]?) with
        | some s =>
          let hasBody := match s.kind with
            | .ax => true
            | .termDef _ => f.terms[s.index]!.isDef
            | _ => false
          hasBody && e.pos != s.pos
        | none => false
      some ⟨e.format f "mutant", inBody⟩

/-- Why `mm0-rs` may accept what we reject: the point of MMB-NOTES section 9. -/
def explain (r : Rejection) : Option String :=
  let has (part : String) : Bool := (r.msg.splitOn part).length > 1
  if has "Sorry" then some "point 6: mm0-rs accepts Sorry"
  else if r.inAxiomOrDefBody then some "point 8: mm0-rs does not read the body of an axiom or definition"
  else if has "the term table gives the result sort" then some "point 9: mm0-rs does not compare the table's sort"
  else if has "more than 55 bound variables" then some "point 10: mm0-rs lets a 56th bound variable pass"
  else if has "exactly its own bit" then some "point 11: mm0-rs ignores the dependency bits of a bound binder"
  else if has "the header has" then some "point 20: mm0-rs does not count statements"
  -- a table entry that no statement declares is never looked at by mm0-rs; our reader
  -- reads every entry of the tables
  else if has "reader: the binders of" then some "point 20: a table entry that no statement declares is unreadable"
  else none

structure Options where
  file : String := ""
  count : Nat := 1000
  seed : Nat := 1
  mm0rs : String := ".tools/bin/mm0-rs"
  /-- `mm0-c` built with `NO_PARSER`, as a third opinion on what the other two accept. -/
  mm0c : Option String := none
  dir : String := ".tools/mutants"

partial def parseArgs (o : Options) : List String → Except String Options
  | [] => if o.file.isEmpty then .error "no input file" else .ok o
  | "--count" :: n :: rest => parseArgs { o with count := n.toNat! } rest
  | "--seed" :: n :: rest => parseArgs { o with seed := n.toNat! } rest
  | "--mm0-rs" :: p :: rest => parseArgs { o with mm0rs := p } rest
  | "--dir" :: p :: rest => parseArgs { o with dir := p } rest
  | "--mm0-c" :: p :: rest => parseArgs { o with mm0c := some p } rest
  | arg :: rest => if o.file.isEmpty then parseArgs { o with file := arg } rest else .error s!"unexpected argument {arg}"

def main (args : List String) : IO UInt32 := do
  let o ←
    match parseArgs {} args with
    | .ok o => pure o
    | .error msg =>
      IO.eprintln s!"mutate: {msg}\nusage: mutate FILE.mmb [--count N] [--seed S] [--mm0-rs PATH] [--dir DIR]"
      return 2
  let bytes ← IO.FS.readBinFile o.file
  let f ←
    match MmbFile.parse bytes with
    | .ok f => pure f
    | .error e =>
      IO.eprintln (e.format o.file)
      return 2
  if let some r := ourVerdict bytes then
    IO.eprintln s!"mutate: the base file must be valid, but: {r.msg}"
    return 2
  IO.FS.createDirAll o.dir
  let stem := (o.file : System.FilePath).fileStem.getD "base"
  let tmp : System.FilePath := (o.dir : System.FilePath) / s!"{stem}-current.mmb"
  let mut rng : Rng := ⟨o.seed.toUInt64 * 2654435761 + 1⟩
  let mut bothReject := 0
  let mut bothAccept := 0
  let mut explained : Array (String × Nat) := #[]
  let mut unexplained := 0
  let mut cRejects := 0
  for i in [0:o.count] do
    let (mutant, rng') := nextMutant f rng
    rng := rng'
    let ours := ourVerdict mutant.bytes
    IO.FS.writeBinFile tmp mutant.bytes
    let out ← IO.Process.output { cmd := o.mm0rs, args := #["compile", "-q", tmp.toString], stdin := .null }
    let theirs := out.exitCode == 0
    match ours, theirs with
    | none, true =>
      bothAccept := bothAccept + 1
      if let some mm0c := o.mm0c then
        let out ← IO.Process.output { cmd := mm0c, args := #[tmp.toString], stdin := .null }
        if out.exitCode != 0 then
          cRejects := cRejects + 1
          let reason := (out.stderr.splitOn "\n").filter (fun l => !l.isEmpty && !l.startsWith "stmt" && !l.startsWith "cmd") |>.head?
          IO.println s!"accepted by us and mm0-rs, rejected by mm0-c #{i}: {mutant.what}: {reason.getD ""}"
    | some _, false => bothReject := bothReject + 1
    | some r, true =>
      match explain r with
      | some why =>
        explained := match explained.findIdx? (·.1 == why) with
          | some k => explained.modify k fun (w, n) => (w, n + 1)
          | none => explained.push (why, 1)
      | none =>
        unexplained := unexplained + 1
        let keep := (o.dir : System.FilePath) / s!"{stem}-seed{o.seed}-{i}.mmb"
        IO.FS.writeBinFile keep mutant.bytes
        IO.println s!"UNEXPLAINED #{i}: we reject, mm0-rs accepts\n  mutation: {mutant.what}\n  ours: {r.msg}\n  kept as {keep}"
    | none, false =>
      unexplained := unexplained + 1
      let keep := (o.dir : System.FilePath) / s!"{stem}-seed{o.seed}-{i}.mmb"
      IO.FS.writeBinFile keep mutant.bytes
      let theirMsg := (out.stdout.splitOn "\n").filter (fun l => (l.splitOn "error").length > 1) |>.head?
      IO.println s!"UNEXPLAINED #{i}: we accept, mm0-rs rejects\n  mutation: {mutant.what}\n  mm0-rs: {theirMsg.getD out.stdout}\n  kept as {keep}"
  IO.FS.removeFile tmp
  IO.println s!"{o.file}: {o.count} mutants, seed {o.seed}"
  IO.println s!"  rejected by both: {bothReject}"
  IO.println s!"  accepted by both: {bothAccept}"
  if o.mm0c.isSome then
    IO.println s!"    of these, rejected by mm0-c: {cRejects}"
  for (why, n) in explained do
    IO.println s!"  rejected by us only, {why}: {n}"
  IO.println s!"  unexplained: {unexplained}"
  return if unexplained == 0 then 0 else 1
