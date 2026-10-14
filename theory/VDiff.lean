/-
`lake exe verify-diff [--mutants N] [--seed S] <file.mmb>...`: the reference verifier
(`Verifier.checkFile`, proved sound for the MM0 semantics) against the fast verifier
(`Whitehead.Verify.checkProofs`), statement by statement (`docs/VERIFIER-THEORY.md`,
milestone V5). For each file, and for `N` mutants of it (`Tests.Mutate`), the verdicts
are compared: accepted by both, or rejected by both at the same statement. A
disagreement is printed.
-/
import Verifier.OfMmb
import Whitehead.Verify.Check
import Mutate.Engine

open Whitehead.Mmb

inductive Verdict where
  | accept
  | reject (stmt : Option Nat) (msg : String)

def Verdict.text : Verdict → String
  | .accept => "accept"
  | .reject (some i) m => s!"reject at statement {i}: {m}"
  | .reject none m => s!"reject: {m}"

def fastVerdict (f : MmbFile) : Verdict :=
  match Whitehead.Verify.checkProofs f with
  | .ok () => .accept
  | .error e => .reject e.stmt e.msg

def refVerdict (f : MmbFile) : Verdict :=
  match Verifier.fileOf f with
  | .error m => .reject none s!"decode: {m}"
  | .ok vf =>
    match Verifier.firstFailure vf with
    | none => .accept
    | some i => if i = vf.stmts.length then .reject none "the counts at the end" else .reject (some i) "the machine rejects"

/-- Agreement: both accept, or both reject at the same statement (a whole-file
rejection, at no statement, matches the counts check). -/
def agree : Verdict → Verdict → Bool
  | .accept, .accept => true
  | .reject a _, .reject b _ => a == b
  | _, _ => false

structure Tally where
  agree : Nat := 0
  bothAccept : Nat := 0
  differ : Nat := 0
  unparsed : Nat := 0

def oneFile (name : String) (bytes : ByteArray) (tally : Tally) (show_ : Bool) : IO Tally := do
  match MmbFile.parse bytes with
  | .error _ => return { tally with unparsed := tally.unparsed + 1 }
  | .ok f =>
    let t0 ← IO.monoMsNow
    let fv := fastVerdict f
    let t1 ← IO.monoMsNow
    let rv := refVerdict f
    let t2 ← IO.monoMsNow
    if show_ then
      IO.println s!"{name}: fast {fv.text} ({t1 - t0} ms); reference {rv.text} ({t2 - t1} ms)"
    if agree fv rv then
      let ba := match fv with | .accept => 1 | _ => 0
      return { tally with agree := tally.agree + 1, bothAccept := tally.bothAccept + ba }
    else
      IO.println s!"DIFFER {name}: fast {fv.text}; reference {rv.text}"
      return { tally with differ := tally.differ + 1 }

def numOpt (args : List String) (name : String) (d : Nat) : Nat :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => v.toNat?.getD d
  | _ => d

def main (args : List String) : IO UInt32 := do
  let mutants := numOpt args "--mutants" 0
  let seed := numOpt args "--seed" 1
  let files := (args.filter (·.endsWith ".mmb"))
  let mut total : Tally := {}
  for path in files do
    let bytes ← IO.FS.readBinFile path
    total ← oneFile path bytes total true
    if mutants > 0 then
      match MmbFile.parse bytes with
      | .error _ => pure ()
      | .ok f =>
        let mut r : Tests.Mutate.Rng := ⟨seed.toUInt64⟩
        let mut t : Tally := {}
        for k in [0:mutants] do
          let (m, r') := Tests.Mutate.nextMutant f r
          r := r'
          t ← oneFile s!"{path} mutant {k} ({m.what})" m.bytes t false
        IO.println s!"{path}: {mutants} mutants: {t.agree} agree ({t.bothAccept} accepted by both), {t.differ} differ, {t.unparsed} not read"
        total := { agree := total.agree + t.agree, bothAccept := total.bothAccept + t.bothAccept,
                   differ := total.differ + t.differ, unparsed := total.unparsed + t.unparsed }
  IO.println s!"total: {total.agree} agree ({total.bothAccept} accepted by both), {total.differ} differ, {total.unparsed} not read"
  return (if total.differ == 0 then 0 else 1)
