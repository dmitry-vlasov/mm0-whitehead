/-
Tests of the MM1 terms of proofs (`Prove/Mm1.lean`) on `tests/fixtures/prove/logic.mmb`:
a proof found by the search in each of the three forms, and the metavariables of an MM1
goal made holes.
-/
import Whitehead.Prove.Session
import Whitehead.Prove.Mm1
import Tests.Prove.Engine
import Tests.Prove.Filter

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def mm1Tests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some file := MmbFile.parse bytes |>.toOption | check "mm1: the fixture is read" false; return
  let some db := Db.ofFile file |>.toOption | check "mm1: the fixture becomes a database" false; return
  let st ← match ← Whitehead.Mm0.load logicSpecPath with
    | .error e => check "mm1: the specification is read" false e.format; return
    | .ok spec =>
      match Whitehead.Mm0.elaborateState spec with
      | .ok st => pure st
      | .error e => check "mm1: the specification is read" false e.format; return
  let spec := Notation.ofSpec st file
  let vc := Whitehead.Verify.Ctx.ofFile file
  let id := thmId db
  let thm := id "syl"
  let r ← search vc (Env.init db db.index (db.task thm)) breadthFirst { maxProps := 100000 }
  match r.proof with
  | none => check "mm1: syl is proved" false
  | some t =>
    let pr := spec.printer db (spec.binderNames thm)
    let hyps := file.thmHypNames thm
    let h (i : Nat) : String := hyps[i]!
    checkEq "mm1: a proof, short: the proofs of the hypotheses only" (t.mm1 db pr hyps .short)
      s!"(mpd {h 1} (a1i {h 0}))"
    checkEq "mm1: without bound variables, bound is short" (t.mm1 db pr hyps .bound) (t.mm1 db pr hyps .short)
    let e := t.mm1 db pr hyps .explicit
    check "mm1: explicit, every variable as a formula" (contains e "(! mpd $ " && contains e "(! a1i $ ") e
  checkEq "mm1: the metavariables of a goal made holes, by name"
    (mm1Holes "G /\\ ~?a -> a = ?b /\\ ?a") ("G /\\ ~_ -> a = _ /\\ _", #["a", "b", "a"])
  checkEq "mm1: a goal without metavariables" (mm1Holes "a -> b") ("a -> b", #[])

end Tests.Prove
