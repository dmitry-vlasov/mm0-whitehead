/-
Tests of the ring procedure (`Whitehead/Prove/Ring.lean`) on `peano.mmb` of the corpus:
the ring the table reads by shape, the normalization, the plan for a goal, and
`follow(ring)` proving identities of `+` and `*` from the lemmas before them.
-/
import Whitehead.Prove.Dsl
import Tests.Prove.Engine
import Tests.Prove.Congr

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

def ringTests : TestM Unit := do
  let path : System.FilePath := ".tools/corpus/peano.mmb"
  if !(← path.pathExists) then
    skip "ring on peano.mmb" "run scripts/build-corpus.sh"
    return
  let file ← match MmbFile.parse (← IO.FS.readBinFile path) with
    | .ok f => pure f
    | .error e => check "ring: peano is read" false e.msg; return
  let db ← match Db.ofFile file with
    | .ok db => pure db
    | .error msg => check "ring: peano becomes a database" false msg; return
  let tb := CongrTable.ofDb db
  let rt := RingTable.ofDb db
  let id (n : String) : Nat := thmId db n
  let term (n : String) : Nat := (db.terms.findIdx? (·.name == n)).getD 1000000
  let name (k : Nat) : String := db.asserts[k]!.name
  checkEq "ring: the lift under an antecedent" (rt.lift.map name) (some "a1i")
  -- the ring of the natural numbers: add, mul, no negation, d0 and d1, no closure
  match rt.rings.find? fun rg => rg.eq == term "eq" && rg.add.term == term "add" with
  | none => check "ring: peano's ring of eq, add and mul" false s!"{rt.rings.size} rings"
  | some rg =>
    checkEq "ring: the multiplication, the units, no negation, no closure"
      (rg.mul.term, rg.zero == Exp.mkApp (term "d0") rg.zero.ty #[], rg.one == Exp.mkApp (term "d1") rg.one.ty #[], rg.neg.isNone, rg.carrier.isNone)
      (term "mul", true, true, true, true)
    let rule (sh : RingShape) : Option String := (rg.rules[(sh, false)]?).map fun r => name r.id
    checkEq "ring: the rules, by shape"
      #[rule .comm, rule .assoc, rule .lcomm, rule .unitR, rule .unitL, rule .mulComm, rule .mulAssoc, rule .oneR, rule .zeroR, rule .distL, rule .distR]
      #[some "addcom", some "addass", some "addlass", some "add0", some "add01", some "mulcom", some "mulass", some "mul12", some "mul0", some "muladd", some "addmul"]
    checkEq "ring: transitivity and symmetry, by form"
      #[(rg.trans[false]?).map name, (rg.trans4[false]?).map name, (rg.symm[false]?).map name, (rg.trans[true]?).map name]
      #[none, some "eqtr4i", some "eqcomi", some "eqtrd"]
    -- normalization: (a + b) + c and (a + c) + b meet
    let task := db.task (id "addrass")
    match CongrTable.binary task.goal with
    | none => check "ring: addrass is an equation" false
    | some (_, l, r) =>
      let tl := RTerm.ofExp rg l
      let tr := RTerm.ofExp rg r
      match tl.normalize, tr.normalize with
      | some (sl, nl), some (sr, nr) =>
        check "ring: both sides of addrass normalize to one term, in normal form"
          (nl == nr && nl.isNormal && !sl.isEmpty && !sr.isEmpty) s!"{repr sl} {repr sr}"
      | _, _ => check "ring: both sides of addrass normalize" false
    checkEq "ring: the plan for addrass's statement has a skeleton" ((rt.planGoal tb (id "addrass") task.goal).map (showSkeleton db) |>.map (·.length != 0)) (some true)
    check "ring: no plan for a goal that is not a ring identity" (rt.planGoal tb (id "eqcomd") (db.task (id "eqcomd")).goal).isNone
  -- in a search: follow(ring) proves identities from the lemmas before them
  let vc := Whitehead.Verify.Ctx.ofFile file
  let rails : Thunk Rails := Thunk.mk fun _ => Rails.ofDb db
  let uses := Uses.ofFile file db.asserts.size
  for n in ["addrass", "mullass", "addlass"] do
    let ctx : Dsl.Ctx := { db, thm := id n, rails := some rails }
    match Dsl.parseTactic ctx "follow(ring, at=root)" with
    | .error e => check s!"ring: follow(ring) proves {n}" false e.msg
    | .ok t =>
      let r ← search vc { Env.init db db.index (db.task (id n)) with uses } t.strategy { maxProps := 200000, maxMs := 10000 }
      check s!"ring: follow(ring) proves {n} from the lemmas before it" (r.ending == .proved) s!"{r.env.counters.expanded} expanded"

end Tests.Prove
