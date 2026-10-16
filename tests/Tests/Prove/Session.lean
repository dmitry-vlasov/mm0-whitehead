/-
Tests of a session (`Whitehead/Prove/Session.lean`) on `tests/fixtures/prove/logic.mmb`:
variants chosen by hand, the errors of a choice that is not one, a strategy run on the
tree as it is, and a search stopped at a limit and resumed, which finds what an
uninterrupted search finds.
-/
import Whitehead.Prove.Session
import Tests.Prove.Engine

open Whitehead.Mmb Whitehead.Prove

namespace Tests.Prove

/-- The variant of goal node `h` that applies the assertion with this name. -/
def variantNamed (s : Session) (h : Nat) (name : String) : Option Variant :=
  match s.variants h with
  | .ok vs => vs.find? (·.name == name)
  | .error _ => none

def sessionTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let file ←
    match MmbFile.parse bytes with
    | .ok f => pure f
    | .error e => check "session: the fixture is read" false e.msg; return
  let db ←
    match Db.ofFile file with
    | .ok db => pure db
    | .error msg => check "session: the fixture becomes a database" false msg; return
  let vc := Whitehead.Verify.Ctx.ofFile file
  let index := db.index
  let id := thmId db
  let startOn (name : String) : IO Session := Session.startFor vc (Env.init db index (db.task (id name)))
  let foundText (s : Session) : String := (s.found.map (proofText db ·.proof)).getD "none"
  -- a1i by hand: ax_mp at the root, then ax_1 at its major premise
  let s ← startOn "a1i"
  checkEq "session: at the start the root is the only goal" s.openGoals #[0]
  let rootText (s : Session) : String :=
    match s.variants 0 with
    | .ok vs => ", ".intercalate (vs.map fun v => s!"{v.prop} {v.name}{if v.expanded then "*" else ""}").toList
    | .error msg => msg
  check "session: the root has its variants, none expanded"
    (match s.variants 0 with | .ok vs => !vs.isEmpty && vs.all (!·.expanded) | .error _ => false)
    s!"{rootText s}; leafs {s.env.leafs}"
  let some mp := variantNamed s 0 "ax_mp"
    | check "session: ax_mp is a variant of the root" false; return
  let s ← match ← s.choose 0 #[mp.prop] with
    | .ok s => pure s
    | .error msg => check "session: ax_mp is chosen" false msg; return
  let some mp := variantNamed s 0 "ax_mp" | return
  check "session: the chosen variant is expanded and has a goal for each premise"
    (mp.expanded && mp.goals.size == 2)
  let minor := mp.goals[0]!
  let major := mp.goals[1]!
  check "session: the minor premise is proved by the hypothesis" (!s.openGoals.contains minor)
  check "session: the major premise is open" (s.openGoals.contains major)
  checkEq "session: not proved yet" (foundText s) "none"
  match ← s.choose 0 #[mp.prop] with
  | .ok _ => check "session: a variant is not chosen twice" false
  | .error msg => check "session: a variant is not chosen twice" (contains msg "expanded already") msg
  match ← s.choose major #[mp.prop] with
  | .ok _ => check "session: a variant of another node is not chosen" false
  | .error msg => check "session: a variant of another node is not chosen" (contains msg "not a variant") msg
  check "session: a node that is not there has no variants" (s.variants s.env.hyps.size |>.toOption |>.isNone)
  let some ax1 := variantNamed s major "ax_1"
    | check "session: ax_1 is a variant of the major premise" false; return
  let s ← match ← s.choose major #[ax1.prop] with
    | .ok s => pure s
    | .error msg => check "session: ax_1 is chosen" false msg; return
  checkEq "session: a1i is proved by the two choices" (foundText s) "(ax_mp h0 ax_1)"
  check "session: the proof is the verifier's" (s.found.any fun f => f.body.size > 0)
  -- a strategy run on a session finds what a search finds
  let limits : Limits := { maxProps := 5000, maxMs := 20000 }
  match ← (← startOn "syl").run breadthFirst limits with
  | .ok (s, ending, _) =>
    check "session: a run of breadth-first proves syl" (ending == .proved)
    checkEq "session: the proof of the run" (foundText s) "(mpd h1 (a1i h0))"
  | .error msg => check "session: a run of breadth-first proves syl" false msg
  -- a choice, then a run from there
  let s ← startOn "mpd"
  match variantNamed s 0 "ax_mp" with
  | none => check "session: ax_mp is a variant of mpd's root" false
  | some v =>
    match ← s.choose 0 #[v.prop] with
    | .error msg => check "session: a choice, then a run" false msg
    | .ok s =>
      let others := match s.variants 0 with
        | .ok vs => vs.filter fun (o : Variant) => o.prop != v.prop
        | .error _ => #[]
      check "session: the variants not chosen stay leaves"
        (!others.isEmpty && others.all fun o => !o.expanded && s.env.leafs.contains o.prop)
        s!"{rootText s}; leafs {s.env.leafs}"
      match ← s.run breadthFirst limits with
      | .ok (s, ending, _) =>
        check "session: a choice, then a run, proves mpd" (ending == .proved && s.found.isSome)
      | .error msg => check "session: a choice, then a run" false msg
  -- a search stopped at a limit and resumed expands what an uninterrupted one does
  let whole ← search vc (Env.init db index (db.task (id "mpd"))) breadthFirst limits
  let half := whole.env.props.size / 2
  match ← (← startOn "mpd").run breadthFirst { limits with maxProps := half } with
  | .error msg => check "session: a run stopped at a limit" false msg
  | .ok (s, ending, stop) =>
    check "session: the first run stops at the limit of nodes" (ending == .limit && stop == some .nodes)
    match ← s.run breadthFirst limits with
    | .error msg => check "session: the run resumed" false msg
    | .ok (s, ending, _) =>
      check "session: the resumed run proves mpd" (ending == .proved)
      checkEq "session: the same proof as the search without a stop" (foundText s)
        ((whole.proof.map (proofText db)).getD "none")
      checkEq "session: the same tree as the search without a stop" s.env.props.size whole.env.props.size

/-- Forward in a session: facts chosen, and the deductions from them (`Session.deduce`). -/
def sessionForwardTests : TestM Unit := do
  let bytes ← IO.FS.readBinFile logicPath
  let some db := (MmbFile.parse bytes |>.toOption).bind (Db.ofFile · |>.toOption)
    | check "session forward: the fixture becomes a database" false; return
  let id := thmId db
  let wffTy := Ty.mk 0 false
  let c (k : Nat) : Exp := ⟨#[Node.const k wffTy]⟩
  let wi (a b : Exp) : Exp := Exp.mkApp 0 wffTy #[a, b]
  -- ph -> ps, ps -> ch, ps -> th; the goal ph -> th
  let task : Task :=
    { limit := id "a2d", sorts := 1, terms := 2,
      consts := (Array.range 4).map fun _ => { ty := wffTy, names := #[] },
      premises := #[wi (c 0) (c 1), wi (c 1) (c 2), wi (c 1) (c 3)], goal := wi (c 0) (c 3) }
  let s ← Session.start acceptAny (Env.init db db.index task db.hypIndexes) (forward := true) { maxFacts := 64 }
  let factOf (s : Session) (e : Exp) : Nat := (s.facts.find? fun f => s.env.hyps[f]!.expr == e).getD 0
  let proofsOf (s : Session) (fs : Array Nat) : Array String :=
    (fs.map fun f => (s.env.hyps[f]!.factProof.map (proofText db)).getD "?").qsort (· < ·)
  let phps := factOf s (wi (c 0) (c 1))
  let psch := factOf s (wi (c 1) (c 2))
  let psth := factOf s (wi (c 1) (c 3))
  check "session forward: the premises are facts on the front"
    (#[phps, psch, psth].all fun f => s.isFact f && s.front.contains f)
  match ← s.deduce #[0] with
  | .ok _ => check "session forward: the root is not a fact" false
  | .error msg => check "session forward: the root is not a fact" (contains msg "not a fact") msg
  match ← (← startOn db task).deduce #[phps] with
  | .ok _ => check "session forward: no deduction without a forward front" false
  | .error msg => check "session forward: no deduction without a forward front" (contains msg "no forward front") msg
  match ← s.deduce #[phps, psch] with
  | .error msg => check "session forward: deductions from ph -> ps and ps -> ch" false msg
  | .ok (s, made) =>
    check "session forward: from ph -> ps and ps -> ch, ph -> ch, and not ph -> th"
      ((proofsOf s made).contains "(syl h1 h0)" && !(proofsOf s made).contains "(syl h2 h0)")
      s!"{proofsOf s made}"
    check "session forward: the chosen facts stay on the front" (s.front.contains phps && s.front.contains psch)
    checkEq "session forward: the hypotheses of a deduction are not goals" s.openGoals #[0]
    check "session forward: not proved yet" s.found.isNone
    match ← s.deduce #[phps, psth] with
    | .error msg => check "session forward: deductions from ph -> ps and ps -> th" false msg
    | .ok (s, made) =>
      check "session forward: from ph -> ps and ps -> th, ph -> th" ((proofsOf s made).contains "(syl h2 h0)")
        s!"{proofsOf s made}"
      checkEq "session forward: ph -> th is the goal, proved by the join with the root"
        ((s.found.map (proofText db ·.proof)).getD "none") "(syl h2 h0)"
where
  startOn (db : Db) (task : Task) : IO Session := Session.start acceptAny (Env.init db db.index task db.hypIndexes)

end Tests.Prove
