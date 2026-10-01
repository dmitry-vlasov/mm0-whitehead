/-
Tests for the check of a proof file against a specification. The proof file is always
`tests/fixtures/mmb/small.mmb`; the specification is `small.mm0` with one thing changed.
`mm0-rs` has no such check, so these cases are the test of this step, together with the
pairs of the corpus (`Tests/Mm0/Pairs.lean`).
-/
import Whitehead.Mm0.Elab
import Whitehead.Verify.Spec
import Tests.Harness

open Whitehead Whitehead.Mm0 Whitehead.Mmb

namespace Tests.Verify

/-- `small.mm0` with `old` replaced by `new`, checked against `small.mmb`. `expected` is
`none` if the pair must be accepted, or a fragment of the error message. -/
def specCase (name old new : String) (expected : Option String) : TestM Unit := do
  let text ← IO.FS.readFile "tests/fixtures/mmb/small.mm0"
  if !old.isEmpty && !contains text old then
    check name false s!"test bug: the specification does not contain `{old}`"
    return
  let text := if old.isEmpty then text ++ new else text.replace old new
  match elabString text with
  | .error e => check name false s!"the changed specification does not elaborate: byte {e.pos}: {e.msg}"
  | .ok env =>
    match MmbFile.parse (← IO.FS.readBinFile "tests/fixtures/mmb/small.mmb") with
    | .error e => check name false e.msg
    | .ok f =>
      match Verify.matchSpec env f, expected with
      | .ok _, none => check name true
      | .ok _, some part => check name false s!"accepted; expected an error containing \"{part}\""
      | .error e, none => check name false (e.format f "small.mmb")
      | .error e, some part => check name (contains (e.format f "small.mmb") part) (e.format f "small.mmb")

def specTests : TestM Unit := do
  specCase "spec: the specification of the file" "" "" none
  -- what may differ
  specCase "spec: a def may be declared without its value"
    "def dbl (a: wff): wff = $ imp a a $;" "def dbl (a: wff): wff;" none
  specCase "spec: names of variables and hypotheses do not matter"
    "theorem t2 (a b: wff) (h1: $ a $) (h2: $ imp a b $): $ b $;"
    "theorem t2 (p q: wff): $ p $ > $ imp p q $ > $ q $;" none
  specCase "spec: names of declarations are not compared (the index is not part of the proof)"
    "theorem t (a: wff): $ dbl a $;" "theorem renamed (a: wff): $ dbl a $;" none
  -- what may not
  specCase "spec: sort modifiers" "provable sort wff;" "strict provable sort wff;"
    (some "sort wff: different modifiers")
  specCase "spec: dependencies of a binder" "term al {x: set} (ph: wff x): wff;"
    "term al {x: set} (ph: wff): wff;" (some "term al: argument 1 differs in its dependencies")
  specCase "spec: kind of a binder" "def allself (ph: wff) {.y: set}: wff = $ al y ph $;"
    "def allself (ph: wff) {y: set}: wff = $ al y ph $;" (some "def allself")
  specCase "spec: value of a def" "def dbl (a: wff): wff = $ imp a a $;"
    "def dbl (a: wff): wff = $ imp a (imp a a) $;" (some "term dbl: value")
  specCase "spec: a term where the proof file has a def" "def dbl (a: wff): wff = $ imp a a $;"
    "term dbl (a: wff): wff;" (some "a def on one side")
  specCase "spec: conclusion of a theorem" "theorem t (a: wff): $ dbl a $;"
    "theorem t (a: wff): $ imp a a $;" (some "theorem t: conclusion")
  specCase "spec: conclusion of an axiom" "axiom ax1 (a: wff): $ imp a a $;"
    "axiom ax1 (a: wff): $ dbl a $;" (some "axiom ax1: conclusion")
  specCase "spec: order of hypotheses"
    "theorem t2 (a b: wff) (h1: $ a $) (h2: $ imp a b $): $ b $;"
    "theorem t2 (a b: wff) (h1: $ imp a b $) (h2: $ a $): $ b $;" (some "theorem t2: hypothesis")
  specCase "spec: number of hypotheses"
    "theorem t2 (a b: wff) (h1: $ a $) (h2: $ imp a b $): $ b $;"
    "theorem t2 (a b: wff) (h1: $ a $): $ b $;" (some "1 hypotheses in the .mm0, 2 in the .mmb")
  specCase "spec: a theorem where the proof file has an axiom" "axiom ax1 (a: wff): $ imp a a $;"
    "theorem ax1 (a: wff): $ imp a a $;" (some "an axiom on one side")
  specCase "spec: an axiom where the proof file has a theorem" "theorem t (a: wff): $ dbl a $;"
    "axiom t (a: wff): $ dbl a $;" (some "an axiom on one side")
  specCase "spec: a statement the proof file does not have" ""
    "theorem t3 (a: wff): $ imp a a $;\n" (some "declares only 10 of them; the next one is theorem t3")
  specCase "spec: a statement the specification does not have"
    "theorem t2 (a b: wff) (h1: $ a $) (h2: $ imp a b $): $ b $;" "" (some "no statement for this one")
  specCase "spec: statements in a different order"
    "sort set;\nterm imp (a b: wff): wff;" "term imp (a b: wff): wff;\nsort set;"
    (some "the .mm0 declares term imp here")

end Tests.Verify
