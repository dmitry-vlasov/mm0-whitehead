/-
Tests of unification (`Whitehead/Prove/Unify.lean`): hand-written cases, and random
expressions on which the port is compared with the reference unifier of
`Tests/Prove/Util.lean`.
-/
import Tests.Prove.Util

open Whitehead.Prove

namespace Tests.Prove

/-- `unifyExps` on expressions written as text, the result as text. -/
def unified (g : Sig) (es : List String) : String :=
  g.showOpt (unifyExps (es.map g.exp).toArray {})

/-- One random comparison: the two unifiers agree on whether `e1` and `e2` unify; the
port's result makes them equal, is not changed by applying itself again, and gives an
instance of the same shape as the reference. -/
def compareOnce (g : Sig) (e1 e2 : Exp) : Option String :=
  let reference := naiveUnify [] (Tree.ofExp e1) (Tree.ofExp e2)
  match unifyExps #[e1, e2] {}, reference with
  | none, none => none
  | some _, none => some "the port unifies, the reference does not"
  | none, some _ => some "the reference unifies, the port does not"
  | some s, some b =>
    let i1 := s.apply e1
    let i2 := s.apply e2
    if i1 != i2 then some s!"the instances differ: {g.showExp i1} and {g.showExp i2}"
    else if !i1.wellFormed then some "the instance is not well formed"
    else if s.apply i1 != i1 then some "the substitution is not idempotent"
    else if shape (Tree.ofExp i1) != shape (resolve b (Tree.ofExp e1)) then
      some s!"not the most general: {g.showExp i1}"
    else none

def unifyTests : TestM Unit := do
  let g := sig
  checkEq "unify: variables on both sides" (unified g ["(wi a b)", "(wi (wn c) c)"]) "a := (wn c), b := c"
  checkEq "unify: one expression" (unified g ["(wi a b)"]) ""
  checkEq "unify: equal expressions" (unified g ["(wi a ph)", "(wi a ph)"]) ""
  checkEq "unify: different terms" (unified g ["(wi a b)", "(wn c)"]) "none"
  checkEq "unify: different constants" (unified g ["ph", "ps"]) "none"
  checkEq "unify: a constant for a variable" (unified g ["(wi a a)", "(wi ph b)"]) "a := ph, b := ph"
  checkEq "unify: occurs check" (unified g ["(wi a a)", "(wi b (wn b))"]) "none"
  checkEq "unify: a variable met twice" (unified g ["(wi a a)", "(wi (wn b) (wn ph))"]) "a := (wn ph), b := ph"
  checkEq "unify: a variable met twice, no solution" (unified g ["(wi a a)", "(wi ph ps)"]) "none"
  checkEq "unify: three expressions"
    (unified g ["(wi a b)", "(wi (wn c) d)", "(wi (wn ph) (wn c))"]) "a := (wn ph), b := (wn ph), c := ph, d := (wn ph)"
  checkEq "unify: three expressions, no solution"
    (unified g ["(wi a b)", "(wi (wn c) c)", "(wi ph ph)"]) "none"
  checkEq "unify: a chain of variables" (unified g ["(wi a (wi b c))", "(wi b (wi c ph))"]) "a := ph, b := ph, c := ph"
  -- under a substitution
  checkEq "unify: under a substitution that already binds"
    (g.showOpt (unifyExps #[g.exp "a", g.exp "(wn b)"] (g.sub [("a", "(wn ph)")]))) "a := (wn ph), b := ph"
  checkEq "unify: under a substitution that contradicts"
    (g.showOpt (unifyExps #[g.exp "a", g.exp "(wi b b)"] (g.sub [("a", "(wn ph)")]))) "none"
  -- names
  checkEq "unify: two names" (unified g ["(wal x a)", "(wal y b)"]) "a := b, x := y"
  checkEq "unify: a name and a name constant" (unified g ["(wal x a)", "(wal X ph)"]) "a := ph, x := X"
  checkEq "unify: a regular variable and a name: the regular one is bound"
    (unified g ["(cv u)", "(cv x)"]) "u := x"
  checkEq "unify: the same, the other way round" (unified g ["(cv x)", "(cv u)"]) "u := x"
  checkEq "unify: a regular variable and a regular constant" (unified g ["(cv u)", "(cv U)"]) "u := U"
  checkEq "unify: a name and a regular constant of its sort" (unified g ["(cv x)", "(cv U)"]) "none"
  checkEq "unify: name, regular variable, name constant"
    (unified g ["(cv u)", "(cv x)", "(cv X)"]) "u := X, x := X"
  -- substitutions
  let showSubs (subs : List (List (String × String))) : String :=
    match unifySubs (subs.map g.sub).toArray with
    | some s => g.showOpt (({} : Subst).compose s)
    | none => "none"
  checkEq "unifySubs: one variable, two images"
    (showSubs [[("a", "(wn b)")], [("a", "(wn ph)")]]) "a := (wn ph), b := ph"
  checkEq "unifySubs: images that do not unify" (showSubs [[("a", "(wn b)")], [("a", "(wi b b)")]]) "none"
  checkEq "unifySubs: nothing in common" (showSubs [[("a", "(wn b)")], [("c", "ph")]]) "a := (wn b), c := ph"
  checkEq "unifySubs: a variable bound in one, used in the other"
    (showSubs [[("a", "(wn b)")], [("b", "ph")]]) "a := (wn ph), b := ph"
  checkEq "unifySubs: a conflict through two variables"
    (showSubs [[("a", "b"), ("c", "ph")], [("a", "c"), ("b", "ps")]]) "none"
  checkEq "unifySubs: three substitutions"
    (showSubs [[("a", "(wi b c)")], [("a", "(wi ph d)")], [("d", "(wn b)")]])
    "a := (wi ph (wn ph)), b := ph, c := (wn ph), d := (wn ph)"
  -- against the reference, on random expressions
  let mut rng : Rng := ⟨20261001⟩
  let mut failures := 0
  let mut solved := 0
  let rounds := 20000
  for _ in [0:rounds] do
    let (tyPick, r) := rng.below 4
    let ty := #[wff, wff, cls, setvar][tyPick]!
    let (e1, r) := genExp g ty 3 0 g.vars.size true r
    let (e2, r) := genExp g ty 3 0 g.vars.size true r
    rng := r
    if (unifyExps #[e1, e2] {}).isSome then solved := solved + 1
    if let some why := compareOnce g e1 e2 then
      failures := failures + 1
      if failures ≤ 5 then
        check s!"unify: random pair {g.showExp e1} and {g.showExp e2}" false why
  check s!"unify: {rounds} random pairs agree with the reference unifier" (failures == 0) s!"{failures} differences"
  check "unify: the random pairs have both outcomes" (solved > rounds / 20 && solved < rounds * 19 / 20) s!"{solved} of {rounds} unify"
  -- substitutions, on random bindings: variables a b x A u are bound, the others occur in
  -- the images
  let bound := #["a", "b", "x", "A", "u"]
  let mut subFailures := 0
  let mut subSolved := 0
  let subRounds := 5000
  for _ in [0:subRounds] do
    let mut subs : Array Subst := #[]
    let mut eqs : Array (Exp × Exp) := #[]
    let (count, r) := rng.below 3
    rng := r
    for _ in [0:count + 2] do
      let mut s : Subst := {}
      for vname in bound do
        let (take, r) := rng.below 2
        rng := r
        if take == 0 then
          let v := g.var vname
          -- images over the variables that are never bound: numbers 2, 3, 5, 6, 8, 10
          let (e, r) := genExp g (Node.ty v) 2 0 g.vars.size true rng
          rng := r
          if e.nodes.all fun n => !Node.isVar n || !bound.contains (g.varName (Node.varId n)) then
            s := { map := s.map.insert (Node.varId v) (SubExp.mk' v e) }
            eqs := eqs.push (Exp.ofVar v, e)
      subs := subs.push s
    -- the reference: all equations `v = image` solved together
    let reference := eqs.foldl (init := some []) fun b (l, r) =>
      b.bind fun b => naiveUnify b (Tree.ofExp l) (Tree.ofExp r)
    let ours := (unifySubs subs).bind fun s => ({} : Subst).compose s
    match ours, reference with
    | none, none => pure ()
    | some s, some _ =>
      subSolved := subSolved + 1
      for (l, r) in eqs do
        if s.apply l != s.apply r || s.apply (s.apply r) != s.apply r then
          subFailures := subFailures + 1
          if subFailures ≤ 5 then
            check s!"unifySubs: random {subs.map g.showSub}" false s!"{g.showSub s} does not solve {g.showExp l} = {g.showExp r}"
    | some _, none | none, some _ =>
      subFailures := subFailures + 1
      if subFailures ≤ 5 then
        check s!"unifySubs: random {subs.map g.showSub}" false
          s!"port: {g.showOpt ours}; the reference {if reference.isSome then "has" else "has no"} solution"
  check s!"unifySubs: {subRounds} random sets of substitutions agree with the reference" (subFailures == 0)
    s!"{subFailures} differences"
  check "unifySubs: the random sets have both outcomes" (subSolved > subRounds / 20 && subSolved < subRounds * 19 / 20)
    s!"{subSolved} of {subRounds} unify"

end Tests.Prove
