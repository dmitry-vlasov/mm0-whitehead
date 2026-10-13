/-
Tests of `unifySubsProd` and `unifyIndexes` (`Whitehead/Prove/Prod.lean`): hand-written
cases, and random sets of substitutions on which the result is compared with trying
every tuple.
-/
import Whitehead.Prove.Prod
import Tests.Prove.Util

open Whitehead.Prove

namespace Tests.Prove

/-- The tuples that unify, by trying each: the reference for `unifySubsProd`. -/
def unifyingTuples (sets : Array (Array Subst)) : Array (Array Nat) :=
  (tuples (sets.map fun set => Array.range set.size)).filter fun picks =>
    (unifySubs ((Array.range sets.size).map fun i => sets[i]![picks[i]!]!)).isSome

def lessTuple (a b : Array Nat) : Bool := Id.run do
  for i in [0:min a.size b.size] do
    if a[i]! != b[i]! then return a[i]! < b[i]!
  return a.size < b.size

def prodTests : TestM Unit := do
  -- the tuples one at a time: the order of `tuples`, `cap + 1` of them at most
  let small : Array (Array Nat) := #[#[1, 2, 3], #[4, 5]]
  checkEq "tuples up to: all, in the order of `tuples`" (tuplesUpTo small 100) (tuples small)
  checkEq "tuples up to: the first cap + 1" (tuplesUpTo small 3) ((tuples small).extract 0 4)
  checkEq "tuples up to: one with a cap of 0" (tuplesUpTo small 0) #[#[1, 4]]
  checkEq "tuples up to: none when a set is empty" (tuplesUpTo #[#[1], (#[] : Array Nat)] 5) #[]
  checkEq "tuples up to: the empty tuple of no sets" (tuplesUpTo (#[] : Array (Array Nat)) 5) #[#[]]
  let big : Array (Array Nat) := #[Array.range 100, Array.range 100, Array.range 100]
  checkEq "tuples up to: a quarter of a million of a million" (tuplesUpTo big 250000).size 250001
  checkEq "tuples up to: the last of them" (tuplesUpTo big 250000).back! #[25, 0, 0]
  let g := sig
  -- several indexes at once
  let index (keys : List String) : Index Nat :=
    (keys.zipIdx).foldl (init := {}) fun ix (k, i) => ix.insert (g.exp k) i
  let together (rows : List (List String)) : List String :=
    ((unifyIndexes (rows.map index).toArray).map fun (s, e, data) =>
      s!"{g.showExp e} {data} [{g.showSub s}]").qsort (· < ·) |>.toList
  checkEq "indexes: equal expressions" (together [["(wn ph)"], ["(wn ph)"]]) ["(wn ph) #[#[0], #[0]] []"]
  checkEq "indexes: different terms" (together [["(wn ph)"], ["(wi ph ph)"]]) []
  checkEq "indexes: a variable against an application"
    (together [["a"], ["(wn ph)"]]) ["(wn ph) #[#[0], #[0]] [a := (wn ph)]"]
  checkEq "indexes: variables inside, both ways"
    (together [["(wi a ph)"], ["(wi ps p)"]]) ["(wi ps ph) #[#[0], #[0]] [a := ps, p := ph]"]
  checkEq "indexes: every choice from each index that unifies"
    (together [["(wn ph)", "(wn ps)", "ph"], ["(wn a)", "ps"]])
    ["(wn ph) #[#[0], #[0]] [a := ph]", "(wn ps) #[#[1], #[0]] [a := ps]"]
  checkEq "indexes: one expression stored for two"
    (together [["(wn ph)"], ["a"]]).length 1
  checkEq "indexes: three indexes"
    (together [["(wi a b)"], ["(wi (wn p) q)"], ["(wi r (wn ph))"]])
    ["(wi (wn p) (wn ph)) #[#[0], #[0], #[0]] [a := (wn p), b := (wn ph), q := (wn ph), r := (wn p)]"]
  -- sets of substitutions
  let prod (sets : List (List (List (String × String)))) : List (List Nat) :=
    ((unifySubsProd (sets.map fun set => (set.map g.sub).toArray).toArray).map (·.2.toList)).qsort
      (fun a b => lessTuple a.toArray b.toArray) |>.toList
  checkEq "prod: the tuples that agree on a variable"
    (prod [[[("a", "ph")], [("a", "ps")]], [[("a", "ps")], [("a", "ph")], [("b", "ph")]]])
    [[0, 1], [0, 2], [1, 0], [1, 2]]
  checkEq "prod: nothing in common: every tuple"
    (prod [[[("a", "ph")], [("a", "ps")]], [[("b", "ph")]]]) [[0, 0], [1, 0]]
  checkEq "prod: an empty set" (prod [[[("a", "ph")]], []]) []
  checkEq "prod: a variable bound in one set and used in the other"
    (prod [[[("a", "(wn b)")]], [[("b", "ph")], [("a", "(wn ps)")], [("a", "(wi ps ps)")]]]) [[0, 0], [0, 1]]
  -- against trying every tuple, on random sets: the variables a b x A u are bound, the
  -- others occur in the images
  let bound := #["a", "b", "x", "A", "u"]
  let mut rng : Rng := ⟨424242⟩
  let mut failures := 0
  let mut found := 0
  let mut total := 0
  let rounds := 1500
  for _ in [0:rounds] do
    let (nSets, r) := rng.below 2
    rng := r
    let mut sets : Array (Array Subst) := #[]
    for _ in [0:nSets + 2] do
      let (n, r) := rng.below 5
      rng := r
      let mut set : Array Subst := #[]
      for _ in [0:n + 1] do
        let mut s : Subst := {}
        for vname in bound do
          let (take, r) := rng.below 3
          rng := r
          if take == 0 then
            let v := g.var vname
            let (e, r) := genExp g (Node.ty v) 2 0 g.vars.size true rng
            rng := r
            if e.nodes.all fun n => !Node.isVar n || !bound.contains (g.varName (Node.varId n)) then
              s := { map := s.map.insert (Node.varId v) (SubExp.mk' v e) }
        set := set.push s
      sets := sets.push set
    let expected := (unifyingTuples sets).qsort lessTuple
    let results := unifySubsProd sets
    let got := (results.map (·.2)).qsort lessTuple
    total := total + (tuples (sets.map fun set => Array.range set.size)).size
    found := found + expected.size
    let mut why := ""
    if got != expected then why := s!"tuples {got}, expected {expected}"
    else
      -- the substitution returned with a tuple unifies its substitutions
      for (s, picks) in results do
        match ({} : Subst).compose s with
        | none => why := "the unifier of a tuple contradicts itself"
        | some u =>
          for i in [0:sets.size] do
            for (_, x) in sets[i]![picks[i]!]!.map do
              if u.apply (Exp.ofVar x.var) != u.apply x.exp then
                why := s!"tuple {picks}: {g.showSub u} does not agree with {g.varName (Node.varId x.var)} := {g.showExp x.exp}"
    if !why.isEmpty then
      failures := failures + 1
      if failures ≤ 5 then check s!"prod: random sets {sets.map (·.map g.showSub)}" false why
  check s!"prod: {rounds} random products agree with trying every tuple" (failures == 0) s!"{failures} differences"
  -- the same where an image may contain a variable that another substitution binds, so
  -- that unifiers come out in chains (Russell 4f1d5f09: `ch => ps, ps => ph` folded
  -- through ruUnifySubs lost a binding). Each substitution stays idempotent itself.
  let mut chainFailures := 0
  let mut chainFound := 0
  for _ in [0:rounds] do
    let (nSets, r) := rng.below 2
    rng := r
    let mut sets : Array (Array Subst) := #[]
    for _ in [0:nSets + 2] do
      let (n, r) := rng.below 5
      rng := r
      let mut set : Array Subst := #[]
      for _ in [0:n + 1] do
        let mut s : Subst := {}
        for vname in bound do
          let (take, r) := rng.below 3
          rng := r
          if take == 0 then
            let v := g.var vname
            let (e, r) := genExp g (Node.ty v) 2 0 g.vars.size true rng
            rng := r
            -- not the variable itself, and nothing that this substitution binds
            if !e.hasVar (Node.varId v) && e.nodes.all fun n => !Node.isVar n || !s.map.contains (Node.varId n) then
              if !s.map.toArray.any fun (_, x) => x.exp.hasVar (Node.varId v) then
                s := { map := s.map.insert (Node.varId v) (SubExp.mk' v e) }
        set := set.push s
      sets := sets.push set
    let expected := (unifyingTuples sets).qsort lessTuple
    let results := unifySubsProd sets
    let got := (results.map (·.2)).qsort lessTuple
    chainFound := chainFound + expected.size
    let mut why := ""
    if got != expected then why := s!"tuples {got}, expected {expected}"
    else
      for (s, picks) in results do
        -- resolved to a fixed point, the unifier must give every variable of every
        -- substitution of the tuple one value
        let resolve (e : Exp) : Exp := Id.run do
          let mut e := e
          for _ in [0:20] do e := s.apply e
          return e
        for i in [0:sets.size] do
          for (_, x) in sets[i]![picks[i]!]!.map do
            if resolve (Exp.ofVar x.var) != resolve x.exp then
              why := s!"tuple {picks}: {g.showSub s} does not agree with {g.varName (Node.varId x.var)} := {g.showExp x.exp}"
    if !why.isEmpty then
      chainFailures := chainFailures + 1
      if chainFailures ≤ 5 then check s!"prod chains: random sets {sets.map (·.map g.showSub)}" false why
  check s!"prod: {rounds} random products with chained substitutions agree with trying every tuple"
    (chainFailures == 0) s!"{chainFailures} differences, {chainFound} tuples unify"
  check "prod: the random products have tuples that unify and tuples that do not"
    (found > total / 20 && found < total * 19 / 20) s!"{found} of {total} tuples unify"

end Tests.Prove
