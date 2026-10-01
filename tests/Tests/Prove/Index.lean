/-
Tests of the index (`Whitehead/Prove/Index.lean`): hand-written cases, and random
expressions on which a lookup in the index is compared with unifying the given
expression with every stored one in turn.
-/
import Whitehead.Prove.Index
import Tests.Prove.Util

open Whitehead.Prove

namespace Tests.Prove

/-- The stored expressions that unify with `q`, as text, sorted. -/
def found (g : Sig) (ix : Index String) (q : String) : List String :=
  ((ix.unify (g.exp q)).map (·.data)).qsort (· < ·) |>.toList

def indexTests : TestM Unit := do
  let g := sig
  let keys := ["(wi a (wi b a))", "(wi (wn a) (wi a b))", "(wi a a)", "(wn (wn a))", "a",
               "(wal x (wi a b))", "(wceq A A)", "(wceq (cv x) B)", "wtru", "(wi ph a)"]
  let ix : Index String := keys.foldl (init := {}) fun ix k => ix.insert (g.exp k) k
  checkEq "index: the number of expressions" ix.size keys.length
  checkEq "index: a closed expression finds itself and the variables"
    (found g ix "wtru") ["a", "wtru"]
  checkEq "index: an application follows its term and the variables"
    (found g ix "(wi ps ps)") ["(wi a a)", "a"]
  checkEq "index: a variable met twice in a stored expression"
    (found g ix "(wi ps (wi ph ps))") ["(wi a (wi b a))", "a"]
  checkEq "index: a constant in a stored expression"
    (found g ix "(wi ph ps)") ["(wi ph a)", "a"]
  checkEq "index: a variable of the given expression takes every stored subexpression"
    (found g ix "(wi p ps)") ["(wi a a)", "(wi ph a)", "a"]
  checkEq "index: a variable alone finds everything of its sort"
    (found g ix "p") ["(wal x (wi a b))", "(wceq (cv x) B)", "(wceq A A)", "(wi (wn a) (wi a b))",
                       "(wi a (wi b a))", "(wi a a)", "(wi ph a)", "(wn (wn a))", "a", "wtru"]
  checkEq "index: a variable of the given expression met twice"
    (found g ix "(wi p p)") ["(wi a a)", "(wi ph a)", "a"]
  checkEq "index: variables on both sides"
    (found g ix "(wi (wn p) q)") ["(wi (wn a) (wi a b))", "(wi a (wi b a))", "(wi a a)", "a"]
  checkEq "index: a name constant for a stored name"
    (found g ix "(wal X ph)") ["a"]
  checkEq "index: a name constant for a stored name, the body fitting"
    (found g ix "(wal X (wi ph ps))") ["(wal x (wi a b))", "a"]
  checkEq "index: a regular constant where a name is stored"
    (found g ix "(wceq (cv U) C)") ["a"]
  checkEq "index: a name where a name is stored"
    (found g ix "(wceq (cv Y) C)") ["(wceq (cv x) B)", "a"]
  checkEq "index: a regular variable where a name is stored is bound to the name"
    ((ix.unify (g.exp "(wceq (cv u') C)")).filterMap fun u =>
      if u.data == "a" then none else some (g.showSub u.sub)) #["B := C, u' := x"]
  checkEq "index: the unifier of a result"
    ((ix.unify (g.exp "(wi (wn ph) q)")).filterMap fun u =>
      if u.data == "(wi (wn a) (wi a b))" then some (g.showSub u.sub) else none) #["a := ph, q := (wi ph b)"]
  checkEq "index: the given expression under the unifier"
    ((ix.unify (g.exp "(wi (wn ph) q)")).filterMap fun u =>
      if u.data == "(wi (wn a) (wi a b))" then some (g.showExp u.expr) else none) #["(wi (wn ph) (wi ph b))"]
  checkEq "index: under a substitution given in advance"
    (((ix.unify (g.exp "(wi p q)") (g.sub [("p", "(wn ps)")])).map (·.data)).qsort (· < ·)).toList
    ["(wi (wn a) (wi a b))", "(wi a (wi b a))", "(wi a a)", "a"]
  -- two expressions under one key
  let ix2 := (ix.insert (g.exp "(wi a a)") "again")
  checkEq "index: two data under one expression" (found g ix2 "(wi ps ps)") ["(wi a a)", "a", "again"]
  -- subexpressions are put together again from the trie
  let mut bad := 0
  for first in [1:ix.nodes.size] do
    for last in ix.nodes[first]!.ends do
      if !(ix.subexpr first last).wellFormed then bad := bad + 1
  check "index: every subexpression read back from the trie is well formed" (bad == 0) s!"{bad} are not"
  -- against unification one by one, on random expressions: the stored ones over the
  -- first set of variables, the given ones over the second
  let mut rng : Rng := ⟨77⟩
  let mut stored : Array Exp := #[]
  let mut big : Index Nat := {}
  for k in [0:400] do
    let (tyPick, r) := rng.below 4
    let (e, r) := genExp g (#[wff, wff, wff, cls][tyPick]!) 3 0 secondVars true r
    rng := r
    stored := stored.push e
    big := big.insert e k
  let mut failures := 0
  let mut hits := 0
  let rounds := 2000
  for _ in [0:rounds] do
    let (tyPick, r) := rng.below 4
    let (q, r) := genExp g (#[wff, wff, wff, cls][tyPick]!) 3 secondVars g.vars.size true r
    rng := r
    let results := big.unify q
    let expected := (Array.range stored.size).filter fun k => (unifyExps #[q, stored[k]!] {}).isSome
    hits := hits + expected.size
    let got := (results.map (·.data)).qsort (· < ·)
    let mut why := ""
    if got != expected then why := s!"found {got}, expected {expected}"
    else
      for u in results do
        let key := stored[u.data]!
        if u.sub.apply q != u.sub.apply key then why := s!"the unifier does not make #{u.data} equal"
        else if u.expr != u.sub.apply q then why := "the instance is not the given expression under the unifier"
        else if !u.expr.wellFormed then why := "the instance is not well formed"
        else
          match unifyExps #[q, key] {} with
          | some s =>
            if shape (Tree.ofExp (s.apply q)) != shape (Tree.ofExp u.expr) then
              why := s!"not the most general unifier for #{u.data}"
          | none => why := "unreachable"
    if !why.isEmpty then
      failures := failures + 1
      if failures ≤ 5 then check s!"index: random lookup of {g.showExp q}" false why
  check s!"index: {rounds} random lookups among 400 expressions agree with unification one by one"
    (failures == 0) s!"{failures} differences"
  check "index: the random lookups find something" (hits > rounds) s!"{hits} hits"

end Tests.Prove
