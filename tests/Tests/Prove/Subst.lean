/-
Tests of expressions and substitutions (`Whitehead/Prove/Exp.lean`, `Subst.lean`), on
the small language of `Tests/Prove/Util.lean`.
-/
import Tests.Prove.Util

open Whitehead.Prove

namespace Tests.Prove

def substTests : TestM Unit := do
  let g := sig
  -- expressions
  let e := g.exp "(wi (wn a) (wal x (wi a b)))"
  checkEq "exp: nodes in prefix order" e.size 8
  checkEq "exp: length of the arguments" (Node.len e.nodes[0]!) 7
  checkEq "exp: a subexpression is a slice" (g.showExp (e.sub 3)) "(wal x (wi a b))"
  checkEq "exp: round trip" (g.showExp e) "(wi (wn a) (wal x (wi a b)))"
  checkEq "exp: variables, each once" (e.vars.map (g.varName ∘ Node.varId)) #["a", "x", "b"]
  check "exp: well formed" e.wellFormed
  check "exp: a wrong length is not well formed" (!(Exp.mk (e.nodes.set! 0 (Node.setLen e.nodes[0]! 5))).wellFormed)
  checkEq "exp: a constant" (g.showExp (g.exp "(wi ph X)")) "(wi ph X)"
  check "exp: a constant is not a variable" (!(g.exp "ph").isVar && Node.isConst (g.exp "ph").nodes[0]!)
  -- types
  check "type: a regular variable takes a name" (Ty.fits setvar name)
  check "type: a name does not take a regular expression" (!Ty.fits name setvar)
  check "type: sorts do not mix" (!Ty.fits wff cls && !Ty.fits cls name)
  -- application
  let s := g.sub [("a", "(wi b c)")]
  let applied := s.apply (g.exp "(wn (wi a a))")
  checkEq "apply: images are put in" (g.showExp applied) "(wn (wi (wi b c) (wi b c)))"
  check "apply: lengths are set again" applied.wellFormed
  checkEq "apply: nested applications close together"
    (g.showExp (s.apply (g.exp "(wi b (wn (wn a)))"))) "(wi b (wn (wn (wi b c))))"
  check "apply: nested lengths" (s.apply (g.exp "(wi b (wn (wn a)))")).wellFormed
  check "apply: an expression without bound variables is returned as it is"
    (s.apply (g.exp "(wn b)") == g.exp "(wn b)")
  -- add
  let none' : Option Subst := none
  checkEq "add: a first binding" (g.showOpt ((Subst.mk {}).add (g.var "a") (g.exp "(wn b)"))) "a := (wn b)"
  checkEq "add: occurs check" (g.showOpt (({} : Subst).add (g.var "a") (g.exp "(wn a)"))) (g.showOpt none')
  checkEq "add: a variable to itself changes nothing"
    (g.showOpt (s.add (g.var "b") (g.exp "b"))) "a := (wi b c)"
  checkEq "add: the new variable is replaced in the old images"
    (g.showOpt (s.add (g.var "b") (g.exp "(wn d)"))) "a := (wi (wn d) c), b := (wn d)"
  checkEq "add: the new image is brought under the substitution"
    (g.showOpt (s.add (g.var "d") (g.exp "(wn a)"))) "a := (wi b c), d := (wn (wi b c))"
  checkEq "add: the same binding again" (g.showOpt (s.add (g.var "a") (g.exp "(wi b c)"))) "a := (wi b c)"
  checkEq "add: another binding of a bound variable" (g.showOpt (s.add (g.var "a") (g.exp "(wn b)"))) "none"
  checkEq "add: a cycle through an old image" (g.showOpt (s.add (g.var "b") (g.exp "(wn a)"))) "none"
  -- add with types
  checkEq "add1: a name to a name constant" (g.showOpt (({} : Subst).add1 (g.var "x") (g.exp "X"))) "x := X"
  checkEq "add1: a name to a regular constant of its sort" (g.showOpt (({} : Subst).add1 (g.var "x") (g.exp "U"))) "none"
  checkEq "add1: a regular variable to a name" (g.showOpt (({} : Subst).add1 (g.var "u") (g.exp "x"))) "u := x"
  checkEq "add1: a name to a regular variable" (g.showOpt (({} : Subst).add1 (g.var "x") (g.exp "u"))) "none"
  checkEq "add1: another sort" (g.showOpt (({} : Subst).add1 (g.var "A") (g.exp "x"))) "none"
  -- composition
  let s1 := g.sub [("a", "(wn b)")]
  let s2 := g.sub [("b", "c")]
  checkEq "compose: first one, then the other" (g.showOpt (s1.compose s2)) "a := (wn c), b := c"
  checkEq "compose: in the other order too, no image keeps a bound variable" (g.showOpt (s2.compose s1)) "a := (wn c), b := c"
  checkEq "compose: a contradiction"
    (g.showOpt ((g.sub [("a", "b")]).compose (g.sub [("b", "(wn a)")]))) "none"
  checkEq "unsafeCompose" (g.showSub (s1.unsafeCompose s2)) "a := (wn c), b := c"
  checkEq "unsafeCompose: the first wins on a common variable"
    (g.showSub ((g.sub [("a", "b")]).unsafeCompose (g.sub [("a", "c"), ("d", "c")]))) "a := b, d := c"
  -- merge
  checkEq "merge: disjoint" (g.showOpt (s1.merge s2)) "a := (wn b), b := c"
  checkEq "merge: agreeing" (g.showOpt (s1.merge s1)) "a := (wn b)"
  checkEq "merge: conflicting" (g.showOpt (s1.merge (g.sub [("a", "(wn c)")]))) "none"
  -- matching
  checkEq "match: the variables of the pattern are bound"
    (g.showOpt (matchExp (g.exp "(wi (wn ph) (wn ph))") (g.exp "(wi a a)"))) "a := (wn ph)"
  checkEq "match: one variable, two different subexpressions"
    (g.showOpt (matchExp (g.exp "(wi (wn ph) ps)") (g.exp "(wi a a)"))) "none"
  checkEq "match: the variables of the other side are not bound"
    (g.showOpt (matchExp (g.exp "(wi a b)") (g.exp "(wi (wn c) c)"))) "none"
  checkEq "match: a variable of the other side is an expression like any"
    (g.showOpt (matchExp (g.exp "(wi b b)") (g.exp "(wi a a)"))) "a := b"
  checkEq "match: a name is not matched by a regular constant"
    (g.showOpt (matchExp (g.exp "(cv U)") (g.exp "(cv x)"))) "none"
  checkEq "match: a name is matched by a name"
    (g.showOpt (matchExp (g.exp "(wal X ph)") (g.exp "(wal x a)"))) "a := ph, x := X"
  -- fresh variables, filtering
  let fresh := Subst.fresher #[g.var "a", g.var "x"] fun v => Node.var (Node.varId v + 100) (Node.ty v)
  checkEq "fresher: every variable to its new one" (g.showSub fresh) "a := v100, x := v104"
  check "fresher: the new variable has the type of the old"
    (((fresh.lookup (g.var "x")).map (·.ty)) == some name)
  checkEq "filter" (g.showSub ((g.sub [("a", "b"), ("x", "y")]).filter fun v _ => Node.ty v == name)) "x := y"
  -- splitting
  let split := splitSubs #[g.sub [("a", "(wn b)"), ("d", "c")], g.sub [("b", "ph")]]
  checkEq "split: a variable that only one substitution mentions is set apart"
    (g.showSub split.indep) "a := (wn b), d := c"
  checkEq "split: the others stay" (split.depend.map g.showSub) #["", "b := ph"]

end Tests.Prove
