/-
Tests for the secondary parser (math strings) and the elaborator, on hand-written
specifications. Formulas are compared as s-expressions.
-/
import Whitehead.Mm0.Elab
import Tests.Harness

open Whitehead.Mm0

namespace Tests.Mm0

/-- A small propositional and predicate signature used by most tests. -/
def logic : String :=
  "delimiter $ ( ~ $ $ ) $;
strict provable sort wff;
term imp (a b: wff): wff; infixr imp: $->$ prec 25;
term not (a: wff): wff; prefix not: $~$ prec 41;
term and (a b: wff): wff; infixl and: $/\\$ prec 34;
term or (a b: wff): wff; infixl or: $\\/$ prec 30;
term iff (a b: wff): wff; infixl iff: $<->$ prec 20;
term top: wff; prefix top: $T.$ prec max;
sort set;
term all {x: set} (ph: wff x): wff; prefix all: $A.$ prec 41;
term eq (a b: set): wff; infixl eq: $=$ prec 50;
sort class;
term cv (x: set): class; coercion cv: set > class;
term el (a b: class): wff; infixl el: $e.$ prec 50;
term ab {x: set} (ph: wff x): class;
notation ab {x: set} (ph: wff x): class = (${$: max) x ($|$: 0) ph ($}$: 0);
"

/-- The conclusion of the last axiom or theorem of `src`, as an s-expression. -/
def lastFormula (src : String) : Except ParseError String := do
  let env ← elabString src
  match env.thms.back? with
  | some t => return env.exprString (t.args.map (·.name.getD "_")) t.concl
  | none => throw ⟨0, "test bug: no axiom or theorem"⟩

/-- `axiom t <binders>: $ <formula> $;` on top of `logic` elaborates to `expected`. -/
def parsesTo (name binders formula expected : String) : TestM Unit := do
  match lastFormula (logic ++ s!"axiom t {binders}: $ {formula} $;") with
  | .ok s => checkEq name s expected
  | .error e => check name false s!"rejected at byte {e.pos}: {e.msg}"

/-- `src` is rejected; one `@` in it marks where, and the message contains `part`. The
position is counted in the whole specification, `logic` included when `withLogic`. -/
def elabRejects (name src part : String) (withLogic : Bool := true) : TestM Unit := do
  match src.splitOn "@" with
  | [before, after] =>
    let pre := if withLogic then logic else ""
    match elabString (pre ++ before ++ after) with
    | .ok _ => check name false "accepted"
    | .error e =>
      let pos := (pre ++ before).utf8ByteSize
      check name (e.pos == pos && contains e.msg part)
        s!"expected an error at byte {pos} containing \"{part}\"\n  actual:   byte {e.pos}: {e.msg}"
  | _ => check name false "test bug: the source must contain exactly one @"

def elabAccepts (name src : String) (withLogic : Bool := true) : TestM Unit := do
  match elabString ((if withLogic then logic else "") ++ src) with
  | .ok _ => check name true
  | .error e => check name false s!"rejected at byte {e.pos}: {e.msg}"

def tokenizerTests : TestM Unit := do
  -- the example of mm0.md: `(` left, `)` right, `*` both
  let env : MathEnv := ({} : MathEnv).addDelimiters "(*".toUTF8 ")*".toUTF8
  checkEq "math tokens: the example of mm0.md"
    (env.tokens "a*b(**{}) c" |>.toList) ["a", "*", "b(", "*", "*", "{}", ")", "c"]
  checkEq "math tokens: whitespace only" (({} : MathEnv).tokens " a  b\n c " |>.toList) ["a", "b", "c"]
  checkEq "math tokens: empty" (({} : MathEnv).tokens "  " |>.toList) []

def formulaTests : TestM Unit := do
  let ab := "(a b c: wff)"
  parsesTo "infixr associates to the right" ab "a -> b -> c" "(imp a (imp b c))"
  parsesTo "infixl associates to the left" ab "a /\\ b /\\ c" "(and (and a b) c)"
  parsesTo "tighter operator on the right" ab "a -> b /\\ c" "(imp a (and b c))"
  parsesTo "tighter operator on the left" ab "a /\\ b -> c" "(imp (and a b) c)"
  parsesTo "three levels" ab "a <-> b \\/ c /\\ a" "(iff a (or b (and c a)))"
  parsesTo "three levels, descending" ab "a /\\ b \\/ c <-> a" "(iff (or (and a b) c) a)"
  parsesTo "parentheses" ab "(a -> b) -> c" "(imp (imp a b) c)"
  parsesTo "nested parentheses" ab "((a))" "a"
  parsesTo "prefix binds tighter than infix" ab "~a -> b" "(imp (not a) b)"
  parsesTo "prefix of a parenthesized formula" ab "~(a -> b)" "(not (imp a b))"
  parsesTo "prefix on the right of an infix" ab "a /\\ ~b" "(and a (not b))"
  parsesTo "prefix twice" ab "~ ~a" "(not (not a))"
  parsesTo "a left delimiter needs no space" ab "~~a -> (~b)" "(imp (not (not a)) (not b))"
  parsesTo "prefix at max precedence, no arguments" ab "T. -> a" "(imp top a)"
  parsesTo "term application" ab "imp a b" "(imp a b)"
  parsesTo "application binds tighter than any operator" ab "imp a b -> c" "(imp (imp a b) c)"
  parsesTo "application as an operand of a prefix" ab "~ imp a b" "(not (imp a b))"
  parsesTo "application arguments are at max precedence" ab "imp (imp a b) (~c)" "(imp (imp a b) (not c))"
  parsesTo "a term with no arguments by name" ab "imp top a" "(imp top a)"
  parsesTo "a variable shadows nothing it should not" "(top2 a: wff)" "top2 -> a" "(imp top2 a)"
  -- binders and bound variables
  parsesTo "binder notation" "{x: set} (ph: wff x)" "A. x ph" "(all x ph)"
  parsesTo "binder notation, body to the right" "{x: set} (ph: wff x)" "A. x ph -> ph" "(imp (all x ph) ph)"
  parsesTo "binder body is parsed at the notation's precedence" "{x y: set}" "A. x A. y x = y" "(all x (all y (eq x y)))"
  -- coercions
  parsesTo "coercion inserted for an argument" "{x: set} (A: class)" "x e. A" "(el (cv x) A)"
  parsesTo "coercion on both sides" "{x y: set}" "x e. y" "(el (cv x) (cv y))"
  parsesTo "no coercion where the sort already fits" "{x y: set}" "x = y" "(eq x y)"
  -- general notation
  parsesTo "general notation" "{x: set} (ph: wff x) (A: class)" "{ x | ph } e. A" "(el (ab x ph) A)"
  parsesTo "general notation, inner formula at its own precedence" "{x: set} (ph ps: wff x)"
    "{ x | ph -> ps } e. { x | ph }" "(el (ab x (imp ph ps)) (ab x ph))"

def notationTests : TestM Unit := do
  -- the example of mm0.md: `[` at 20, then a at max, b at 41, `]`, c at 20
  let nota := "sort T; term z: T; term s (a: T): T; term foo (a b c: T): T;
term add (a b: T): T; infixl add: $+$ prec 41; term mul (a b: T): T; infixl mul: $*$ prec 60;
term eqt (a b: T): wff; infixl eqt: $==$ prec 10;
notation foo (a b c: T): T = ($[$: 20) a b ($]$: 40) c;
"
  let check' (name formula expected : String) : TestM Unit := do
    match lastFormula (logic ++ nota ++ "axiom t (x y w: T): $ " ++ formula ++ " == z $;") with
    | .ok s => checkEq name s s!"(eqt {expected} z)"
    | .error e => check name false s!"rejected at byte {e.pos}: {e.msg}"
  check' "notation: variables at max, at the next constant's precedence plus one, and at the notation's"
    "[ x y + w ] z" "(foo x (add y w) z)"
  check' "notation: the last variable takes operators at the notation's precedence or above"
    "[ x y ] z + w" "(foo x y (add z w))"
  check' "notation: the first variable is at max precedence" "[ (x + y) w ] z" "(foo (add x y) w z)"
  check' "notation: application at max needs no parentheses if it has no arguments" "[ z z ] z" "(foo z z z)"
  elabRejects "notation: an operator below the required precedence"
    (nota ++ "axiom t (x y w: T): $ [ x @+ y w ] z == z $;") "expected"
  elabRejects "notation: missing closing constant"
    (nota ++ "axiom t (x y w: T): $ [ x y @z == z $;") "expected `]`"
  -- declarations of notations
  elabRejects "infix on a term that is not binary" "term t1 (a: wff): wff; infixl @t1: $%$ prec 5;" "two arguments"
  elabRejects "infix at max precedence" "infixl @and: $%$ prec max;" "max"
  elabRejects "notation for an unknown term" "prefix @nope: $%$ prec 5;" "unknown term"
  elabRejects "token declared at two precedences" "prefix not: @$->$ prec 26;" "precedence"
  elabRejects "parenthesis as a notation token" "prefix not: @$($ prec 5;" "parenthes"
  elabRejects "constant that is not one token" "prefix not: @$a b$ prec 5;" "one token"
  elabRejects "constant that is empty" "prefix not: @$ $ prec 5;" "one token"
  elabRejects "coercion on a term that is not unary" "coercion @imp: wff > wff;" "one argument"
  elabRejects "coercion with an unknown sort" "coercion cv: set > @nope;" "unknown sort"
  elabRejects "coercion cycle" "term vc (a: class): set; coercion @vc: class > set;" "cycle"
  elabRejects "coercion diamond"
    "sort mid; term sm (x: set): mid; term mc (x: mid): class; coercion sm: set > mid; coercion @mc: mid > class;"
    "diamond"
  elabRejects "notation: variable used twice"
    "term f2 (a b: wff): wff; notation f2 (a b: wff): wff = ($#$: 10) a @a;" "twice"
  elabRejects "notation: variable not used"
    "term f2 (a b: wff): wff; notation @f2 (a b: wff): wff = ($#$: 10) a;" "not used"
  elabRejects "notation: wrong number of binders"
    "term f2 (a b: wff): wff; notation @f2 (a: wff): wff = ($#$: 10) a;" "argument"
  elabRejects "notation: unknown variable"
    "term f2 (a b: wff): wff; notation f2 (a b: wff): wff = ($#$: 10) a @c;" "variable"
  elabRejects "notation: constant at max before which a variable stands"
    "term f2 (a b: wff): wff; notation f2 (a b: wff): wff = ($#$: 10) a (@$!$: max) b;" "max"
  elabRejects "delimiter of more than one character" "delimiter $ @ab $;" "one character"

def declarationTests : TestM Unit := do
  elabAccepts "the logic signature" ""
  elabAccepts "def with a dummy"
    "def ex {x: set} (ph: wff x): wff = $ ~ A. x ~ph $;
def eu {x .y: set} (ph: wff x): wff = $ ex y (A. x (ph <-> x = y)) $;"
  elabAccepts "def without a value" "def foo (a: wff): wff;"
  elabAccepts "theorem with hypotheses in binders and arrows"
    "theorem mp (a b: wff) (h1: $ a $): $ a -> b $ > $ b $;"
  elabAccepts "dependency on a bound variable of an earlier binder group"
    "term sb {x: set} (a: class) (ph: wff x): wff;"
  elabAccepts "anonymous binders and arrows" "term f3 (_ _: wff): wff > wff;"
  elabAccepts "input and output statements are parsed" "output string: $ T. $ top;"
  -- names
  elabRejects "unknown sort in a binder" "term f (a: @nope): wff;" "unknown sort"
  elabRejects "unknown sort as a result" "term f (a: wff): @nope;" "unknown sort"
  elabRejects "duplicate sort" "sort @wff;" "already declared"
  elabRejects "duplicate term" "term @imp: wff;" "already declared"
  elabRejects "def and term share a namespace" "def @imp: wff;" "already declared"
  elabRejects "duplicate theorem" "axiom a1: $ T. $; theorem @a1: $ T. $;" "already declared"
  elabRejects "variable declared twice" "term f (a @a: wff): wff;" "declared twice"
  elabRejects "dummy with the name of a variable" "def f (a: wff) {@.a: set}: wff;" "declared twice"
  -- dependencies
  elabRejects "dependency on an unknown variable" "term f (a: wff @y): wff;" "unknown variable"
  elabRejects "dependency on a regular variable" "term f (b: set) (a: wff @b): wff;" "not a bound variable"
  elabRejects "dependency on a variable of the same binder group" "term f (c d: wff @d): wff;" "unknown variable"
  elabRejects "bound variable with dependencies" "term f {x: set} {y: set @x}: wff;" "bound variable"
  elabRejects "dummy with dependencies" "def f {x: set} (.y: set @x): wff;" "dummy"
  elabRejects "result depending on a regular variable" "term f (a: wff): wff @a;" "not a bound variable"
  -- order of variables and hypotheses
  elabRejects "variable binder after a hypothesis" "axiom t (h: $ T. $) @(a: wff): $ a $;" "after"
  elabRejects "variable type after a hypothesis in the arrows" "axiom t: $ T. $ > @wff > $ T. $;" "after"
  -- formulas
  elabRejects "unknown token" "axiom t (a: wff): $ a -> @b $;" "unknown"
  elabRejects "empty formula" "axiom t: $ @$;" "expression"
  elabRejects "operator without a right operand" "axiom t (a: wff): $ a -> @$;" "expression"
  elabRejects "trailing tokens" "axiom t (a b: wff): $ a @b $;" "expected"
  elabRejects "unclosed parenthesis" "axiom t (a: wff): $ (a -> a @$;" "`)`"
  elabRejects "closing parenthesis alone" "axiom t (a: wff): $ a @) $;" "expected"
  elabRejects "too few arguments" "axiom t (a: wff): $ imp a @$;" "expression"
  elabRejects "application where max precedence is required" "axiom t (a: wff): $ imp a @not a $;" "parenthes"
  elabRejects "prefix below the required precedence" "axiom t {x: set} (a: wff x): $ imp a @A. x a $;" "expected"
  elabRejects "sort mismatch without a coercion" "axiom t (A: class): $ A. @A T. $;" "sort"
  elabRejects "no coercion back" "axiom t (A: class): $ @A = A $;" "sort"
  elabRejects "regular variable in a bound position" "axiom t (y: set): $ A. @y T. $;" "bound variable"
  elabRejects "expression in a bound position" "axiom t: $ A. @T. T. $;" "bound variable"
  -- a parenthesized variable is still a variable (formal specification: PTParens)
  parsesTo "parenthesized variable in a bound position" "{x: set}" "A. (x) T." "(all x top)"
  elabRejects "formula of a sort that is not provable" "axiom t (A: class): $ @A $;" "provable"
  elabRejects "def value of the wrong sort" "def f (A: class): wff = $ @A $;" "sort"
  elabRejects "hypothesis of a sort that is not provable" "axiom t (A: class) (h: $ @A $): $ T. $;" "provable"
  -- coercion to a provable sort
  elabAccepts "coercion to the provable sort"
    "sort bool; term tr (b: bool): wff; coercion tr: bool > wff; term bt: bool; axiom t: $ bt $;"
  -- positions inside a formula are positions in the file
  elabRejects "error position in a second line" "axiom t (a: wff):\n  $ a ->\n    @b $;" "unknown"
  -- imports cannot be elaborated from a string
  elabRejects "import in a string" "@import \"x.mm0\";" "import" (withLogic := false)

def elabTests : TestM Unit := do
  tokenizerTests
  formulaTests
  notationTests
  declarationTests

end Tests.Mm0
