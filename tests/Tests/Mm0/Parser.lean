/-
Unit tests for the `.mm0` lexer and primary parser on hand-written snippets.

The accepted and rejected snippets include every case of `tests/mm0_mmu/{pass,fail}` in
the MM0 repository that is decided at the level of the grammar.
-/
import Whitehead.Mm0.Parser
import Whitehead.Mm0.Print
import Tests.Harness

open Whitehead.Mm0

namespace Tests.Mm0

/-- `src` parses, and printing the result is a fixed point of parse-then-print. -/
def accepts (name src : String) : TestM Unit := do
  match parseString src with
  | .error e => check name false s!"rejected at byte {e.pos}: {e.msg}"
  | .ok stmts =>
    let printed := printStmts stmts
    match parseString printed with
    | .error e => check name false s!"printed form rejected at byte {e.pos}: {e.msg}\n{printed}"
    | .ok stmts' => checkEq name (printStmts stmts') printed

/-- `src` parses and prints as `expected` (one statement per line). -/
def printsAs (name src expected : String) : TestM Unit := do
  match parseString src with
  | .error e => check name false s!"rejected at byte {e.pos}: {e.msg}"
  | .ok stmts => checkEq name (printStmts stmts) expected

/-- `src` is rejected. It contains exactly one `@`, which is removed before parsing and
marks the byte at which the error must be reported; the message must contain `msgPart`. -/
def rejects (name src msgPart : String) : TestM Unit := do
  match src.splitOn "@" with
  | [before, after] =>
    match parseString (before ++ after) with
    | .ok _ => check name false "accepted"
    | .error e =>
      check name (e.pos == before.utf8ByteSize && contains e.msg msgPart)
        s!"expected an error at byte {before.utf8ByteSize} containing \"{msgPart}\"\n  actual:   byte {e.pos}: {e.msg}"
  | _ => check name false "test bug: the source must contain exactly one @"

def tokenKinds (src : String) : Except ParseError (List TokenKind) :=
  (Lexer.tokenize src.toUTF8).map fun ts => ts.toList.map (·.kind)

instance : ToString TokenKind := ⟨fun k => toString (repr k)⟩
instance : ToString (Except ParseError (List TokenKind)) := ⟨fun
  | .ok ks => toString ks
  | .error e => s!"error at {e.pos}: {e.msg}"⟩
instance : BEq (Except ParseError (List TokenKind)) := ⟨fun
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false⟩

def lexerTests : TestM Unit := do
  checkEq "lex: symbols" (tokenKinds "* . : ; ( ) > { } = _")
    (.ok ("*.:;()>{}=_".toList.map TokenKind.sym ++ [.eof]))
  checkEq "lex: identifiers" (tokenKinds "a _a a_ __ A1 _1 sort")
    (.ok (["a", "_a", "a_", "__", "A1", "_1", "sort"].map TokenKind.ident ++ [.eof]))
  checkEq "lex: numbers" (tokenKinds "0 1 10 2046 4294967296")
    (.ok ([0, 1, 10, 2046, 4294967296].map TokenKind.number ++ [.eof]))
  checkEq "lex: math strings keep their text" (tokenKinds "$ a -> b $$$ $\n x\n$")
    (.ok [.math " a -> b ", .math "", .math "\n x\n", .eof])
  checkEq "lex: no space needed between lexemes" (tokenKinds "a:b>c$x$;")
    (.ok [.ident "a", .sym ':', .ident "b", .sym '>', .ident "c", .math "x", .sym ';', .eof])
  checkEq "lex: comments" (tokenKinds "a -- b c\n--| doc\n d --\n")
    (.ok [.ident "a", .ident "d", .eof])
  checkEq "lex: string literals and their escapes"
    (tokenKinds "\"a/b.mm0\" \"\" \"q\\\"\\\\\\n\\r\\x41\"")
    (.ok [.str "a/b.mm0", .str "", .str "q\"\\\n\rA", .eof])
  checkEq "lex: a comment marker inside a math string is text" (tokenKinds "$ a -- b $")
    (.ok [.math " a -- b ", .eof])
  checkEq "lex: empty input" (tokenKinds "") (.ok [.eof])
  -- positions
  let spans :=
    match Lexer.tokenize "ab  $c$\n;".toUTF8 with
    | .ok ts => ts.toList.map fun t => (t.span.start, t.span.stop)
    | .error _ => []
  checkEq "lex: spans" spans [(0, 2), (4, 7), (8, 9), (9, 9)]
  checkEq "lineCol" (lineCol "ab\ncd\n\nx".toUTF8 4) (2, 2)
  checkEq "lineCol: start" (lineCol "ab\ncd".toUTF8 0) (1, 1)
  checkEq "lineCol: end of file" (lineCol "ab\n".toUTF8 3) (2, 1)

def acceptTests : TestM Unit := do
  -- tests/mm0_mmu/pass
  accepts "pass/comment" " --  <-- comment doesn't start the line\nsort \n-- comment inside a statement\ns;"
  accepts "pass/id" "sort id_1;\nsort Id2_;\nsort _id3;\n"
  accepts "pass/int" "sort s; term a: s;\nprefix a: $ + $ prec 0;\nprefix a: $ * $ prec 2046;\n"
  accepts "pass/whitespace" "sort s ;\nsort t\n;\n"
  printsAs "pass/sort"
    ("sort s0; free sort s1; provable sort s2; provable free sort s3; strict sort s4;"
      ++ "strict free sort s5; strict provable sort s6; strict provable free sort s7;"
      ++ "pure sort s8; pure free sort s9; pure provable sort s10; pure provable free sort s11;"
      ++ "pure strict sort s12; pure strict free sort s13; pure strict provable sort s14;"
      ++ "pure strict provable free sort s15;")
    ("sort s0;\nfree sort s1;\nprovable sort s2;\nprovable free sort s3;\nstrict sort s4;\n"
      ++ "strict free sort s5;\nstrict provable sort s6;\nstrict provable free sort s7;\n"
      ++ "pure sort s8;\npure free sort s9;\npure provable sort s10;\npure provable free sort s11;\n"
      ++ "pure strict sort s12;\npure strict free sort s13;\npure strict provable sort s14;\n"
      ++ "pure strict provable free sort s15;\n")
  accepts "pass/blank_binder" "axiom cast (_ b: wff): $ b $ > $ b $;"
  -- every statement form, normalized
  printsAs "term with binders" "term  imp(ph ps:wff) :wff ;" "term imp (ph ps: wff): wff;\n"
  printsAs "term with arrows" "term imp: wff > wff > wff;" "term imp: wff > wff > wff;\n"
  printsAs "term with bound variable and dependency"
    "term all {x: set} (ph: wff x): wff;" "term all {x: set} (ph: wff x): wff;\n"
  printsAs "term mixing binders and arrows, with dependencies in the arrows"
    "term foo {x y: set} (_: wff x): wff x y > set > wff y;"
    "term foo {x y: set} (_: wff x): wff x y > set > wff y;\n"
  printsAs "term with no arguments" "term bot: wff;" "term bot: wff;\n"
  printsAs "binder with no names" "term foo (: wff): wff;" "term foo (: wff): wff;\n"
  -- the grammar of mm0.md has no `_` here; the formal specification allows it
  printsAs "anonymous bound variable" "term foo {_ x: s}: s;" "term foo {_ x: s}: s;\n"
  printsAs "axiom with hypotheses as arrows"
    "axiom ax_mp (ph ps: wff): $ ph $ > $ ph -> ps $ > $ ps $;"
    "axiom ax_mp (ph ps: wff): $ ph $ > $ ph -> ps $ > $ ps $;\n"
  printsAs "theorem with named hypotheses"
    "theorem mp (ph ps: wff) (h1: $ ph $) (h2 _: $ ph -> ps $): $ ps $;"
    "theorem mp (ph ps: wff) (h1: $ ph $) (h2 _: $ ph -> ps $): $ ps $;\n"
  printsAs "axiom with anonymous variables in the arrows"
    "axiom foo: wff > $ a $ > $ b $;" "axiom foo: wff > $ a $ > $ b $;\n"
  printsAs "theorem with no binders" "theorem a1i: $ T. $;" "theorem a1i: $ T. $;\n"
  printsAs "def with dummies and a value"
    "def weu {x .y: set} (ph: wff x): wff = $ E. y A. x (ph <-> x =s y) $;"
    "def weu {x .y: set} (ph: wff x): wff = $ E. y A. x (ph <-> x =s y) $;\n"
  printsAs "def with dummies in a regular binder"
    "def foo (a .b .c: nat): nat = $ a $;" "def foo (a .b .c: nat): nat = $ a $;\n"
  printsAs "abstract def" "def foo (a: nat): nat;" "def foo (a: nat): nat;\n"
  -- not in the grammar of mm0.md, but used by examples/hol.mm0
  printsAs "def with an arrow type" "def all: type > term;" "def all: type > term;\n"
  printsAs "def with an arrow type and a value"
    "def foo (a: nat): nat > nat = $ a $;" "def foo (a: nat): nat > nat = $ a $;\n"
  printsAs "delimiter, one list" "delimiter $ ( ) ~ $;" "delimiter $ ( ) ~ $;\n"
  printsAs "delimiter, two lists" "delimiter $ ( ~ $  $ ) $;" "delimiter $ ( ~ $ $ ) $;\n"
  printsAs "prefix" "prefix not: $~$ prec max;" "prefix not: $~$ prec max;\n"
  printsAs "infixl" "infixl add: $+$ prec 64;" "infixl add: $+$ prec 64;\n"
  printsAs "infixr" "infixr imp: $->$ prec 25;" "infixr imp: $->$ prec 25;\n"
  printsAs "coercion" "coercion cv: set > class;" "coercion cv: set > class;\n"
  printsAs "notation"
    "notation ab {x: set} (ph: wff x): class = ($ { $ : max) x ($|$:0) ph ($}$:0);"
    "notation ab {x: set} (ph: wff x): class = ($ { $: max) x ($|$: 0) ph ($}$: 0);\n"
  printsAs "notation with only a head constant"
    "notation zero: nat = ($0$: max);" "notation zero: nat = ($0$: max);\n"
  printsAs "input" "input string: $ a $ b $c$;" "input string: $ a $ b $c$;\n"
  printsAs "output with no arguments" "output string:;" "output string:;\n"
  -- math strings are kept verbatim, newlines included
  printsAs "math string text is preserved"
    "axiom a: $  x\n   y $;" "axiom a: $  x\n   y $;\n"
  -- pseudo-keywords are ordinary identifiers wherever an identifier is expected
  accepts "keywords as names"
    ("sort sort; pure sort pure; term term: sort; term prec (max free: sort): sort;"
      ++ "axiom axiom: $ term $; theorem theorem (def: sort): $ def $; def def: sort;"
      ++ "prefix prefix: $x$ prec 0; coercion coercion: sort > pure;"
      ++ "notation notation (input: sort): sort = ($y$: max) input; input input:; output output: output;")
  accepts "empty file" ""
  accepts "only comments" "-- nothing\n   -- here\n"
  -- a math string is any bytes other than `$`
  accepts "NUL inside a math string" "axiom a: $ x\x00 $;"
  -- `import` is an mm0-rs extension, not in mm0.md
  printsAs "import" "import  \"peano.mm0\" ;" "import \"peano.mm0\";\n"
  printsAs "import between statements, path with escapes"
    "sort s; import \"a\\\\b \\\"c\\\".mm0\"; sort t;"
    "sort s;\nimport \"a\\\\b \\\"c\\\".mm0\";\nsort t;\n"
  accepts "import as a name" "sort import; term import: import;"

def rejectTests : TestM Unit := do
  -- tests/mm0_mmu/fail
  rejects "fail/bad-id1: empty id" "sort @;" "expected a sort name"
  rejects "fail/bad-id2: blank id" "sort  \n @;" "expected a sort name"
  rejects "fail/bad-id3: id starting with a digit" "sort @0;" "expected a sort name"
  rejects "fail/bad-id4: forbidden character" "sort sot@-;" "illegal character"
  rejects "fail/bad-id5: single underscore" "sort @_;" "expected a sort name"
  rejects "fail/bad-int2: not an int" "prefix p : $+$ prec 1@.0;" "expected `;`"
  rejects "fail/bad-int3: sign" "prefix p : $+$ prec @+1;" "illegal character"
  rejects "fail/bad-int4: sign" "prefix plus: $ + $ prec @-1;" "illegal character"
  rejects "fail/bad-int5: leading zero" "prefix p : $+$ prec @01;" "leading zero"
  rejects "fail/bad-math-string1" "delimiter $ $ @$;\n" "unterminated math string"
  rejects "fail/bad-math-string2" "delimiter $ $ $  $  @$ ;\n" "unterminated math string"
  rejects "fail/bad-math-string3" "delimiter $ $ $ $ @$ $ ;\n" "expected `;`"
  rejects "fail/bad-sort21" "strict @pure sort s21;" "order"
  rejects "fail/bad-sort31" "provable @pure sort s31;" "order"
  rejects "fail/bad-sort32" "provable @strict sort s32;" "order"
  rejects "fail/bad-sort41" "free @pure sort s41;" "order"
  rejects "fail/bad-sort42" "free @strict sort s42;" "order"
  rejects "fail/bad-sort43" "free @provable sort s43;" "order"
  rejects "fail/bad-whitespace1: tab" "sort s@\t;" "tab"
  rejects "fail/bad-whitespace2: line tabulation" "sort s@\x0b;" "illegal character"
  rejects "fail/bad-whitespace3: form feed" "sort s@\x0c;" "illegal character"
  rejects "fail/bad-whitespace4: carriage return" "sort s@\r;" "carriage return"
  rejects "fail/non-ascii1" "sort @ß;" "non-ASCII"
  rejects "fail/non-ascii2" "sort s@ ;" "non-ASCII"
  -- lexical
  rejects "NUL byte" "sort s@\x00;" "NUL"
  rejects "comment without a final newline" "sort s; @-- the end" "newline"
  rejects "unclosed string literal" "import @\"peano.mm0;\n" "unclosed string literal"
  rejects "unknown escape in a string literal" "import \"a@\\qb\";" "escape"
  rejects "bad hex escape in a string literal" "import \"a@\\xZ1\";" "escape"
  rejects "string literal that is not UTF-8" "import @\"\\xff\";" "UTF-8"
  rejects "single dash" "sort s; @- comment" "illegal character"
  rejects "number glued to a letter" "prefix p: $+$ prec 12@a;" "number"
  rejects "repeated modifier" "pure @pure sort s;" "order"
  rejects "unterminated math string at the end" "axiom a: @$ x" "unterminated math string"
  -- statements
  rejects "not a statement" "@foo bar;" "expected a statement"
  rejects "statement starting with a symbol" "sort s; @; sort t;" "expected a statement"
  rejects "missing semicolon at end of file" "sort s@" "expected `;`"
  rejects "modifier without sort" "pure @term foo: s;" "expected `sort`"
  rejects "missing colon in binder" "term foo (x y wff@): wff;" "expected a variable name or `:`"
  rejects "unclosed binder" "term foo (x: wff@; " "expected `)`"
  rejects "mismatched binder brackets" "term foo {x: set@): wff;" "expected `}`"
  rejects "missing type after colon" "term foo (x: @): wff;" "expected a sort name"
  rejects "missing return type" "term foo (x: wff)@;" "expected `:`"
  rejects "dangling arrow" "term foo: wff > @;" "expected a sort name"
  rejects "dummy outside def" "term foo (x @.y: s): s;" "only allowed in a `def`"
  rejects "dummy without a name" "def foo (.@: s): s;" "expected a variable name"
  rejects "formula as a term argument" "term foo (h: @$ x $): s;" "only allowed in an `axiom` or `theorem`"
  rejects "formula as a term result" "term foo: @$ x $;" "expected a sort name"
  rejects "formula in a curly binder" "theorem foo {x: @$ a $}: $ a $;" "must have a sort"
  rejects "axiom ending in a type" "axiom ax_1 (a b: wff): @wff;" "must be a formula"
  rejects "axiom ending in a type after hypotheses" "axiom foo: $ a $ > @wff;" "must be a formula"
  rejects "def with two values" "def foo: wff = $ x $ @$ y $;" "expected `;`"
  rejects "def with a formula in the arrows" "def foo: wff > @$ x $;" "expected a sort name"
  rejects "def value that is not a formula" "def foo: wff = @x;" "expected a math string"
  rejects "hypothesis in a def" "def foo (h: @$ x $): wff;" "only allowed in an `axiom` or `theorem`"
  rejects "notation without a head constant" "notation foo (a: s): s = @a ($x$: 1);" "expected `(`"
  rejects "notation constant without precedence" "notation foo: s = ($x$@);" "expected `:`"
  rejects "notation with dummy" "notation foo (@.a: s): s = ($x$: 1);" "only allowed in a `def`"
  rejects "bad precedence" "prefix p: $+$ prec @foo;" "expected a precedence"
  rejects "missing prec keyword" "prefix p: $+$ @5;" "expected `prec`"
  rejects "simple notation constant must be a math string" "infixl p: @x prec 5;" "expected a math string"
  rejects "coercion without arrow" "coercion c: a @b;" "expected `>`"
  rejects "delimiter without a math string" "delimiter @;" "expected a math string"
  rejects "input kind missing" "input @: $x$;" "expected an input kind"
  rejects "stray token in input" "input ast: $x$ @5;" "expected `;`"
  rejects "import without a string" "import @peano;" "expected a string literal"
  rejects "import without semicolon" "import \"x.mm0\"@" "expected `;`"
  rejects "string literal where a name belongs" "sort @\"s\";" "expected a sort name"
  rejects "modifier before import" "pure @import \"x.mm0\";" "expected `sort`"

def errorFormatTests : TestM Unit := do
  let src := "sort s;\nterm foo (x: ): s;\n"
  match parseString src with
  | .ok _ => check "format: error expected" false
  | .error e =>
    checkEq "format: message with line, column and source line"
      (e.format "t.mm0" src.toUTF8)
      "t.mm0:2:14: error: expected a sort name, found `)`\n  term foo (x: ): s;\n               ^"

def parserTests : TestM Unit := do
  lexerTests
  acceptTests
  rejectTests
  errorFormatTests

end Tests.Mm0
