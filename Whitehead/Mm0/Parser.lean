/-
The primary parser of `.mm0` files: the grammar of `mm0.md`, production by production,
as a hand-written recursive descent with one token of lookahead.

Math strings are returned as raw text. `mm0.md` is taken literally here; where `mm0-c`'s
own parser accepts more or less than the grammar, that is listed in `docs/DESIGN.md`.

The parser state is the source and the current token. `parseStmt?` returns one statement
at a time, so a caller can process a large file without holding its whole syntax tree.
-/
import Whitehead.Mm0.Lexer

namespace Whitehead.Mm0

structure ParserState where
  src : ByteArray
  /-- The lookahead: the first token that has not been consumed. -/
  tok : Token
  /-- Where the last consumed token ended. -/
  prevStop : Nat

abbrev ParserM := EStateM ParseError ParserState

namespace Parser

def describe : TokenKind → String
  | .ident name => s!"identifier `{name}`"
  | .number n => s!"number {n}"
  | .math _ => "a math string"
  | .sym c => s!"`{c}`"
  | .str _ => "a string literal"
  | .eof => "end of file"

@[inline] def peek : ParserM Token :=
  fun s => .ok s.tok s

/-- Consumes the current token. An error in the token after it is reported here. -/
def advance : ParserM Unit := fun s =>
  let stop := s.tok.span.stop
  match Lexer.nextToken s.src stop with
  | .ok t => .ok () { s with tok := t, prevStop := stop }
  | .error e => .error e s

def errorAt {α : Type} (pos : Nat) (msg : String) : ParserM α :=
  throw ⟨pos, msg⟩

/-- Fails at the current token: `expected <what>, found <the current token>`. -/
def expected {α : Type} (what : String) : ParserM α := do
  let t ← peek
  errorAt t.span.start s!"expected {what}, found {describe t.kind}"

def isSym (c : Char) : ParserM Bool := do
  return (← peek).kind == .sym c

/-- Consumes the symbol `c` if it is the current token. -/
def trySym (c : Char) : ParserM Bool := do
  if ← isSym c then advance; return true else return false

def expectSym (c : Char) : ParserM Unit := do
  if !(← trySym c) then expected s!"`{c}`"

/-- Is the current token the identifier `kw`? -/
def isKeyword (kw : String) : ParserM Bool := do
  return (← peek).kind == .ident kw

def expectKeyword (kw : String) : ParserM Unit := do
  if ← isKeyword kw then advance else expected s!"`{kw}`"

def expectIdent (what : String) : ParserM Ident := do
  let t ← peek
  match t.kind with
  | .ident name => advance; return ⟨name, t.span⟩
  | _ => expected what

def expectMath : ParserM MathString := do
  let t ← peek
  match t.kind with
  | .math text => advance; return ⟨text, t.span⟩
  | _ => expected "a math string"

/-- `precedence-lvl ::= number | 'max'` -/
def parsePrec : ParserM Prec := do
  match (← peek).kind with
  | .number n => advance; return .num n
  | .ident "max" => advance; return .max
  | _ => expected "a precedence (a number or `max`)"

partial def parseIdents (acc : Array Ident) : ParserM (Array Ident) := do
  let t ← peek
  match t.kind with
  | .ident name => advance; parseIdents (acc.push ⟨name, t.span⟩)
  | _ => return acc

/-- `type ::= identifier (identifier)*` -/
def parseDepType : ParserM DepType := do
  let sort ← expectIdent "a sort name"
  return ⟨sort, ← parseIdents #[]⟩

/-- Which statement a binder list belongs to; the four binder productions of the grammar
differ only in what they allow. -/
inductive BinderCtx where
  /-- `type-binder`, in `term` and `notation` -/
  | term
  /-- `formula-type-binder`, in `axiom` and `theorem`: formulas allowed in `(...)` -/
  | assert
  /-- `dummy-binder`, in `def`: `.x` allowed -/
  | defn
  deriving BEq

/-- The names of one binder, up to but not including the `:`. The grammar of `mm0.md`
has no `_` in a `{...}` binder outside `def`; the formal specification (`parseCurlyBinder`
in `mm0.mm0`) allows it everywhere, and that is what is done here. -/
partial def parseBinderNames (ctx : BinderCtx) (acc : Array LocalName) :
    ParserM (Array LocalName) := do
  let t ← peek
  match t.kind with
  | .ident name =>
    advance
    parseBinderNames ctx (acc.push ⟨some name, false, t.span⟩)
  | .sym '_' =>
    advance
    parseBinderNames ctx (acc.push ⟨none, false, t.span⟩)
  | .sym '.' =>
    if ctx != .defn then
      errorAt t.span.start "dummy variables (`.x`) are only allowed in a `def`"
    advance
    let x ← expectIdent "a variable name"
    parseBinderNames ctx (acc.push ⟨some x.name, true, ⟨t.span.start, x.span.stop⟩⟩)
  | .sym ':' => return acc
  | _ => expected "a variable name or `:`"

/-- `(binder)*`: zero or more `{...}` and `(...)` groups. -/
partial def parseBinders (ctx : BinderCtx) (acc : Array Binder) : ParserM (Array Binder) := do
  let t ← peek
  let curly ←
    match t.kind with
    | .sym '{' => pure true
    | .sym '(' => pure false
    | _ => return acc
  advance
  let names ← parseBinderNames ctx #[]
  expectSym ':'
  let ty ← peek
  let type ←
    match ty.kind with
    | .math text =>
      if curly then
        errorAt ty.span.start "a `{...}` binder must have a sort, not a formula"
      if ctx != .assert then
        errorAt ty.span.start "hypotheses are only allowed in an `axiom` or `theorem`"
      advance
      pure (BinderType.formula ⟨text, ty.span⟩)
    | _ => pure (BinderType.type (← parseDepType))
  expectSym (if curly then '}' else ')')
  let stop := (← get).prevStop
  parseBinders ctx (acc.push ⟨curly, names, type, ⟨t.span.start, stop⟩⟩)

/-- `arrow-type ::= type | type '>' arrow-type`, as the list of types in order. -/
partial def parseArrowTypes (acc : Array DepType) : ParserM (Array DepType) := do
  let acc := acc.push (← parseDepType)
  if ← trySym '>' then parseArrowTypes acc else return acc

/-- `formula-arrow-type ::= formula | (type | formula) '>' formula-arrow-type`. Returns
the elements before the last one, and the last one, which must be a formula. -/
partial def parseFormulaArrow (acc : Array BinderType) : ParserM (Array BinderType × MathString) := do
  let t ← peek
  match t.kind with
  | .math text =>
    advance
    if ← trySym '>' then parseFormulaArrow (acc.push (.formula ⟨text, t.span⟩))
    else return (acc, ⟨text, t.span⟩)
  | _ =>
    let ty ← parseDepType
    if ← trySym '>' then parseFormulaArrow (acc.push (.type ty))
    else errorAt t.span.start "the conclusion of an axiom or theorem must be a formula (`$ ... $`)"

/-- `prec-constant ::= '(' constant ':' precedence-lvl ')'`, after the `(`. -/
def parsePrecConstTail : ParserM PrecConst := do
  let const ← expectMath
  expectSym ':'
  let prec ← parsePrec
  expectSym ')'
  return ⟨const, prec⟩

/-- `(notation-literal)*` -/
partial def parseNotaLits (acc : Array NotaLit) : ParserM (Array NotaLit) := do
  let t ← peek
  match t.kind with
  | .sym '(' => advance; parseNotaLits (acc.push (.const (← parsePrecConstTail)))
  | .ident name => advance; parseNotaLits (acc.push (.var ⟨name, t.span⟩))
  | _ => return acc

/-- `(identifier | math-string)*` -/
partial def parseInoutArgs (acc : Array InoutArg) : ParserM (Array InoutArg) := do
  let t ← peek
  match t.kind with
  | .ident name => advance; parseInoutArgs (acc.push (.ident ⟨name, t.span⟩))
  | .math text => advance; parseInoutArgs (acc.push (.math ⟨text, t.span⟩))
  | _ => return acc

def sortModRank : String → Option Nat
  | "pure" => some 0
  | "strict" => some 1
  | "provable" => some 2
  | "free" => some 3
  | _ => none

/-- `sort-stmt ::= ('pure')? ('strict')? ('provable')? ('free')? 'sort' identifier ';'`,
up to and including the name. `next` is the lowest modifier rank still allowed. -/
partial def parseSort (mods : SortMods) (next : Nat) : ParserM StmtKind := do
  let t ← peek
  match t.kind with
  | .ident "sort" =>
    advance
    return .sort mods (← expectIdent "a sort name")
  | .ident name =>
    match sortModRank name with
    | some rank =>
      if rank < next then
        errorAt t.span.start
          "sort modifiers must appear in the order `pure strict provable free`, each at most once"
      advance
      let mods :=
        match rank with
        | 0 => { mods with isPure := true }
        | 1 => { mods with isStrict := true }
        | 2 => { mods with isProvable := true }
        | _ => { mods with isFree := true }
      parseSort mods (rank + 1)
    | none => expected "`sort`"
  | _ => expected "`sort`"

def parseSimpleNota (kind : SimpleNotaKind) : ParserM StmtKind := do
  let term ← expectIdent "a term name"
  expectSym ':'
  let const ← expectMath
  expectKeyword "prec"
  return .simpleNota kind term const (← parsePrec)

/-- One statement without its final `;`. The current token is the identifier `kw`. -/
def parseStmtKind (kw : String) : ParserM StmtKind := do
  if (sortModRank kw).isSome || kw == "sort" then
    return ← parseSort {} 0
  match kw with
  | "term" =>
    advance
    let name ← expectIdent "a term name"
    let binders ← parseBinders .term #[]
    expectSym ':'
    let types ← parseArrowTypes #[]
    return .term name binders types.pop types.back!
  | "axiom" | "theorem" =>
    advance
    let name ← expectIdent (if kw == "axiom" then "an axiom name" else "a theorem name")
    let binders ← parseBinders .assert #[]
    expectSym ':'
    let (hyps, concl) ← parseFormulaArrow #[]
    return .assert (if kw == "axiom" then .ax else .thm) name binders hyps concl
  | "def" =>
    advance
    let name ← expectIdent "a definition name"
    let binders ← parseBinders .defn #[]
    expectSym ':'
    let types ← parseArrowTypes #[]
    if ← trySym '=' then
      return .defn name binders types.pop types.back! (some (← expectMath))
    else if ← isSym ';' then
      return .defn name binders types.pop types.back! none
    else
      expected "`>`, `=` or `;`"
  | "delimiter" =>
    advance
    let left ← expectMath
    match (← peek).kind with
    | .math _ => return .delimiter left (some (← expectMath))
    | _ => return .delimiter left none
  | "prefix" => advance; parseSimpleNota .pfx
  | "infixl" => advance; parseSimpleNota .infl
  | "infixr" => advance; parseSimpleNota .infr
  | "coercion" =>
    advance
    let term ← expectIdent "a term name"
    expectSym ':'
    let src ← expectIdent "a sort name"
    expectSym '>'
    let tgt ← expectIdent "a sort name"
    return .coercion term src tgt
  | "notation" =>
    advance
    let term ← expectIdent "a term name"
    let binders ← parseBinders .term #[]
    expectSym ':'
    let ret ← parseDepType
    expectSym '='
    expectSym '('
    let head ← parsePrecConstTail
    return .genNota term binders ret head (← parseNotaLits #[])
  | "input" | "output" =>
    advance
    let kind ← expectIdent (if kw == "input" then "an input kind" else "an output kind")
    expectSym ':'
    return .inout (kw == "input") kind (← parseInoutArgs #[])
  | "import" =>
    advance
    let t ← peek
    match t.kind with
    | .str path => advance; return .importFile path t.span
    | _ => expected "a string literal (the path of the file to import)"
  | _ => expected "a statement"

/-- The next statement, or `none` at the end of the file. -/
def parseStmt? : ParserM (Option Stmt) := do
  let t ← peek
  match t.kind with
  | .eof => return none
  | .ident kw =>
    let kind ← parseStmtKind kw
    expectSym ';'
    return some ⟨kind, ⟨t.span.start, (← get).prevStop⟩⟩
  | _ => expected "a statement"

partial def parseStmts (acc : Array Stmt) : ParserM (Array Stmt) := do
  match ← parseStmt? with
  | some s => parseStmts (acc.push s)
  | none => return acc

/-- The state at the start of `src`, with the first token read. -/
def init (src : ByteArray) : Except ParseError ParserState :=
  (Lexer.nextToken src 0).map fun t => ⟨src, t, 0⟩

end Parser

/-- Parses a whole `.mm0` file. -/
def parse (src : ByteArray) : Except ParseError (Array Stmt) :=
  match Parser.init src with
  | .error e => .error e
  | .ok s =>
    match (Parser.parseStmts #[]).run s with
    | .ok stmts _ => .ok stmts
    | .error e _ => .error e

def parseString (src : String) : Except ParseError (Array Stmt) :=
  parse src.toUTF8

end Whitehead.Mm0
