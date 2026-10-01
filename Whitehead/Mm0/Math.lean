/-
The secondary parser: the contents of `$ ... $` ("Secondary parsing" in `mm0.md`).

A math string is cut into tokens at whitespace and at the declared delimiters, and the
tokens are parsed by precedence climbing against the notations declared so far. The
result is typed on the way: every argument is checked against the binder it goes into,
and coercions are inserted where the sorts differ.

The parser implements the grammar of `mm0.md` exactly. In particular the left operand
of an infix operator must itself have the precedence the grammar asks for, which is
tracked as the *level* of every parsed expression; `mm0-rs` and mm0-c take a shortcut
that agrees with the grammar only when no precedence level mixes left and right
associative operators.
-/
import Std.Data.HashMap
import Whitehead.Mm0.Env
import Whitehead.Mm0.Lexer

namespace Whitehead.Mm0

namespace Prec

/-- `p ≤ q` on precedences, `max` being above every number. -/
def le : Prec → Prec → Bool
  | _, .max => true
  | .max, .num _ => false
  | .num a, .num b => a ≤ b

def toString : Prec → String
  | .num n => s!"{n}"
  | .max => "max"

instance : ToString Prec := ⟨Prec.toString⟩

/-- The precedence of a term applied to arguments: `expression(1024)` in `mm0.md`. -/
def app : Prec := .num 1024

end Prec

/-- A piece of a notation after its leading constant. -/
inductive Literal where
  /-- The argument with index `idx`, parsed at precedence `prec`. -/
  | var (idx : Nat) (prec : Prec)
  | const (token : String)
  deriving Inhabited, Repr

/-- A notation that starts with a constant: `prefix`, or `notation`. -/
structure PrefixInfo where
  term : Nat
  /-- What follows the leading constant. -/
  lits : Array Literal
  deriving Inhabited

structure InfixInfo where
  term : Nat
  rassoc : Bool
  deriving Inhabited

/-- What the secondary parser knows: delimiters, notations and coercions. -/
structure MathEnv where
  /-- Per byte: a token ends after it. -/
  delimsLeft : Array Bool := Array.replicate 256 false
  /-- Per byte: a token ends before it. -/
  delimsRight : Array Bool := Array.replicate 256 false
  /-- Every constant of a notation, with its one precedence. -/
  consts : Std.HashMap String Prec := {}
  prefixes : Std.HashMap String PrefixInfo := {}
  infixes : Std.HashMap String InfixInfo := {}
  /-- `(s1, s2)` ↦ the coercion terms that lead from sort `s1` to sort `s2`, the first to
  apply first. Closed under composition. -/
  coes : Std.HashMap (Nat × Nat) (Array Nat) := {}
  /-- A sort that is not provable ↦ the provable sort it can be coerced to. -/
  coeProv : Std.HashMap Nat Nat := {}
  deriving Inhabited

/-- A token of a math string: its text and its offset in the file. -/
structure MathToken where
  text : String
  pos : Nat
  deriving Inhabited

namespace MathEnv

def addDelimiters (env : MathEnv) (left right : ByteArray) : MathEnv :=
  { env with
    delimsLeft := left.foldl (fun a c => a.set! c.toNat true) env.delimsLeft
    delimsRight := right.foldl (fun a c => a.set! c.toNat true) env.delimsRight }

/-- The tokens of the math string `bytes`, which starts at file offset `base`: split at
whitespace, after every left delimiter and before every right delimiter. -/
def tokenize (env : MathEnv) (bytes : ByteArray) (base : Nat) : Array MathToken := Id.run do
  let mut tokens := #[]
  let mut i := 0
  while i < bytes.size do
    let c := bytes.get! i
    if c == 0x20 || c == 0x0A then
      i := i + 1
    else
      let start := i
      i := i + 1
      -- the token ends here if its last byte is a left delimiter, or at whitespace, or
      -- before a right delimiter
      while i < bytes.size && !env.delimsLeft[(bytes.get! (i - 1)).toNat]! &&
          (let d := bytes.get! i; d != 0x20 && d != 0x0A && !env.delimsRight[d.toNat]!) do
        i := i + 1
      let text := (String.fromUTF8? (bytes.extract start i)).getD ""
      tokens := tokens.push ⟨text, base + start⟩
  return tokens

/-- The texts of the tokens of `text`. -/
def tokens (env : MathEnv) (text : String) : Array String :=
  (env.tokenize text.toUTF8 0).map (·.text)

/-- Records the precedence of a notation constant. A constant has one precedence. -/
def addConst (env : MathEnv) (token : String) (p : Prec) : Except String MathEnv :=
  match env.consts[token]? with
  | some q =>
    if q == p then .ok env
    else .error s!"the token `{token}` already has precedence {q}; a token has one precedence"
  | none => .ok { env with consts := env.consts.insert token p }

def addPrefix (env : MathEnv) (token : String) (info : PrefixInfo) : Except String MathEnv :=
  if env.prefixes.contains token then
    .error s!"the token `{token}` already starts another notation"
  else .ok { env with prefixes := env.prefixes.insert token info }

def addInfix (env : MathEnv) (token : String) (info : InfixInfo) : Except String MathEnv :=
  if env.infixes.contains token then
    .error s!"the token `{token}` is already an infix operator"
  else .ok { env with infixes := env.infixes.insert token info }

/-- Adds the coercion `t : s1 > s2` and everything it composes to. `provable` tells
which sorts are provable, `sortName` names a sort for messages. The coercions must not
form a cycle, and there must be at most one way from one sort to another and from a sort
to a provable one. -/
def addCoe (env : MathEnv) (provable : Nat → Bool) (sortName : Nat → String) (s1 s2 t : Nat) :
    Except String MathEnv := do
  -- everything that reaches s1, and everything reachable from s2, with the paths
  let mut before : Array (Nat × Array Nat) := #[(s1, #[])]
  let mut after : Array (Nat × Array Nat) := #[(s2, #[])]
  for ((a, b), path) in env.coes.toArray do
    if b == s1 then before := before.push (a, path)
    if a == s2 then after := after.push (b, path)
  let mut coes := env.coes
  for (a, pa) in before do
    for (b, pb) in after do
      if a == b then
        throw s!"coercion cycle: sort `{sortName a}` would be coerced to itself"
      if coes.contains (a, b) then
        throw s!"coercion diamond: there would be two ways from sort `{sortName a}` to sort `{sortName b}`"
      coes := coes.insert (a, b) (pa ++ #[t] ++ pb)
  let mut coeProv : Std.HashMap Nat Nat := {}
  for ((a, b), _) in coes.toArray do
    if provable b && !provable a then
      match coeProv[a]? with
      | some b' =>
        if b' != b then
          throw s!"coercion diamond to provable: sort `{sortName a}` could be coerced to the provable sorts `{sortName b'}` and `{sortName b}`"
      | none => coeProv := coeProv.insert a b
  return { env with coes, coeProv }

end MathEnv

/-- What the parser needs to know about the declarations so far and about the variables
in scope. -/
structure MathCtx where
  env : MathEnv
  sorts : Array SortDecl
  terms : Array TermDecl
  termIds : Std.HashMap String Nat
  /-- The variables in scope: the arguments, then the dummies. -/
  vars : Array VarDecl
  tokens : Array MathToken
  /-- The file offset of the closing `$`, where "the formula ends here" is reported. -/
  endPos : Nat

/-- The sort an expression must have. -/
inductive Target where
  | sort (s : Nat)
  /-- Any provable sort, or a sort with a coercion to one. -/
  | provable
  /-- No requirement. -/
  | any

namespace MathParser

/-- The index of the variable named `name`, from `i` on. A plain loop: this is done for
every identifier of every formula, and `Array.findIdx?` with a comparison of
`Option String` calls a closure and compares boxed options for every variable. -/
partial def findVar (vars : Array VarDecl) (name : String) (i : Nat) : Option Nat :=
  if h : i < vars.size then
    match vars[i].name with
    | some n => if n == name then some i else findVar vars name (i + 1)
    | none => findVar vars name (i + 1)
  else none

/-- The state is the index of the next token. -/
abbrev MathM := EStateM ParseError Nat

def fail {α : Type} (pos : Nat) (msg : String) : MathM α :=
  throw ⟨pos, msg⟩

def peek (c : MathCtx) : MathM (Option MathToken) := do
  return c.tokens[← get]?

/-- The file offset of the next token, or of the end of the formula. -/
def here (c : MathCtx) : MathM Nat := do
  return match c.tokens[← get]? with
    | some t => t.pos
    | none => c.endPos

def advance : MathM Unit :=
  modify (· + 1)

def sortName (c : MathCtx) (s : Nat) : String :=
  (c.sorts[s]?.map (·.name)).getD s!"s{s}"

def isIdent (s : String) : Bool :=
  let b := s.toUTF8
  b.size > 0 && Lexer.isIdentStart (b.get! 0) && b.foldl (fun ok ch => ok && Lexer.isIdentRest ch) true

/-- Applies the coercions that lead from sort `s` to sort `target`. -/
def coerce (c : MathCtx) (pos : Nat) (e : Expr) (s target : Nat) : MathM Expr :=
  if s == target then pure e
  else
    match c.env.coes[(s, target)]? with
    | some path => pure (path.foldl (fun e t => Expr.app t #[e]) e)
    | none =>
      fail pos s!"this expression has sort `{sortName c s}`, but sort `{sortName c target}` is expected here and there is no coercion"

/-- An expression of sort `s` as the argument for the binder `b`. -/
def coerceArg (c : MathCtx) (pos : Nat) (e : Expr) (s : Nat) (b : VarDecl) : MathM Expr :=
  if b.bound then
    match e with
    | .var v =>
      if s == b.sort && (c.vars[v]?.map (·.bound)).getD false then pure e
      else fail pos s!"a bound variable of sort `{sortName c b.sort}` is required here"
    | _ => fail pos s!"a bound variable of sort `{sortName c b.sort}` is required here"
  else coerce c pos e s b.sort

mutual

/-- `expression(p)` of `mm0.md`: an expression whose precedence is at least `p`. Returns
the expression, its sort, and its level: the precedence of its outermost construct. -/
partial def expr (c : MathCtx) (p : Prec) : MathM (Expr × Nat × Prec) := do
  let pos ← here c
  let first ← leading c p
  operators c p pos first

/-- The arguments of a notation, after its leading constant. -/
partial def literals (c : MathCtx) (info : PrefixInfo) : MathM (Array Expr) := do
  let binders := c.terms[info.term]!.args
  let mut args : Array Expr := Array.replicate binders.size default
  for lit in info.lits do
    match lit with
    | .const token =>
      match ← peek c with
      | some t =>
        if t.text == token then advance
        else fail t.pos s!"expected `{token}`, found `{t.text}`"
      | none => fail c.endPos s!"expected `{token}`, but the formula ends here"
    | .var idx prec =>
      let pos ← here c
      let (e, s, _) ← expr c prec
      args := args.set! idx (← coerceArg c pos e s binders[idx]!)
  return args

/-- An expression that does not start with an infix operator: a parenthesized expression,
a notation, a variable, or a term with its arguments. -/
partial def leading (c : MathCtx) (p : Prec) : MathM (Expr × Nat × Prec) := do
  let some tk ← peek c
    | fail c.endPos "expected an expression, but the formula ends here"
  advance
  if tk.text == "(" then
    let (e, s, _) ← expr c (.num 0)
    match ← peek c with
    | some t =>
      if t.text == ")" then advance
      else fail t.pos s!"expected `)`, found `{t.text}`"
    | none => fail c.endPos "expected `)`, but the formula ends here"
    return (e, s, .max)
  match c.env.consts[tk.text]? with
  | some q =>
    -- a notation constant is never read as a variable or a term (as in mm0-rs)
    match c.env.prefixes[tk.text]? with
    | some info =>
      if !p.le q then
        fail tk.pos s!"`{tk.text}` has precedence {q}, but an expression of precedence {p} or higher is expected here"
      let args ← literals c info
      return (.app info.term args, c.terms[info.term]!.retSort, q)
    | none => fail tk.pos s!"expected an expression, found the operator `{tk.text}`"
  | none =>
    if tk.text == ")" then
      fail tk.pos "expected an expression, found `)`"
    if !isIdent tk.text then
      fail tk.pos s!"unknown token `{tk.text}`"
    -- a variable shadows a term of the same name
    if let some v := findVar c.vars tk.text 0 then
      return (.var v, c.vars[v]!.sort, .max)
    let some t := c.termIds[tk.text]?
      | fail tk.pos s!"unknown variable or term `{tk.text}`"
    let decl := c.terms[t]!
    if decl.args.isEmpty then
      return (.app t #[], decl.retSort, .max)
    if !p.le Prec.app then
      fail tk.pos s!"the application of `{tk.text}` needs parentheses here: an expression of precedence {p} is expected"
    let mut args := Array.mkEmpty decl.args.size
    for b in decl.args do
      let pos ← here c
      let (e, s, _) ← expr c .max
      args := args.push (← coerceArg c pos e s b)
    return (.app t args, decl.retSort, Prec.app)

/-- Infix operators after the expression `lhs`, which starts at `lhsPos`. For an operator
at precedence `q` the grammar is `expression(q) -> expression(q) OP expression(q+1)` if it
is left associative and `expression(q+1) OP expression(q)` if it is right associative. -/
partial def operators (c : MathCtx) (p : Prec) (lhsPos : Nat) (lhs : Expr × Nat × Prec) :
    MathM (Expr × Nat × Prec) := do
  let some tk ← peek c | return lhs
  let (some (.num q), some info) := (c.env.consts[tk.text]?, c.env.infixes[tk.text]?)
    | return lhs
  let (l, ls, level) := lhs
  -- the whole must be an expression(p), and the left operand what the operator asks for
  if !p.le (.num q) || !Prec.le (.num (if info.rassoc then q + 1 else q)) level then
    return lhs
  advance
  let rhsPos ← here c
  let (r, rs, _) ← expr c (.num (if info.rassoc then q else q + 1))
  let decl := c.terms[info.term]!
  let l ← coerceArg c lhsPos l ls decl.args[0]!
  let r ← coerceArg c rhsPos r rs decl.args[1]!
  operators c p lhsPos (.app info.term #[l, r], decl.retSort, .num q)

end

end MathParser

/-- Parses the math string `m`, in the context `c` without its tokens, to an expression
of the sort that `target` asks for. -/
def parseMath (c : MathCtx) (m : MathString) (target : Target) : Except ParseError Expr := do
  let base := m.span.start + 1
  let c := { c with tokens := c.env.tokenize m.text.toUTF8 base, endPos := m.span.stop - 1 }
  let run : MathParser.MathM Expr := do
    let (e, s, _) ← MathParser.expr c (.num 0)
    if let some t ← MathParser.peek c then
      MathParser.fail t.pos s!"expected the end of the formula, found `{t.text}`"
    let start := (c.tokens[0]?.map (·.pos)).getD base
    match target with
    | .any => return e
    | .sort t => MathParser.coerce c start e s t
    | .provable =>
      if (c.sorts[s]?.map (·.mods.isProvable)).getD false then return e
      match c.env.coeProv[s]? with
      | some t => MathParser.coerce c start e s t
      | none =>
        MathParser.fail start s!"this formula has sort `{MathParser.sortName c s}`, which is not provable and has no coercion to a provable sort"
  match run.run 0 with
  | .ok e _ => .ok e
  | .error err _ => .error err

end Whitehead.Mm0
