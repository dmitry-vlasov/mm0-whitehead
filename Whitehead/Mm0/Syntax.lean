/-
The abstract syntax of a `.mm0` specification file, as produced by the primary parser.

This follows the grammar in `mm0.md` production by production. Math strings are kept as
raw text here; interpreting them needs the notations declared in the file and is the job
of the secondary parser.
-/
namespace Whitehead.Mm0

/-- A half-open range `[start, stop)` of byte offsets into the source file. -/
structure Span where
  start : Nat
  stop : Nat
  deriving Repr, BEq, Inhabited

structure Ident where
  name : String
  span : Span
  deriving Repr, Inhabited

/-- The text between two `$`, not yet tokenized. `span` includes both `$`. -/
structure MathString where
  text : String
  span : Span
  deriving Repr, Inhabited

/-- The modifiers of a `sort` statement. -/
structure SortMods where
  isPure : Bool := false
  isStrict : Bool := false
  isProvable : Bool := false
  isFree : Bool := false
  deriving Repr, BEq, Inhabited

/-- `precedence-lvl ::= number | 'max'` -/
inductive Prec where
  | num (n : Nat)
  | max
  deriving Repr, BEq, Inhabited

/-- `type ::= identifier (identifier)*`: a sort and the bound variables it depends on. -/
structure DepType where
  sort : Ident
  deps : Array Ident
  deriving Repr, Inhabited

/-- What stands after the `:` of a binder, or between the `>` of an arrow type. -/
inductive BinderType where
  | type (t : DepType)
  | formula (f : MathString)
  deriving Repr, Inhabited

/-- A name in a binder: `x`, the anonymous `_` (`name = none`), or a dummy `.x`. -/
structure LocalName where
  name : Option String
  dummy : Bool
  span : Span
  deriving Repr, Inhabited

/-- `{x y: s}` (`curly`, bound variables) or `(ph ps: s x)` / `(h: $ ... $)`. -/
structure Binder where
  curly : Bool
  names : Array LocalName
  type : BinderType
  span : Span
  deriving Repr, Inhabited

inductive AssertKind where
  | ax
  | thm
  deriving Repr, BEq, Inhabited

inductive SimpleNotaKind where
  | pfx
  | infl
  | infr
  deriving Repr, BEq, Inhabited

/-- `prec-constant ::= '(' constant ':' precedence-lvl ')'` -/
structure PrecConst where
  const : MathString
  prec : Prec
  deriving Repr, Inhabited

/-- `notation-literal ::= prec-constant | identifier` -/
inductive NotaLit where
  | const (c : PrecConst)
  | var (x : Ident)
  deriving Repr, Inhabited

inductive InoutArg where
  | ident (x : Ident)
  | math (m : MathString)
  deriving Repr, Inhabited

inductive StmtKind where
  /-- `pure strict provable free sort name;` -/
  | sort (mods : SortMods) (name : Ident)
  /-- `term name binders: a1 > ... > an > ret;` -/
  | term (name : Ident) (binders : Array Binder) (args : Array DepType) (ret : DepType)
  /-- `axiom name binders: h1 > ... > hn > $ concl $;`, and the same for `theorem`.
  An element of `hyps` that is a type is an anonymous variable, as in a `term`. -/
  | assert (kind : AssertKind) (name : Ident) (binders : Array Binder)
      (hyps : Array BinderType) (concl : MathString)
  /-- `def name binders: a1 > ... > an > ret = $ value $;`; the value may be omitted.
  The arrows are not in the grammar of `mm0.md`, which has a single `type` here, but
  `examples/hol.mm0` uses them and `mm0-c` accepts them (see `docs/DESIGN.md`). -/
  | defn (name : Ident) (binders : Array Binder) (args : Array DepType) (ret : DepType)
      (value : Option MathString)
  /-- `delimiter $ both $;` or `delimiter $ left $ $ right $;` -/
  | delimiter (left : MathString) (right : Option MathString)
  /-- `prefix term: $tk$ prec p;`, and the same for `infixl`, `infixr`. -/
  | simpleNota (kind : SimpleNotaKind) (term : Ident) (const : MathString) (prec : Prec)
  /-- `coercion term: src > tgt;` -/
  | coercion (term : Ident) (src : Ident) (tgt : Ident)
  /-- `notation term binders: ret = ($tk$: p) lit ...;` -/
  | genNota (term : Ident) (binders : Array Binder) (ret : DepType) (head : PrecConst)
      (lits : Array NotaLit)
  /-- `input kind: ...;` (`isInput`) or `output kind: ...;` -/
  | inout (isInput : Bool) (kind : Ident) (args : Array InoutArg)
  /-- `import "path";` — an extension of `mm0-rs`, not in `mm0.md`. The path is relative
  to the directory of the file that contains the statement; `pathSpan` is the span of
  the string literal. Imports are resolved by `Whitehead.Mm0.load`. -/
  | importFile (path : String) (pathSpan : Span)
  deriving Repr, Inhabited

structure Stmt where
  kind : StmtKind
  span : Span
  deriving Repr, Inhabited

/-- An error of the lexer or the primary parser, at a byte offset of the source. -/
structure ParseError where
  pos : Nat
  msg : String
  deriving Repr, BEq, Inhabited

end Whitehead.Mm0
