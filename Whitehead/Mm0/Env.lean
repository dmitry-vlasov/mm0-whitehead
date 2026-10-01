/-
The elaborated form of a `.mm0` specification: sorts, terms and statements with their
formulas as expression trees. This is the environment of the formal specification
(`Env` in `examples/mm0.mm0`, `env` in `mm0-lean/mm0/mm0.lean`), with names kept for
messages and for matching against a proof file.
-/
import Whitehead.Mm0.Syntax

namespace Whitehead.Mm0

/-- An expression: a variable of the enclosing declaration, by index, or a term applied
to arguments. Sorts, terms and variables are referred to by their index in order of
declaration, as in a `.mmb` file. -/
inductive Expr where
  | var (idx : Nat)
  | app (term : Nat) (args : Array Expr)
  deriving BEq, Inhabited, Repr

/-- A variable of a declaration. -/
structure VarDecl where
  /-- `none` for `_` and for the variables that an arrow type stands for. -/
  name : Option String
  sort : Nat
  /-- A bound variable (`{x: s}`), or a dummy. -/
  bound : Bool
  /-- For a regular variable: the bound variables it may depend on, as indices into the
  variable list of the declaration. -/
  deps : Array Nat
  deriving BEq, Inhabited, Repr

structure SortDecl where
  name : String
  mods : SortMods
  deriving Inhabited, Repr

/-- The value of a definition. Its expression refers to the arguments of the definition
by their indices and to the dummies by the indices after them. -/
structure DefValue where
  dummies : Array VarDecl
  expr : Expr
  deriving Inhabited, Repr

structure TermDecl where
  name : String
  args : Array VarDecl
  retSort : Nat
  retDeps : Array Nat
  isDef : Bool
  /-- `none` for a `term`, and for a `def` whose value the specification does not give. -/
  value : Option DefValue
  deriving Inhabited, Repr

structure HypDecl where
  name : Option String
  expr : Expr
  deriving Inhabited, Repr

structure ThmDecl where
  name : String
  isAxiom : Bool
  args : Array VarDecl
  hyps : Array HypDecl
  concl : Expr
  deriving Inhabited, Repr

/-- A declaration, as an index into the table of its kind. -/
inductive DeclRef where
  | sort (idx : Nat)
  | term (idx : Nat)
  | thm (idx : Nat)
  deriving BEq, Inhabited, Repr

structure Env where
  sorts : Array SortDecl := #[]
  terms : Array TermDecl := #[]
  thms : Array ThmDecl := #[]
  /-- The declarations in the order of the specification. -/
  order : Array DeclRef := #[]
  deriving Inhabited

/-- An expression as an s-expression: `(imp a (not b))`, a term without arguments as its
bare name. `names` are the names of the variables. -/
partial def Env.exprString (env : Env) (names : Array String) : Expr → String
  | .var i => names[i]?.getD s!"v{i}"
  | .app t args =>
    let name := (env.terms[t]?.map (·.name)).getD s!"t{t}"
    if args.isEmpty then name
    else args.foldl (fun acc a => acc ++ " " ++ env.exprString names a) ("(" ++ name) ++ ")"

end Whitehead.Mm0
