/-
Prints the syntax tree of a `.mm0` file back as `.mm0` text, one statement per line.

The output is normalized (layout and comments are not kept) and parses back to the same
tree, source positions aside. Math strings are printed verbatim.
-/
import Whitehead.Mm0.Syntax

namespace Whitehead.Mm0

def Prec.print : Prec → String
  | .num n => toString n
  | .max => "max"

def MathString.print (m : MathString) : String :=
  "$" ++ m.text ++ "$"

def DepType.print (t : DepType) : String :=
  t.deps.foldl (fun acc d => acc ++ " " ++ d.name) t.sort.name

def BinderType.print : BinderType → String
  | .type t => t.print
  | .formula f => f.print

def LocalName.print (n : LocalName) : String :=
  (if n.dummy then "." else "") ++ n.name.getD "_"

def Binder.print (b : Binder) : String :=
  let names := " ".intercalate (b.names.toList.map LocalName.print)
  let body := names ++ ": " ++ b.type.print
  if b.curly then "{" ++ body ++ "}" else "(" ++ body ++ ")"

/-- ` b1 b2 ...`: each binder preceded by a space, so that it follows a name directly. -/
def printBinders (bs : Array Binder) : String :=
  bs.foldl (fun acc b => acc ++ " " ++ b.print) ""

def PrecConst.print (c : PrecConst) : String :=
  "(" ++ c.const.print ++ ": " ++ c.prec.print ++ ")"

def NotaLit.print : NotaLit → String
  | .const c => c.print
  | .var x => x.name

def InoutArg.print : InoutArg → String
  | .ident x => x.name
  | .math m => m.print

def SortMods.print (m : SortMods) : String :=
  (if m.isPure then "pure " else "") ++ (if m.isStrict then "strict " else "") ++
  (if m.isProvable then "provable " else "") ++ (if m.isFree then "free " else "")

def SimpleNotaKind.print : SimpleNotaKind → String
  | .pfx => "prefix"
  | .infl => "infixl"
  | .infr => "infixr"

/-- A string literal that the lexer reads back as `s`. -/
def quoteString (s : String) : String :=
  let body := s.foldl (init := "") fun acc c =>
    if c == '\\' then acc ++ "\\\\"
    else if c == '"' then acc ++ "\\\""
    else if c == '\n' then acc ++ "\\n"
    else if c == '\r' then acc ++ "\\r"
    else acc.push c
  "\"" ++ body ++ "\""

def Stmt.print (s : Stmt) : String :=
  match s.kind with
  | .sort mods name => mods.print ++ "sort " ++ name.name ++ ";"
  | .term name binders args ret =>
    let types := " > ".intercalate ((args.push ret).toList.map DepType.print)
    "term " ++ name.name ++ printBinders binders ++ ": " ++ types ++ ";"
  | .assert kind name binders hyps concl =>
    let kw := match kind with
      | .ax => "axiom"
      | .thm => "theorem"
    let types := " > ".intercalate (hyps.toList.map BinderType.print ++ [concl.print])
    kw ++ " " ++ name.name ++ printBinders binders ++ ": " ++ types ++ ";"
  | .defn name binders args ret value =>
    let types := " > ".intercalate ((args.push ret).toList.map DepType.print)
    let value := match value with
      | some v => " = " ++ v.print
      | none => ""
    "def " ++ name.name ++ printBinders binders ++ ": " ++ types ++ value ++ ";"
  | .delimiter left right =>
    let right := match right with
      | some r => " " ++ r.print
      | none => ""
    "delimiter " ++ left.print ++ right ++ ";"
  | .simpleNota kind term const prec =>
    kind.print ++ " " ++ term.name ++ ": " ++ const.print ++ " prec " ++ prec.print ++ ";"
  | .coercion term src tgt =>
    "coercion " ++ term.name ++ ": " ++ src.name ++ " > " ++ tgt.name ++ ";"
  | .genNota term binders ret head lits =>
    let lits := lits.foldl (fun acc l => acc ++ " " ++ l.print) ""
    "notation " ++ term.name ++ printBinders binders ++ ": " ++ ret.print ++ " = " ++
      head.print ++ lits ++ ";"
  | .inout isInput kind args =>
    let args := args.foldl (fun acc a => acc ++ " " ++ a.print) ""
    (if isInput then "input " else "output ") ++ kind.name ++ ":" ++ args ++ ";"
  | .importFile path _ => "import " ++ quoteString path ++ ";"

/-- All statements, one per line. -/
def printStmts (stmts : Array Stmt) : String :=
  stmts.foldl (fun acc s => acc ++ s.print ++ "\n") ""

end Whitehead.Mm0
