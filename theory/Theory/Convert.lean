/-
From the production engine's database (`Whitehead/Prove/Db.lean`) to the model: the
flat expressions become trees, the assertions below the task's limit become the
database, the task becomes the statement. For the driver and the differential test
(`docs/THEORY.md`, "The link to the production engine").
-/
import Whitehead.Prove.Db
import Theory.Search

namespace Theory.Convert



/-- A production type: a sort and the name bit in one number. -/
def ty (t : Nat) : Ty := ⟨Whitehead.Prove.Ty.sort t, Whitehead.Prove.Ty.isName t⟩

mutual
/-- The expression that starts at node `i` of a flat expression, and the node after it. -/
partial def expAt (e : Whitehead.Prove.Exp) (i : Nat) : Exp × Nat :=
  let n := e.nodes[i]!
  if Whitehead.Prove.Node.isVar n then (.var ⟨Whitehead.Prove.Node.varId n, ty (Whitehead.Prove.Node.ty n)⟩, i + 1)
  else if Whitehead.Prove.Node.isConst n then (.const (Whitehead.Prove.Node.appId n - Whitehead.Prove.Node.constBase) (ty (Whitehead.Prove.Node.ty n)), i + 1)
  else
    let (args, next) := argsUpTo e (i + 1) (i + 1 + Whitehead.Prove.Node.len n) []
    (.app (Whitehead.Prove.Node.appId n) (ty (Whitehead.Prove.Node.ty n)) args, next)
partial def argsUpTo (e : Whitehead.Prove.Exp) (j stop : Nat) (acc : List Exp) : List Exp × Nat :=
  if j < stop then
    let (a, j') := expAt e j
    argsUpTo e j' stop (acc ++ [a])
  else (acc, j)
end

def exp (e : Whitehead.Prove.Exp) : Exp := (expAt e 0).1

def var (v : Nat) : Var := ⟨Whitehead.Prove.Node.varId v, ty (Whitehead.Prove.Node.ty v)⟩

def assertion (a : Whitehead.Prove.Assertion) : Assertion :=
  let vars := a.vars.toList.map var
  { vars, pairs := a.disjs.toList.map fun (i, j) => (vars[i]!, vars[j]!),
    hyps := a.hyps.toList.map exp, concl := exp a.concl }

/-- The assertions a task may use, as the database, with their names. The conversion
rules of a file with defs (`pseudo`) are left out: the first variant of the theory has
no definitions (`docs/THEORY.md`, decision 6). -/
def database (db : Whitehead.Prove.Db) (task : Whitehead.Prove.Task) : Database × Array String :=
  let usable := db.asserts.toList.filter fun a =>
    a.rank < Whitehead.Prove.rankLimit task.limit && a.pseudo.isNone
  ({ asserts := usable.map assertion }, (usable.map (·.name)).toArray)

/-- The task as the statement. A sort allows dummies unless it is `strict` or `free`
(the sort table of the proof file). -/
def statement (db : Whitehead.Prove.Db) (task : Whitehead.Prove.Task) : Statement :=
  { consts := { ty := fun k => ty (task.consts[k]!).ty, deps := fun k => (task.consts[k]!).names.toList.toFinset },
    dummies := fun s => match db.file.sorts[s]? with
      | some d => !d.isStrict && !d.isFree
      | none => false,
    hyps := task.premises.toList.map exp, concl := exp task.goal }

/-- An expression for a reader: terms by name, constants as `c0`, variables as `?7`. -/
partial def expText (terms : Array String) : Exp → String
  | .var v => s!"?{v.id}"
  | .const k _ => s!"c{k}"
  | .app f _ [] => terms[f]?.getD s!"t{f}"
  | .app f _ args => s!"({terms[f]?.getD s!"t{f}"} {" ".intercalate (args.map (expText terms))})"

/-- A proof tree for a reader: `(name children)`, a leaf as its hypothesis. -/
partial def proofText (names terms : Array String) : PTree → String
  | .hyp e => s!"[{expText terms e}]"
  | .step _ a _ [] => names[a]?.getD s!"a{a}"
  | .step _ a _ cs => s!"({names[a]?.getD s!"a{a}"} {" ".intercalate (cs.map (proofText names terms))})"

end Theory.Convert
