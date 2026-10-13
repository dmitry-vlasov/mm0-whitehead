/-
From the production engine's database (`Whitehead/Prove/Db.lean`) to the model: the
flat expressions become trees, the assertions below the task's limit become the
database, the task becomes the statement. For the driver and the differential test
(`docs/THEORY.md`, "The link to the production engine").
-/
import Whitehead.Prove.Db
import Theory.Search
import Theory.Rules

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

/-- The language of the file: its sorts and which are provable; its terms — those of
the file, before the judgment terms a file with definitions has — with their
signature; and the production engine's judgment sort (`judgmentTy`). -/
def language (db : Whitehead.Prove.Db) : Language :=
  { sorts := db.file.sorts.size,
    provable := fun s => match db.file.sorts[s]? with | some d => d.isProvable | none => false,
    terms := if db.defs.isEmpty then db.terms.size else db.conv.base,
    sig := { args := fun f => match db.terms[f]? with | some info => info.args.toList.map ty | none => [],
             sort := fun f => match db.terms[f]? with | some info => Whitehead.Prove.Ty.sort info.ty | none => 0 },
    judg := Whitehead.Prove.Ty.sort Whitehead.Prove.judgmentTy }

/-- The definitions of the file, in the order of the terms. -/
def defs (db : Whitehead.Prove.Db) : List Def :=
  db.defs.toList.filterMap fun t =>
    match db.terms[t]? with
    | some info =>
      match info.value with
      | some v =>
        some { term := t, ty := ty info.ty,
               args := (List.range info.args.size).map fun k => ⟨k, ty info.args[k]!⟩,
               dummies := v.dummies.toList.map var, value := exp v.expr }
      | none => none
    | none => none

/-- The assertions a task may use, as the database, with their names: the file's and,
for a file with definitions, the rules of the conversion judgment (`pseudo`), which
the production engine lays out as the model does (`Rules.all`; checked by
`rulesMismatch`); and the definitions. -/
def database (db : Whitehead.Prove.Db) (task : Whitehead.Prove.Task) : Database × Array String :=
  let usable := db.asserts.toList.filter fun a => a.rank < Whitehead.Prove.rankLimit task.limit
  ({ asserts := usable.map assertion, defs := defs db }, (usable.map (·.name)).toArray)

/-- Two assertions, the pairs in any order. -/
def assertionEqv (A B : Assertion) : Bool :=
  A.vars == B.vars && A.hyps == B.hyps && A.concl == B.concl && A.pairs.isPerm B.pairs

/-- The rules the model builds for the file against the rules the file has: `none` when
they agree rule for rule, else the first difference. -/
def rulesMismatch (db : Whitehead.Prove.Db) : Option String :=
  let model := Rules.all (language db) (defs db)
  let file := db.asserts.toList.filter (·.pseudo.isSome)
  if model.length != file.length then some s!"{model.length} rules in the model, {file.length} in the file"
  else (model.zip file).findSome? fun ((k, A), a) =>
    if assertionEqv A (assertion a) then none
    else some s!"rule {a.name} ({repr k}) differs: model vars {A.vars.length}, pairs {A.pairs.length}, \
      file vars {(assertion a).vars.length}, pairs {(assertion a).pairs.length}"

/-- What keeps a definition of the file from being well-formed (`Def.WF`); nothing, as
a rule. -/
def defsFaults (db : Whitehead.Prove.Db) : List String :=
  (defs db).filterMap fun D =>
    let name := (db.terms[D.term]?.map (·.name)).getD s!"t{D.term}"
    if !(D.value.vars ⊆ (D.args ++ D.dummies).toFinset) then some s!"{name}: the value has a variable that is no binder"
    else if D.dummies.any (fun y => !(y ∈ D.value.vars)) then some s!"{name}: a dummy does not occur in the value"
    else if D.dummies.any (fun y => !y.ty.name) then some s!"{name}: a dummy is not of a name type"
    else if D.ty.name then some s!"{name}: the result is of a name type"
    else if D.value.ty.sort != D.ty.sort then some s!"{name}: the value is not of the result's sort"
    else if !(D.args ++ D.dummies).Nodup then some s!"{name}: two binders are the same"
    else none

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
  | .hyp h e => s!"[h{h}: {expText terms e}]"
  | .step _ a _ [] => names[a]?.getD s!"a{a}"
  | .step _ a _ cs => s!"({names[a]?.getD s!"a{a}"} {" ".intercalate (cs.map (proofText names terms))})"

end Theory.Convert
