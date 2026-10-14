/-
An elaborated specification (`Whitehead.Mm0.Env`) as an environment of the semantics,
for the match of milestone V6. Trusted, like the `.mm0` front end it reads. Three
choices of names and order, none of which the semantics depends on:
- terms are numbered as the proof file numbers them (`termMap`, the file's number for
  each term of the specification, as `matchSpec` builds it: term ids are names);
- a def's dummies are numbered by first occurrence in the value, read left to right,
  as the proof file's unify stream numbers them, and an unused dummy is dropped;
- a theorem's hypotheses are listed last first, as the stream lists them.
-/
import Verifier.Extend
import Verifier.OfMmb
import Whitehead.Mm0.Env

namespace Verifier

open Whitehead.Mm0 (Expr VarDecl SortMods)

def sortDataOfMods (m : SortMods) : mm0.sort_data :=
  { pure := m.isPure, strict := m.isStrict, provable := m.isProvable, free := m.isFree }

def binderOfVar (v : VarDecl) : mm0.binder :=
  if v.bound then .bound v.sort else .reg v.sort v.deps.toList.toFinset

partial def exprOf (termMap : Array ℕ) (ren : ℕ → ℕ) : Expr → mm0.sexpr
  | .var i => .var (ren i)
  | .app t args => mm0.sexpr.app (termMap[t]?.getD t) (args.toList.map (exprOf termMap ren))

/-- The dummies of a value in order of first occurrence, read left to right. -/
partial def dummyOrder (nargs : ℕ) : Expr → Array ℕ → Array ℕ
  | .var i, acc => if i ≥ nargs && !acc.contains i then acc.push i else acc
  | .app _ args, acc => args.foldl (fun acc a => dummyOrder nargs a acc) acc

def specEnv (env : Whitehead.Mm0.Env) (termMap : Array ℕ) : mm0.env :=
  env.order.toList.map fun d =>
    match d with
    | .sort i => mm0.decl.sort i (sortDataOfMods env.sorts[i]!.mods)
    | .term i =>
      let t := env.terms[i]!
      let args := t.args.toList.map binderOfVar
      let ret : mm0.dep_type := (t.retSort, t.retDeps.toList.toFinset)
      let id := termMap[i]?.getD i
      if t.isDef then
        mm0.decl.defn id args ret (t.value.map fun v =>
          let order := dummyOrder t.args.size v.expr #[]
          let ren := fun j => if j < t.args.size then j else t.args.size + (order.idxOf? j).getD 0
          (order.toList.map fun j => (v.dummies[j - t.args.size]!).sort, exprOf termMap ren v.expr))
      else mm0.decl.term id args ret
    | .thm i =>
      let t := env.thms[i]!
      let args := t.args.toList.map binderOfVar
      let hyps := (t.hyps.toList.map fun h => exprOf termMap id h.expr).reverse
      if t.isAxiom then mm0.decl.ax args hyps (exprOf termMap id t.concl)
      else mm0.decl.thm args hyps (exprOf termMap id t.concl)

/-- The file's number for each term of the specification: its non-local term
statements in order. -/
def termMapOf (f : Whitehead.Mmb.MmbFile) : Array ℕ :=
  f.stmts.foldl (init := #[]) fun acc s =>
    match s.kind with
    | .termDef false => acc.push s.index
    | _ => acc

/-- The file's local flags, one per statement. -/
def localFlags (f : Whitehead.Mmb.MmbFile) : List Bool :=
  f.stmts.toList.map fun s => match s.kind with
    | .termDef l | .thm l => l
    | _ => false

end Verifier
