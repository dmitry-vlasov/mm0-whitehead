/-
A decoded `.mmb` file (`Whitehead.Mmb.MmbFile`) as the machine's input (`Verifier.File`):
for the differential test of milestone V5. Not part of the proofs: what it reads is the
reader's, which stays trusted (`docs/VERIFIER-THEORY.md`).
-/
import Verifier.Check
import Whitehead.Mmb.Reader

namespace Verifier

open Whitehead.Mmb (MmbFile Arg SortData)

def sortDataOf (s : SortData) : mm0.sort_data :=
  { pure := s.isPure, strict := s.isStrict, provable := s.isProvable, free := s.isFree }

/-- The bound variables of a dependency mask, bits 0 to 54. -/
def depsOf (mask : UInt64) : Finset ℕ :=
  ((List.range 55).filter fun k => (mask >>> k.toUInt64) &&& 1 == 1).toFinset

def binderOf (a : Arg) : Binder := ⟨a.sort, a.bound, depsOf a.deps⟩

/-- The file, or the first stream that does not decode. -/
def fileOf (f : MmbFile) : Except String File := do
  let terms ← (List.range f.terms.size).mapM fun t => do
    let args := (f.termArgs t).toList.map binderOf
    let defn ← if f.terms[t]!.isDef then
        match f.termUnifyCmds t with
        | .ok us => pure (some us.toList)
        | .error e => throw s!"term {t}: {e.msg}"
      else pure none
    pure ({ args, ret := binderOf (f.termRet t), defn } : TermDecl)
  let thms ← (List.range f.thms.size).mapM fun t => do
    let us ← match f.thmUnifyCmds t with
      | .ok us => pure us.toList
      | .error e => throw s!"theorem {t}: {e.msg}"
    pure ({ args := (f.thmArgs t).toList.map binderOf, unify := us } : ThmDecl)
  let stmts ← f.stmts.toList.mapM fun s => do
    let body ← match f.proofCmds s with
      | .ok b => pure b.toList
      | .error e => throw s!"statement at 0x{Whitehead.Mmb.hex s.pos}: {e.msg}"
    let kind : StmtKind := match s.kind with
      | .sort => .sort
      | .termDef isLocal => if f.terms[s.index]!.isDef then .defn isLocal else .term
      | .ax => .ax
      | .thm isLocal => .thm isLocal
    pure ({ kind, body } : Stmt)
  pure { sorts := f.sorts.toList.map sortDataOf, terms, thms, stmts }

/-- The reference verdict statement by statement: the index of the first statement the
machine rejects (`stmts.length` for the final counts), or none. -/
def firstFailure (f : File) : Option ℕ := go f.stmts 0 0 0 0
where
  go : List Stmt → ℕ → ℕ → ℕ → ℕ → Option ℕ
    | [], _, ns, nt, nh =>
      if ns = f.sorts.length ∧ nt = f.terms.length ∧ nh = f.thms.length then none else some f.stmts.length
    | s :: ss, i, ns, nt, nh =>
      if okOne s ns nt nh then
        match s.kind with
        | .sort => go ss (i + 1) (ns + 1) nt nh
        | .term | .defn _ => go ss (i + 1) ns (nt + 1) nh
        | .ax | .thm _ => go ss (i + 1) ns nt (nh + 1)
      else some i
  okOne (s : Stmt) (ns nt nh : ℕ) : Bool :=
    let c (b : Bool) : Ctx := ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, b⟩
    match s.kind with
    | .sort => decide (s.body = []) && decide (ns < f.sorts.length)
    | .term => decide (s.body = []) && match f.terms[nt]? with
      | some d => decide (d.defn = none) && termOkB (c false) d false []
      | none => false
    | .defn isLocal => match f.terms[nt]? with
      | some d => d.defn.isSome && termOkB (c true) d isLocal s.body
      | none => false
    | .ax => match f.thms[nh]? with
      | some d => thmOkB (c false) d true s.body
      | none => false
    | .thm _ => match f.thms[nh]? with
      | some d => thmOkB (c false) d false s.body
      | none => false

end Verifier
