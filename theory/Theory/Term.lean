/-
The term language of MM0 for the theory (`docs/THEORY.md`, "The model"): sorts, types
with the "names only" bit, variables, constants for the variables of the statement
being proved, and expressions. The production engine's `Exp` (`Whitehead/Prove/Exp.lean`)
is a flat array of the same nodes; a converter (`Theory/Convert.lean`) maps it here.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Nat.Pairing

namespace Theory

/-- A type: a sort, and whether only names — bound variables — have it. -/
structure Ty where
  sort : ℕ
  name : Bool
  deriving DecidableEq, Repr, Inhabited

/-- May an expression of type `e` stand where a variable of type `v` stands? The same
sort; and where a name is wanted, only a name. This is the typing of substitutions of
the 2017 paper (section 2.2), with "names of sort `s`" a subtype of `s`
(`DESIGN.md`, "Where MM0 differs", condition 1). -/
def Ty.fits (v e : Ty) : Prop := v.sort = e.sort ∧ (v.name = true → e.name = true)

instance : DecidableRel Ty.fits := fun v e => by unfold Ty.fits; infer_instance

theorem Ty.fits_refl (t : Ty) : t.fits t := ⟨rfl, fun h => h⟩

theorem Ty.fits_trans {a b c : Ty} (h₁ : a.fits b) (h₂ : b.fits c) : a.fits c :=
  ⟨h₁.1.trans h₂.1, fun h => h₂.2 (h₁.2 h)⟩

/-- A variable of the search: replaceable, with its type. -/
structure Var where
  id : ℕ
  ty : Ty
  deriving DecidableEq, Repr, Inhabited

/-- A number for a variable, distinct for distinct variables: the closing of a proof
names its dummies by it. -/
def Var.code (v : Var) : ℕ := Nat.pair v.id (Nat.pair v.ty.sort (if v.ty.name then 1 else 0))

theorem Var.code_injective : Function.Injective Var.code := by
  intro a b h
  obtain ⟨i, s, n⟩ := a
  obtain ⟨i', s', n'⟩ := b
  simp only [Var.code, Nat.pair_eq_pair] at h
  obtain ⟨rfl, rfl, h⟩ := h
  cases n <;> cases n' <;> simp_all

/-- Variables are ordered, by number, then sort, then the name bit: the domain of a
substitution is listed in this order. -/
instance : LinearOrder Var :=
  LinearOrder.lift' (fun v : Var => toLex (v.id, toLex (v.ty.sort, v.ty.name))) fun a b h => by
    obtain ⟨i, s, n⟩ := a
    obtain ⟨i', s', n'⟩ := b
    simp only [toLex_inj, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl

/-- An expression: a variable; a constant — a variable of the statement being proved,
which is not replaceable; or the application of a term symbol. An application carries
its type, as the production engine's nodes do; an application is never of a name type
(`WF` below). -/
inductive Exp where
  | var (v : Var)
  | const (k : ℕ) (ty : Ty)
  | app (f : ℕ) (ty : Ty) (args : List Exp)
  deriving Repr

instance : Inhabited Exp := ⟨.const 0 default⟩

namespace Exp

mutual
def beq : Exp → Exp → Bool
  | var v, var w => decide (v = w)
  | const k t, const k' t' => decide (k = k') && decide (t = t')
  | app f t as, app f' t' as' => decide (f = f') && decide (t = t') && beqList as as'
  | _, _ => false
def beqList : List Exp → List Exp → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false
end

mutual
theorem beq_iff : ∀ a b : Exp, beq a b = true ↔ a = b
  | var v, var w => by simp [beq]
  | var _, const _ _ | var _, app _ _ _ | const _ _, var _ | const _ _, app _ _ _
  | app _ _ _, var _ | app _ _ _, const _ _ => by simp [beq]
  | const k t, const k' t' => by simp [beq]
  | app f t as, app f' t' as' => by
    simp only [beq, Bool.and_eq_true, decide_eq_true_eq, app.injEq]
    rw [beqList_iff]
    tauto
theorem beqList_iff : ∀ as bs : List Exp, beqList as bs = true ↔ as = bs
  | [], [] => by simp [beqList]
  | [], _ :: _ | _ :: _, [] => by simp [beqList]
  | a :: as, b :: bs => by
    simp only [beqList, Bool.and_eq_true, List.cons.injEq]
    rw [beq_iff, beqList_iff]
end

instance : DecidableEq Exp := fun a b =>
  if h : beq a b = true then isTrue ((beq_iff a b).1 h) else isFalse (fun e => h ((beq_iff a b).2 e))

/-- The type of an expression. -/
def ty : Exp → Ty
  | var v => v.ty
  | const _ t => t
  | app _ t _ => t

/-- A name: a variable or a constant, what a name type may be given. -/
def IsName : Exp → Prop
  | var _ => True
  | const _ _ => True
  | app _ _ _ => False

instance : DecidablePred IsName := fun e => by
  cases e <;> simp only [IsName] <;> infer_instance

mutual
/-- The variables of an expression. -/
def vars : Exp → Finset Var
  | var v => {v}
  | const _ _ => ∅
  | app _ _ args => varsList args
def varsList : List Exp → Finset Var
  | [] => ∅
  | e :: es => vars e ∪ varsList es
end

mutual
/-- The constants of an expression, with their types. -/
def consts : Exp → Finset (ℕ × Ty)
  | var _ => ∅
  | const k t => {(k, t)}
  | app _ _ args => constsList args
def constsList : List Exp → Finset (ℕ × Ty)
  | [] => ∅
  | e :: es => consts e ∪ constsList es
end

mutual
/-- The number of nodes. -/
def size : Exp → ℕ
  | var _ => 1
  | const _ _ => 1
  | app _ _ args => sizeList args + 1
def sizeList : List Exp → ℕ
  | [] => 0
  | e :: es => size e + sizeList es
end

mutual
/-- The variables of an expression renamed: `id ↦ base + id`. The assertions' own
variables are renamed this way when an assertion is applied, so that each application
has variables of its own (the 2017 paper, section 3.1). -/
def rename (base : ℕ) : Exp → Exp
  | var v => var ⟨base + v.id, v.ty⟩
  | const k t => const k t
  | app f t args => app f t (renameList base args)
def renameList (base : ℕ) : List Exp → List Exp
  | [] => []
  | e :: es => rename base e :: renameList base es
end

end Exp

/-- The constants of a statement: the type of each, and for a regular one the name
constants it is declared to depend on (`(ph: wff x)`: `deps ph = {x}`). -/
structure Consts where
  ty : ℕ → Ty
  deps : ℕ → Finset ℕ

/-- The names that occur in `e`, for the conditions on bound variables: its variables
and constants of a name type, and the names its constants depend on (`DESIGN.md`,
"Where MM0 differs", condition 2: "occurs" includes the declared dependencies). -/
def Consts.names (c : Consts) (e : Exp) : Finset Exp :=
  (e.vars.filter (·.ty.name = true)).image Exp.var ∪
  (e.consts.filter (·.2.name = true)).image (fun p => Exp.const p.1 p.2) ∪
  e.consts.biUnion (fun p => (c.deps p.1).image (fun m => Exp.const m (c.ty m)))

theorem Consts.mem_names (c : Consts) (x e : Exp) :
    x ∈ c.names e ↔ (∃ v ∈ e.vars, v.ty.name = true ∧ x = .var v) ∨
      (∃ p ∈ e.consts, p.2.name = true ∧ x = .const p.1 p.2) ∨
      (∃ p ∈ e.consts, ∃ m ∈ c.deps p.1, x = .const m (c.ty m)) := by
  simp only [Consts.names, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_biUnion]
  aesop

/-- A name is a variable or a constant: an application never occurs as a name. -/
theorem Consts.app_not_mem_names (c : Consts) (f : ℕ) (t : Ty) (args : List Exp) (e : Exp) :
    Exp.app f t args ∉ c.names e := by
  simp [Consts.mem_names]

/-- Well-formed expressions of a signature: the argument types and the result sort of
every term symbol. -/
structure Signature where
  args : ℕ → List Ty
  sort : ℕ → ℕ

mutual
/-- An expression respects the signature: an application has the sort of its symbol
and is not of a name type, and each argument fits the declared type. -/
def Signature.WF (sig : Signature) : Exp → Prop
  | .var _ => True
  | .const _ _ => True
  | .app f t args => t = ⟨sig.sort f, false⟩ ∧ sig.WFArgs (sig.args f) args
def Signature.WFArgs (sig : Signature) : List Ty → List Exp → Prop
  | [], [] => True
  | t :: ts, e :: es => t.fits e.ty ∧ sig.WF e ∧ sig.WFArgs ts es
  | _, _ => False
end

end Theory
