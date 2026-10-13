/-
Substitutions: finite support, application, composition, typing, instances, and the
equational form that the join of substitutions is defined from (the draft, Definitions
2.1 and 2.6).
-/
import Mathlib.Data.Finset.Sort
import Theory.Term

namespace Theory

/-- A substitution: a map on variables that moves finitely many of them. `dom` is
exactly the set of variables it moves, so that two substitutions with the same map are
equal (`Subst.ext`). -/
structure Subst where
  f : Var → Exp
  dom : Finset Var
  hdom : ∀ v, v ∈ dom ↔ f v ≠ .var v

namespace Subst

theorem ext {θ η : Subst} (h : θ.f = η.f) : θ = η := by
  cases θ with | mk f d hd =>
  cases η with | mk f' d' hd' =>
  simp only at h
  subst h
  have : d = d' := Finset.ext fun v => by rw [hd, hd']
  subst this
  rfl

theorem f_eq_of_not_mem {θ : Subst} {v : Var} (h : v ∉ θ.dom) : θ.f v = .var v := by
  by_contra h'
  exact h ((θ.hdom v).2 h')

/-- The identity. -/
def id : Subst where
  f := Exp.var
  dom := ∅
  hdom := fun v => by simp

instance : Inhabited Subst := ⟨Subst.id⟩

/-- A substitution from a function that is the identity outside a finite set. -/
def ofFun (cands : Finset Var) (g : Var → Exp) (h : ∀ v, v ∉ cands → g v = .var v) : Subst where
  f := g
  dom := cands.filter fun v => g v ≠ .var v
  hdom := fun v => by
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    intro hv
    by_contra hc
    exact hv (h v hc)

/-- The substitution that moves one variable. -/
def single (v : Var) (e : Exp) : Subst where
  f := fun w => if w = v then e else .var w
  dom := if e = .var v then ∅ else {v}
  hdom := fun w => by
    by_cases hw : w = v
    · subst hw; by_cases he : e = .var w <;> simp [he]
    · by_cases he : e = .var v <;> simp [he, hw]

mutual
/-- Application to an expression. -/
def apply (θ : Subst) : Exp → Exp
  | .var v => θ.f v
  | .const k t => .const k t
  | .app f t args => .app f t (applyList θ args)
def applyList (θ : Subst) : List Exp → List Exp
  | [] => []
  | e :: es => apply θ e :: applyList θ es
end

@[simp] theorem apply_var (θ : Subst) (v : Var) : θ.apply (.var v) = θ.f v := by
  simp [apply]

@[simp] theorem apply_const (θ : Subst) (k : ℕ) (t : Ty) : θ.apply (.const k t) = .const k t := by
  simp [apply]

/-- Composition: `(θ.comp η).apply e = θ.apply (η.apply e)`, so `η` is applied first.
The 2017 paper writes it `θ ∘ η`. -/
def comp (θ η : Subst) : Subst where
  f := fun v => θ.apply (η.f v)
  dom := (θ.dom ∪ η.dom).filter fun v => θ.apply (η.f v) ≠ .var v
  hdom := fun v => by
    simp only [Finset.mem_filter, Finset.mem_union, and_iff_right_iff_imp]
    intro h
    by_contra h'
    rw [not_or] at h'
    rw [f_eq_of_not_mem h'.2, apply_var, f_eq_of_not_mem h'.1] at h
    exact h rfl

mutual
theorem apply_comp (θ η : Subst) : ∀ e, (θ.comp η).apply e = θ.apply (η.apply e)
  | .var v => by simp [apply, comp]
  | .const k t => by simp [apply]
  | .app f t args => by simp [apply, applyList_comp θ η args]
theorem applyList_comp (θ η : Subst) : ∀ es, (θ.comp η).applyList es = θ.applyList (η.applyList es)
  | [] => by simp [applyList]
  | e :: es => by simp [applyList, apply_comp θ η e, applyList_comp θ η es]
end

mutual
theorem apply_id : ∀ e, Subst.id.apply e = e
  | .var v => by simp [apply, Subst.id]
  | .const k t => by simp [apply]
  | .app f t args => by simp [apply, applyList_id args]
theorem applyList_id : ∀ es, Subst.id.applyList es = es
  | [] => by simp [applyList]
  | e :: es => by simp [applyList, apply_id e, applyList_id es]
end

/-- Typed: every variable gets an expression that fits its type. -/
def Typed (θ : Subst) : Prop := ∀ v : Var, v.ty.fits (θ.f v).ty

/-- `σ` is an instance of `θ`: `σ = δ ∘ θ` for some `δ`. The draft writes `θ ≼ σ`. -/
def IsInstance (σ θ : Subst) : Prop := ∃ δ : Subst, σ = δ.comp θ

/-- Idempotent: applying it twice is applying it once. -/
def Idem (θ : Subst) : Prop := θ.comp θ = θ

/-- The equational form: the equations `v = θ(v)` for the variables it moves (the
draft, Definition 2.6). -/
def eqs (θ : Subst) : List (Exp × Exp) :=
  (θ.dom.sort (· ≤ ·)).map fun v => (.var v, θ.f v)

/-- Restricted to a set of variables: outside it, the identity. -/
def restrict (θ : Subst) (s : Finset Var) : Subst where
  f := fun v => if v ∈ s then θ.f v else .var v
  dom := θ.dom.filter (· ∈ s)
  hdom := fun v => by
    by_cases hv : v ∈ s
    · simp [hv, θ.hdom]
    · simp [hv]

end Subst

end Theory

namespace Theory.Subst

/-- A typed substitution keeps the type of an expression, up to `fits`. -/
theorem ty_apply {θ : Subst} (hθ : θ.Typed) : ∀ e : Exp, e.ty.fits (θ.apply e).ty
  | .var v => hθ v
  | .const _ _ => Ty.fits_refl _
  | .app _ t _ => by simp only [apply, Exp.ty]; exact Ty.fits_refl t

theorem Typed.comp {θ η : Subst} (hθ : θ.Typed) (hη : η.Typed) : (θ.comp η).Typed :=
  fun v => Ty.fits_trans (hη v) (ty_apply hθ (η.f v))

mutual
/-- The variables of an expression under a substitution: those of the images of its
variables. -/
theorem vars_apply (θ : Subst) : ∀ e : Exp, (θ.apply e).vars = e.vars.biUnion fun v => (θ.f v).vars
  | .var v => by simp [apply, Exp.vars]
  | .const _ _ => by simp [apply, Exp.vars]
  | .app _ _ args => by simp only [apply, Exp.vars]; exact varsList_applyList θ args
theorem varsList_applyList (θ : Subst) :
    ∀ es : List Exp, Exp.varsList (θ.applyList es) = (Exp.varsList es).biUnion fun v => (θ.f v).vars
  | [] => by simp [applyList, Exp.varsList]
  | e :: es => by
    simp only [applyList, Exp.varsList, vars_apply θ e, varsList_applyList θ es]
    ext w
    simp only [Finset.mem_union, Finset.mem_biUnion]
    aesop
end

mutual
/-- The constants of an expression under a substitution: its own and those of the
images of its variables. -/
theorem consts_apply (θ : Subst) :
    ∀ e : Exp, (θ.apply e).consts = e.consts ∪ e.vars.biUnion fun v => (θ.f v).consts
  | .var v => by simp [apply, Exp.vars, Exp.consts]
  | .const _ _ => by simp [apply, Exp.vars, Exp.consts]
  | .app _ _ args => by simp only [apply, Exp.vars, Exp.consts]; exact constsList_applyList θ args
theorem constsList_applyList (θ : Subst) :
    ∀ es : List Exp, Exp.constsList (θ.applyList es) =
      Exp.constsList es ∪ (Exp.varsList es).biUnion fun v => (θ.f v).consts
  | [] => by simp [applyList, Exp.varsList, Exp.constsList]
  | e :: es => by
    simp only [applyList, Exp.varsList, Exp.constsList, consts_apply θ e, constsList_applyList θ es]
    ext w
    simp only [Finset.mem_union, Finset.mem_biUnion]
    aesop
end

end Theory.Subst

namespace Theory.Subst

theorem comp_assoc (θ η σ : Subst) : (θ.comp η).comp σ = θ.comp (η.comp σ) := by
  apply ext
  funext v
  show (θ.comp η).apply (σ.f v) = θ.apply ((η.comp σ).f v)
  rw [apply_comp]
  rfl

theorem comp_id (θ : Subst) : θ.comp Subst.id = θ := by
  apply ext
  funext v
  show θ.apply (Subst.id.f v) = θ.f v
  rfl

theorem id_comp (θ : Subst) : Subst.id.comp θ = θ := by
  apply ext
  funext v
  show Subst.id.apply (θ.f v) = θ.f v
  exact apply_id _

end Theory.Subst
