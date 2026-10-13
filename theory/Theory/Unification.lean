/-
Unification as the draft's Postulate 2.5, for first-order terms: a structure with a most
general unifier of every solvable problem and its specification. The theorems are proved
relative to it; it is discharged by a unifier of the package with its proof (milestone 7
of `docs/THEORY.md`). The join of substitutions is defined from it (Definition 2.6).
-/
import Theory.Subst

namespace Theory

/-- A unification problem: equations between expressions. -/
abbrev Problem := List (Exp × Exp)

/-- `σ` solves the problem: it makes the two sides of every equation equal. -/
def Solves (σ : Subst) (E : Problem) : Prop := ∀ p ∈ E, σ.apply p.1 = σ.apply p.2

/-- The variables of a problem. -/
def Problem.vars (E : Problem) : Finset Var :=
  (E.map fun p => p.1.vars ∪ p.2.vars).foldr (· ∪ ·) ∅

/-- A most general unifier (Postulate 2.5 for first-order terms, where every problem is
in the class): `mgu E` is a typed idempotent solution of `E` of which every typed
solution is an instance, and `none` only when there is no typed solution. -/
structure Unification where
  mgu : Problem → Option Subst
  typed : ∀ E θ, mgu E = some θ → θ.Typed
  idem : ∀ E θ, mgu E = some θ → θ.Idem
  solves : ∀ E θ, mgu E = some θ → Solves θ E
  mostGeneral : ∀ E σ, σ.Typed → Solves σ E → ∃ θ, mgu E = some θ ∧ σ.IsInstance θ
  /-- A unifier mentions no variable outside its problem. -/
  dom_sub : ∀ E θ, mgu E = some θ → ∀ v ∈ θ.dom, v ∈ E.vars
  range_sub : ∀ E θ, mgu E = some θ → ∀ v, ∀ w ∈ (θ.f v).vars, w ∈ E.vars ∨ w = v

namespace Unification

theorem none_iff (U : Unification) (E : Problem) :
    U.mgu E = none ↔ ∀ σ : Subst, σ.Typed → ¬ Solves σ E := by
  constructor
  · intro h σ hσ hs
    obtain ⟨θ, hθ, _⟩ := U.mostGeneral E σ hσ hs
    rw [h] at hθ
    simp at hθ
  · intro h
    cases hm : U.mgu E with
    | none => rfl
    | some θ => exact absurd (U.solves E θ hm) (h θ (U.typed E θ hm))

/-- The join of two substitutions: the most general unifier of their equational forms
(Definition 2.6; "unification of substitutions" in the 2017 paper, `ruUnifySubs`). -/
def join (U : Unification) (θ η : Subst) : Option Subst :=
  U.mgu (θ.eqs ++ η.eqs)

/-- The join of a list of substitutions, `some Subst.id` for the empty list. -/
def joinAll (U : Unification) : List Subst → Option Subst
  | [] => some Subst.id
  | θ :: θs => (U.joinAll θs).bind fun η => U.join θ η

end Unification

end Theory
