/-
A unifier for the first-order terms of MM0, to run the reference engine with: the
classical algorithm (Robinson; Martelli–Montanari) on a list of equations, with a
fuel. That it satisfies the postulate (`Unification`) is milestone 7 of
`docs/THEORY.md`; until then the instance `Unify.postulate` carries the proofs as
`sorry`, and the engine runs on it.

The typing of substitutions (`Ty.fits`) is the one of the production unifier: of two
variables the more general is bound to the more special (`ruUnifyStepVar`; `DESIGN.md`,
change 2); a variable is bound to a term only if the term's type fits it, so a name
variable never takes an application.
-/
import Theory.Unification

namespace Theory

namespace Unify

/-- Binds `v` to `e` on top of `θ`: `θ` followed by the binding. -/
def bind (v : Var) (e : Exp) (θ : Subst) : Subst :=
  (Subst.single v e).comp θ

/-- Binds `v` to `e` in the remaining equations. -/
def bindIn (v : Var) (e : Exp) (E : Problem) : Problem :=
  let σ := Subst.single v e
  E.map fun p => (σ.apply p.1, σ.apply p.2)

/-- The algorithm, on equations whose sides are already under the substitution so far. -/
def go : ℕ → Problem → Subst → Option Subst
  | 0, _, _ => none
  | _ + 1, [], θ => some θ
  | fuel + 1, (s, t) :: E, θ =>
    match s, t with
    | .var v, .var w =>
      if v = w then go fuel E θ
      else if v.ty.fits w.ty then go fuel (bindIn v (.var w) E) (bind v (.var w) θ)
      else if w.ty.fits v.ty then go fuel (bindIn w (.var v) E) (bind w (.var v) θ)
      else none
    | .var v, e | e, .var v =>
      if v.ty.fits e.ty ∧ v ∉ e.vars then go fuel (bindIn v e E) (bind v e θ) else none
    | .const k t, .const k' t' =>
      if k = k' ∧ t = t' then go fuel E θ else none
    | .app f t args, .app f' t' args' =>
      if f = f' ∧ t = t' ∧ args.length = args'.length then go fuel (args.zip args' ++ E) θ else none
    | _, _ => none

/-- Enough fuel: every step but a binding shortens the equations or their sizes, and
there are at most as many bindings as variables. -/
def fuel (E : Problem) : ℕ :=
  let size := E.foldl (fun n p => n + p.1.size + p.2.size) 0
  let vars := (E.map fun p => (p.1.vars ∪ p.2.vars)).foldr (· ∪ ·) ∅
  (vars.card + 1) * (size + E.length + 1) * 2

/-- The most general unifier of a problem, if there is one. -/
def mgu (E : Problem) : Option Subst := go (fuel E) E Subst.id

end Unify

/-- The postulate, carried by `Unify.mgu`; its proofs are milestone 7. -/
def Unify.postulate : Unification where
  mgu := Unify.mgu
  typed := by sorry
  idem := by sorry
  solves := by sorry
  mostGeneral := by sorry

end Theory
