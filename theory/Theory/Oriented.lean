/-
Oriented unifiers (`docs/THEORY.md`, "The production engine", decision 16 and
milestone 16).

Of two variables that fit each other a unifier binds one to the other, and which one
is its choice; two most general unifiers of a problem differ only in such choices. An
*oriented* unifier makes the choice by the variables alone: the one with the larger
number is bound, or the one of the more general type (`Var.before`, as `Unify.go` has
it since milestone 15). Then the choice is no longer free: two oriented idempotent
unifiers that are instances of each other are equal (`oriented_unique`) — a
representative the first keeps the second would have to bind to one before it, and the
first would then bind that one back, against the orientation. The concrete unifier is
oriented (`Unify.postulate_oriented`).

With this the keyed engine's substitutions are the reference engine's restricted ones
exactly (`KeyedExact.lean`), where milestones 13 and 14 had them equal up to instance
each way.
-/
import Theory.Engine
import Theory.Unify

namespace Theory

/-- `r` is kept and `v` bound to it, of two variables that are made equal: `v`'s type
fits `r`'s, and `r` has the smaller number or the more special type. This is the
condition of the variable case of `Unify.go`. -/
def Var.before (r v : Var) : Prop := v.ty.fits r.ty ∧ (r.id < v.id ∨ ¬ r.ty.fits v.ty)

theorem Ty.eq_of_fits {a b : Ty} (h₁ : a.fits b) (h₂ : b.fits a) : a = b := by
  cases a with | mk s n =>
  cases b with | mk s' n' =>
  simp only [Ty.fits] at h₁ h₂
  obtain ⟨rfl, hn⟩ := h₁
  obtain ⟨_, hn'⟩ := h₂
  cases n <;> cases n' <;> simp_all

theorem Var.before_asymm {r v : Var} (h₁ : Var.before r v) (h₂ : Var.before v r) : False := by
  obtain ⟨h1, h2⟩ := h₁
  obtain ⟨h3, h4⟩ := h₂
  rcases h2 with h2 | h2
  · rcases h4 with h4 | h4
    · omega
    · exact h4 h1
  · exact h2 h3

theorem Var.before_trans {r w v : Var} (h₁ : Var.before r w) (h₂ : Var.before w v) : Var.before r v := by
  obtain ⟨h1, h2⟩ := h₁
  obtain ⟨h3, h4⟩ := h₂
  refine ⟨Ty.fits_trans h3 h1, ?_⟩
  by_cases hrv : r.ty.fits v.ty
  · left
    have h2' : r.id < w.id := by
      rcases h2 with h2 | h2
      · exact h2
      · exact absurd (Ty.fits_trans hrv h3) h2
    have h4' : w.id < v.id := by
      rcases h4 with h4 | h4
      · exact h4
      · exact absurd (Ty.fits_trans h1 hrv) h4
    omega
  · right
    exact hrv

/-- Two distinct variables that fit each other have distinct numbers. -/
theorem Var.id_ne_of_fits {v w : Var} (hne : v ≠ w) (h₁ : v.ty.fits w.ty) (h₂ : w.ty.fits v.ty) : v.id ≠ w.id := by
  intro hid
  apply hne
  have hty := Ty.eq_of_fits h₁ h₂
  cases v
  cases w
  simp only at hid hty
  subst hid
  subst hty
  rfl

/-- Oriented: every variable bound to a variable is bound to one before it. -/
def Subst.Oriented (θ : Subst) : Prop := ∀ v r, θ.f v = .var r → r ≠ v → Var.before r v

theorem Subst.Oriented.id : Subst.id.Oriented := fun _ r h hne => by
  simp only [Subst.id] at h
  exact absurd (Exp.var.inj h).symm hne

/-- An oriented postulate: every unifier it gives is oriented. -/
def Unification.Oriented (U : Unification) : Prop := ∀ E θ, U.mgu E = some θ → θ.Oriented

/-! ### Uniqueness -/

theorem Subst.apply_eq_var {δ : Subst} {e : Exp} {r : Var} (h : δ.apply e = .var r) : ∃ w, e = .var w := by
  cases e with
  | var w => exact ⟨w, rfl⟩
  | const k t => simp [Subst.apply] at h
  | app f t args => simp [Subst.apply] at h

/-- A variable in the image of an idempotent substitution is fixed by it. -/
theorem Subst.Idem.fixed {θ : Subst} (h : θ.Idem) {u w : Var} (hw : w ∈ (θ.f u).vars) : θ.f w = .var w :=
  Subst.f_eq_of_not_mem (h.not_mem_dom hw)

/-- **Uniqueness**: two oriented idempotent substitutions that are instances of each
other are equal. -/
theorem oriented_unique {σ σ' : Subst} (hσ : σ.Idem) (hσ' : σ'.Idem) (ho : σ.Oriented) (ho' : σ'.Oriented)
    (h₁ : σ.IsInstance σ') (h₂ : σ'.IsInstance σ) : σ = σ' := by
  obtain ⟨δ, hδ⟩ := h₁
  obtain ⟨δ', hδ'⟩ := h₂
  have e1 : ∀ v, σ.f v = δ.apply (σ'.f v) := fun v => congrArg (fun τ => τ.f v) hδ
  have e2 : ∀ v, σ'.f v = δ'.apply (σ.f v) := fun v => congrArg (fun τ => τ.f v) hδ'
  -- a representative of `σ'` is fixed by `σ`
  have fixed : ∀ r, σ'.f r = .var r → σ.f r = .var r := by
    intro r hr
    have h1 : σ.f r = δ.f r := by rw [e1 r, hr, Subst.apply_var]
    have h2 : δ'.apply (δ.f r) = .var r := by rw [← h1, ← e2 r, hr]
    obtain ⟨r₁, hr₁⟩ := Subst.apply_eq_var h2
    rw [hr₁] at h1 h2
    rw [Subst.apply_var] at h2
    by_cases hrr : r₁ = r
    · rw [h1, hrr]
    · exfalso
      have hb1 : Var.before r₁ r := ho r r₁ h1 hrr
      have hfix : σ.f r₁ = .var r₁ := hσ.fixed (u := r) (by rw [h1]; simp [Exp.vars])
      have h3 : σ'.f r₁ = .var r := by rw [e2 r₁, hfix, Subst.apply_var, h2]
      have hb2 : Var.before r r₁ := ho' r₁ r h3 (Ne.symm hrr)
      exact Var.before_asymm hb1 hb2
  apply Subst.ext
  funext v
  rw [e1 v]
  have hfixδ : ∀ w ∈ (σ'.f v).vars, δ.f w = Subst.id.f w := by
    intro w hw
    have hw' : σ'.f w = .var w := hσ'.fixed hw
    have := fixed w hw'
    rw [e1 w, hw', Subst.apply_var] at this
    exact this
  rw [apply_congr_vars _ hfixδ, Subst.apply_id]

/-! ### The concrete unifier is oriented -/

namespace Unify

theorem bind_oriented {v : Var} {e : Exp} {θ : Subst} (hθ : θ.Oriented)
    (he : ∀ r, e = .var r → Var.before r v) : (Unify.bind v e θ).Oriented := by
  intro u r hu hne
  change (Subst.single v e).apply (θ.f u) = .var r at hu
  obtain ⟨w, hw⟩ := Subst.apply_eq_var hu
  rw [hw, Subst.apply_var, single_f] at hu
  by_cases hwv : w = v
  · rw [ite_eq_left hwv] at hu
    subst hwv
    have hb := he r hu
    by_cases huw : u = w
    · subst huw
      exact hb
    · exact Var.before_trans hb (hθ u w hw (Ne.symm huw))
  · rw [ite_eq_right hwv] at hu
    obtain rfl := Exp.var.inj hu
    exact hθ u w hw hne

theorem go_oriented : ∀ (E : Problem) (θ : Subst), θ.Oriented → ∀ θ', go E θ = some θ' → θ'.Oriented := by
  intro E θ
  induction E, θ using go.induct with
  | case1 θ =>
    intro ho θ' hgo
    rw [go] at hgo
    obtain rfl := Option.some.inj hgo
    exact ho
  | case2 E θ w ih =>
    intro ho θ' hgo
    rw [go, ite_eq_left rfl] at hgo
    exact ih ho θ' hgo
  | case3 E θ v w hvw hfit ih =>
    intro ho θ' hgo
    rw [go, ite_eq_right hvw, ite_eq_left hfit] at hgo
    exact ih (bind_oriented ho fun r h => by cases h; exact hfit) θ' hgo
  | case4 E θ v w hvw hfit hfit' ih =>
    intro ho θ' hgo
    rw [go, ite_eq_right hvw, ite_eq_right hfit, ite_eq_left hfit'] at hgo
    have hb : Var.before v w := by
      refine ⟨hfit', ?_⟩
      by_cases hvw' : v.ty.fits w.ty
      · left
        have hnot : ¬ (w.id < v.id ∨ ¬ w.ty.fits v.ty) := fun h => hfit ⟨hvw', h⟩
        rw [not_or, not_not] at hnot
        have hid := Var.id_ne_of_fits hvw hvw' hnot.2
        omega
      · right
        exact hvw'
    exact ih (bind_oriented ho fun r h => by cases h; exact hb) θ' hgo
  | case5 E θ v w hvw hfit hfit' =>
    intro ho θ' hgo
    rw [go, ite_eq_right hvw, ite_eq_right hfit, ite_eq_right hfit'] at hgo
    simp at hgo
  | case6 E θ v k t hfit ih =>
    intro ho θ' hgo
    rw [go, ite_eq_left hfit] at hgo
    exact ih (bind_oriented ho fun r h => by cases h) θ' hgo
  | case7 E θ v k t hfit =>
    intro ho θ' hgo
    rw [go, ite_eq_right hfit] at hgo
    simp at hgo
  | case8 E θ k t v hfit ih =>
    intro ho θ' hgo
    rw [go, ite_eq_left hfit] at hgo
    exact ih (bind_oriented ho fun r h => by cases h) θ' hgo
  | case9 E θ k t v hfit =>
    intro ho θ' hgo
    rw [go, ite_eq_right hfit] at hgo
    simp at hgo
  | case10 E θ v f t args hc ih =>
    intro ho θ' hgo
    rw [go, ite_eq_left hc] at hgo
    exact ih (bind_oriented ho fun r h => by cases h) θ' hgo
  | case11 E θ v f t args hc =>
    intro ho θ' hgo
    rw [go, ite_eq_right hc] at hgo
    simp at hgo
  | case12 E θ f t args v hc ih =>
    intro ho θ' hgo
    rw [go, ite_eq_left hc] at hgo
    exact ih (bind_oriented ho fun r h => by cases h) θ' hgo
  | case13 E θ f t args v hc =>
    intro ho θ' hgo
    rw [go, ite_eq_right hc] at hgo
    simp at hgo
  | case14 E θ k t k' t' hc ih =>
    intro ho θ' hgo
    rw [go, ite_eq_left hc] at hgo
    exact ih ho θ' hgo
  | case15 E θ k t k' t' hc =>
    intro ho θ' hgo
    rw [go, ite_eq_right hc] at hgo
    simp at hgo
  | case16 E θ f t args f' t' args' hc ih =>
    intro ho θ' hgo
    rw [go, ite_eq_left hc] at hgo
    exact ih ho θ' hgo
  | case17 E θ f t args f' t' args' hc =>
    intro ho θ' hgo
    rw [go, ite_eq_right hc] at hgo
    simp at hgo
  | case18 s t E θ h1 h2 h3 h4 h5 h6 h7 =>
    intro ho θ' hgo
    cases s <;> cases t
    · exact (h1 _ _ rfl rfl).elim
    · exact (h2 _ _ _ rfl rfl).elim
    · exact (h4 _ _ _ _ rfl rfl).elim
    · exact (h3 _ _ _ rfl rfl).elim
    · exact (h6 _ _ _ _ rfl rfl).elim
    · rw [go.eq_def] at hgo; simp at hgo
    · exact (h5 _ _ _ _ rfl rfl).elim
    · rw [go.eq_def] at hgo; simp at hgo
    · exact (h7 _ _ _ _ _ _ rfl rfl).elim

/-- The concrete unifier is oriented. -/
theorem postulate_oriented : Unify.postulate.Oriented :=
  fun E θ h => go_oriented E Subst.id Subst.Oriented.id θ h

end Unify

end Theory
