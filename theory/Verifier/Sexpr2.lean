/-
More facts about the semantics (milestone V3, part d): inversion and uniqueness of
typing, monotonicity in the environment, typing under substitution and back under a
renaming, the congruence of an application argument by argument, and substitution by
the identity.
-/
import Verifier.Sexpr

namespace Verifier

open mm0

/-! ### Inversion -/

theorem ok'_app1_inv {E : env} {Γ : ctx} {f x : sexpr} {bis : List binder} {s : sort_id}
    (h : sexpr.ok' E Γ (sexpr.app1 f x) bis s) : ∃ bi, sexpr.ok' E Γ f (bi :: bis) s ∧ sexpr.ok_bi E Γ x bi := by
  generalize he : sexpr.app1 f x = e at h
  cases h with
  | var _ => cases he
  | term _ => cases he
  | app_var hv hf =>
    cases he
    exact ⟨_, hf, ⟨_, rfl, hv⟩⟩
  | app_reg hf hx =>
    cases he
    exact ⟨_, hf, hx⟩

theorem ok'_term_inv {E : env} {Γ : ctx} {t : term_id} {bis : List binder} {s : sort_id}
    (h : sexpr.ok' E Γ (sexpr.term t) bis s) : ∃ ret o, E.get_term t bis ret o ∧ s = ret.1 := by
  generalize he : sexpr.term t = e at h
  cases h with
  | var _ => cases he
  | term ht => cases he; exact ⟨_, _, ht, rfl⟩
  | app_var _ _ => cases he
  | app_reg _ _ => cases he

theorem ok'_app'_inv {E : env} {Γ : ctx} : ∀ (es : List sexpr) (f : sexpr) (bis : List binder) (s : sort_id),
    sexpr.ok' E Γ (sexpr.app' f es) bis s → ∃ pre, sexpr.ok' E Γ f (pre ++ bis) s ∧ List.Forall₂ (sexpr.ok_bi E Γ) es pre
  | [], f, bis, s, h => ⟨[], h, List.Forall₂.nil⟩
  | x :: xs, f, bis, s, h => by
    rw [sexpr.app'] at h
    obtain ⟨pre, h1, h2⟩ := ok'_app'_inv xs _ bis s h
    obtain ⟨bi, hf, hx⟩ := ok'_app1_inv h1
    exact ⟨bi :: pre, hf, List.Forall₂.cons hx h2⟩

theorem ok_app_inv {E : env} {Γ : ctx} {t : term_id} {es : List sexpr} {s : sort_id}
    (h : sexpr.ok E Γ (sexpr.app t es) s) :
    ∃ bis ret o, E.get_term t bis ret o ∧ s = ret.1 ∧ List.Forall₂ (sexpr.ok_bi E Γ) es bis := by
  obtain ⟨pre, h1, h2⟩ := ok'_app'_inv es _ [] s h
  rw [List.append_nil] at h1
  obtain ⟨ret, o, ht, hs⟩ := ok'_term_inv h1
  exact ⟨pre, ret, o, ht, hs, h2⟩

/-! ### Uniqueness -/

/-- An environment in which a term has one declaration. -/
def TermsUnique (E : env) : Prop :=
  ∀ t a r o a' r' o', E.get_term t a r o → E.get_term t a' r' o' → a = a' ∧ r = r'

theorem ok'_unique {E : env} (hu : TermsUnique E) {Γ : ctx} : ∀ {x : sexpr} {bis bis' : List binder} {s s' : sort_id},
    sexpr.ok' E Γ x bis s → sexpr.ok' E Γ x bis' s' → bis = bis' ∧ s = s' := by
  intro x bis bis' s s' h h'
  induction h generalizing bis' s' with
  | var hv =>
    obtain ⟨bi, hv', rfl, rfl⟩ := ok'_var_inv h'
    rw [hv] at hv'
    cases hv'
    exact ⟨rfl, rfl⟩
  | term ht =>
    obtain ⟨ret', o', ht', rfl⟩ := ok'_term_inv h'
    obtain ⟨hb, rfl⟩ := hu _ _ _ _ _ _ _ ht ht'
    exact ⟨hb, rfl⟩
  | app_var hv _ ih =>
    obtain ⟨bi, hf', hx'⟩ := ok'_app1_inv h'
    obtain ⟨hb, rfl⟩ := ih hf'
    exact ⟨(List.cons.inj hb).2, rfl⟩
  | app_reg _ _ ih _ =>
    obtain ⟨bi, hf', _⟩ := ok'_app1_inv h'
    obtain ⟨hb, rfl⟩ := ih hf'
    exact ⟨(List.cons.inj hb).2, rfl⟩

theorem ok_unique {E : env} (hu : TermsUnique E) {Γ : ctx} {x : sexpr} {s s' : sort_id}
    (h : sexpr.ok E Γ x s) (h' : sexpr.ok E Γ x s') : s = s' := (ok'_unique hu h h').2

/-- An expression that fits a binder has the binder's sort. -/
theorem ok_bi_sort {E : env} (hu : TermsUnique E) {Γ : ctx} {x : sexpr} {bi : binder} {s : sort_id}
    (hbi : sexpr.ok_bi E Γ x bi) (h : sexpr.ok E Γ x s) : s = bi.sort := by
  cases bi with
  | bound s0 =>
    obtain ⟨v, rfl, hv⟩ := hbi
    obtain ⟨bi', hv', _, rfl⟩ := ok'_var_inv h
    rw [hv] at hv'
    cases hv'
    rfl
  | reg s0 vs => exact ok_unique hu h hbi

theorem ok_bi_ok {E : env} {Γ : ctx} {x : sexpr} {bi : binder} (h : sexpr.ok_bi E Γ x bi) : sexpr.ok E Γ x bi.sort := by
  cases bi with
  | bound s0 =>
    obtain ⟨v, rfl, hv⟩ := h
    exact sexpr.ok'.var hv
  | reg s0 vs => exact h

/-! ### A larger environment -/

theorem get_term_mono {E E' : env} (hE : ∀ d ∈ E, d ∈ E') {t : term_id} {a : ctx} {r : dep_type}
    {o : Option (List sort_id × sexpr)} (h : E.get_term t a r o) : E'.get_term t a r o := by
  cases h with
  | term h => exact env.get_term.term (hE _ h)
  | defn h => exact env.get_term.defn (hE _ h)

theorem ok'_env_mono {E E' : env} (hE : ∀ d ∈ E, d ∈ E') {Γ : ctx} : ∀ {x : sexpr} {bis : List binder} {s : sort_id},
    sexpr.ok' E Γ x bis s → sexpr.ok' E' Γ x bis s := by
  intro x bis s h
  induction h with
  | var hv => exact sexpr.ok'.var hv
  | term ht => exact sexpr.ok'.term (get_term_mono hE ht)
  | app_var hv _ ih => exact sexpr.ok'.app_var hv ih
  | app_reg _ _ ih1 ih2 => exact sexpr.ok'.app_reg ih1 ih2

/-! ### Substitution -/

theorem ok'_subst {E : env} {Δ Γ : ctx} {σ : List sexpr}
    (hσ : ∀ (i : ℕ) (bi : binder), Δ[i]? = some bi → sexpr.ok_bi E Γ (σ.getD i default) bi) :
    ∀ {v : sexpr} {bis : List binder} {s : sort_id}, sexpr.ok' E Δ v bis s → sexpr.ok' E Γ (sexpr.subst σ v) bis s := by
  intro v bis s h
  induction h with
  | var hv => exact ok_bi_ok (hσ _ _ hv)
  | term ht => exact sexpr.ok'.term ht
  | app_var hv _ ih =>
    obtain ⟨w, hw, hw'⟩ := hσ _ _ hv
    simp only [sexpr.subst]
    rw [hw]
    exact sexpr.ok'.app_var hw' ih
  | app_reg _ _ ih1 ih2 => exact sexpr.ok'.app_reg ih1 ih2

/-- Back under a renaming: an expression whose renaming is well-typed in `Γ` is
well-typed in `Δ`, when the renaming sends every variable of `Δ` to one of `Γ` with the
same binder. -/
theorem ok'_of_subst_renaming {E : env} {Δ Γ : ctx} {ρ : List sexpr}
    (hρ : ∀ i, i < Δ.length → ∃ w, ρ.getD i default = sexpr.var w ∧ Γ[w]? = Δ[i]?) :
    ∀ (v : sexpr) {bis : List binder} {s : sort_id}, sexpr.VarsLt v Δ.length →
      sexpr.ok' E Γ (sexpr.subst ρ v) bis s → sexpr.ok' E Δ v bis s
  | .var i, bis, s, hv, h => by
    obtain ⟨w, hw, hΓ⟩ := hρ i hv
    simp only [sexpr.subst] at h
    rw [hw] at h
    obtain ⟨bi, hbi, rfl, rfl⟩ := ok'_var_inv h
    rw [hbi] at hΓ
    exact sexpr.ok'.var hΓ.symm
  | .term t, bis, s, _, h => by
    obtain ⟨ret, o, ht, rfl⟩ := ok'_term_inv h
    exact sexpr.ok'.term ht
  | .app1 f x, bis, s, hv, h => by
    simp only [sexpr.subst] at h
    obtain ⟨bi, hf, hx⟩ := ok'_app1_inv h
    have ihf := ok'_of_subst_renaming hρ f hv.1 hf
    cases bi with
    | bound s0 =>
      obtain ⟨u, hu, hu'⟩ := hx
      cases x with
      | var i =>
        obtain ⟨w, hw, hΓ⟩ := hρ i hv.2
        simp only [sexpr.subst] at hu
        rw [hw] at hu
        cases hu
        rw [hu'] at hΓ
        exact sexpr.ok'.app_var hΓ.symm ihf
      | term _ => simp [sexpr.subst] at hu
      | app1 _ _ => simp [sexpr.subst] at hu
    | reg s0 vs => exact sexpr.ok'.app_reg ihf (ok'_of_subst_renaming hρ x hv.2 hx)

theorem subst_id_of_varsLt : ∀ {x : sexpr} {n : ℕ}, sexpr.VarsLt x n → sexpr.subst ((List.range n).map sexpr.var) x = x
  | .var v, n, h => by
    simp only [sexpr.subst]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
    rfl
  | .term _, _, _ => rfl
  | .app1 f x, n, h => by
    simp only [sexpr.subst]
    rw [subst_id_of_varsLt h.1, subst_id_of_varsLt h.2]

/-! ### Congruence of an application -/

theorem conv'_app'_cong {E : env} {Γ : ctx} {rest : List binder} {s : sort_id} :
    ∀ (bis : List binder) (A B : List sexpr) (f1 f2 : sexpr), A.length = bis.length → B.length = bis.length →
      (∀ i (hA : i < A.length) (hB : i < B.length) (hb : i < bis.length),
        sexpr.ok_bi E Γ A[i] bis[i] ∧ sexpr.ok_bi E Γ B[i] bis[i] ∧ conv' E Γ A[i] B[i] [] bis[i].sort) →
      conv' E Γ f1 f2 (bis ++ rest) s → conv' E Γ (sexpr.app' f1 A) (sexpr.app' f2 B) rest s
  | [], [], [], _, _, _, _, _, h => h
  | bi :: bis, a :: A, b :: B, f1, f2, hA, hB, hall, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hA hB
    obtain ⟨ha, hb, hab⟩ := hall 0 (by simp) (by simp) (by simp)
    simp only [List.getElem_cons_zero] at ha hb hab
    rw [sexpr.app', sexpr.app']
    refine conv'_app'_cong bis A B _ _ hA hB (fun i h1 h2 h3 => ?_) (conv'.cong ha hb h hab)
    have := hall (i + 1) (by simp; omega) (by simp; omega) (by simp; omega)
    simpa using this
  | [], _ :: _, _, _, _, hA, _, _, _ => by simp at hA
  | [], [], _ :: _, _, _, _, hB, _, _ => by simp at hB
  | _ :: _, [], _, _, _, hA, _, _, _ => by simp at hA
  | _ :: _, _ :: _, [], _, _, _, hB, _, _ => by simp at hB

end Verifier
