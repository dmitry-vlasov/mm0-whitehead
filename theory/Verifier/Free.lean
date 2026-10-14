/-
Free variables (milestone V3b): a free variable of a well-typed expression is a bound
variable of the context, and free variables are carried along an injective renaming of
variables that keeps the binders.
-/
import Verifier.StmtSound

namespace Verifier

open mm0

/-- A context whose regular variables depend on bound variables only. -/
def RegDepsBound (Γ : ctx) : Prop :=
  ∀ (u : ℕ) (s : sort_id) (vs : Finset var_id), Γ[u]? = some (binder.reg s vs) → ∀ x ∈ vs,
    ∃ s', Γ[x]? = some (binder.bound s')

/-- An environment whose terms' return types depend on bound binders only. -/
def TermsRetBound (E : env) : Prop :=
  ∀ (t : term_id) (a : ctx) (r : dep_type) (o : Option (List sort_id × sexpr)), E.get_term t a r o →
    ∀ u ∈ r.2, ∃ s, a[u]? = some (binder.bound s)

theorem free'_bound {E : env} (hu : TermsUnique E) (hr : TermsRetBound E) {Γ : ctx} (hΓ : RegDepsBound Γ) {w : var_id} :
    ∀ (e : sexpr) (es : List sexpr) (ps : List Prop) (bis : List binder) (s : sort_id),
      sexpr.ok' E Γ e bis s → List.Forall₂ (sexpr.ok_bi E Γ) es bis →
      (∀ (n : ℕ) (p : Prop), ps[n]? = some p → p → ∃ s', Γ[w]? = some (binder.bound s')) →
      sexpr.free' E Γ w e es ps → ∃ s', Γ[w]? = some (binder.bound s')
  | .var u, es, ps, bis, s, hok, hes, _, h => by
    obtain ⟨bi, hbi, rfl, _⟩ := ok'_var_inv hok
    simp only [sexpr.free', sexpr.has_var] at h
    obtain ⟨bi', hbi', hm⟩ := h
    rw [hbi] at hbi'
    cases hbi'
    cases bi with
    | bound s0 =>
      simp only at hm
      subst hm
      exact ⟨s0, hbi⟩
    | reg s0 vs =>
      simp only at hm
      exact hΓ u s0 vs hbi w hm
  | .term f, es, ps, bis, s, hok, hes, hps, h => by
    obtain ⟨ret, o, hget, _⟩ := ok'_term_inv hok
    simp only [sexpr.free'] at h
    obtain ⟨args, r, rs, o', hget', h⟩ := h
    obtain ⟨rfl, hret⟩ := hu _ _ _ _ _ _ _ hget' hget
    rcases h with ⟨n, p, a, hp, _, hpp, _⟩ | ⟨u, hu', hesu⟩
    · exact hps n p hp hpp
    · obtain ⟨s0, hs0⟩ := hr f args (r, rs) o' hget' u hu'
      obtain ⟨hul, he1⟩ := List.getElem?_eq_some_iff.1 hesu
      obtain ⟨hub, hb1⟩ := List.getElem?_eq_some_iff.1 hs0
      have hbu := forall₂_get hes hul hub
      rw [he1, hb1] at hbu
      obtain ⟨v, hv, hΓv⟩ := hbu
      cases hv
      exact ⟨s0, hΓv⟩
  | .app1 f x, es, ps, bis, s, hok, hes, hps, h => by
    simp only [sexpr.free'] at h
    obtain ⟨bi, hf, hx⟩ := ok'_app1_inv hok
    refine free'_bound hu hr hΓ f (x :: es) _ (bi :: bis) s hf (List.Forall₂.cons hx hes) (fun n p hp hpp => ?_) h
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      exact free'_bound hu hr hΓ x [] [] [] bi.sort (ok_bi_ok hx) List.Forall₂.nil (fun _ _ h => by simp at h) hpp
    | succ n =>
      simp only [List.getElem?_cons_succ] at hp
      exact hps n p hp hpp

theorem free_bound {E : env} (hu : TermsUnique E) (hr : TermsRetBound E) {Γ : ctx} (hΓ : RegDepsBound Γ)
    {e : sexpr} {s : sort_id} {w : var_id} (hok : sexpr.ok E Γ e s) (h : sexpr.free E Γ e w) :
    ∃ s', Γ[w]? = some (binder.bound s') :=
  free'_bound hu hr hΓ e [] [] [] s hok List.Forall₂.nil (fun _ _ h => by simp at h) h

/-! ### Renaming -/

/-- A renaming of the variables of `Δ` into `Γ`: `ρ` sends each variable to a variable
with the same binder, injectively, and fixes the variables regular binders depend on. -/
structure Renaming (Δ Γ : ctx) (ρ : List sexpr) (r : ℕ → ℕ) : Prop where
  var : ∀ i, i < Δ.length → ρ.getD i default = sexpr.var (r i)
  ctx : ∀ i, i < Δ.length → Γ[r i]? = Δ[i]?
  inj : ∀ i j, i < Δ.length → j < Δ.length → r i = r j → i = j
  fix : ∀ (u : ℕ) (s : sort_id) (vs : Finset var_id), Δ[u]? = some (binder.reg s vs) → ∀ x ∈ vs, r x = x

theorem subst_eq_var {Δ Γ : ctx} {ρ : List sexpr} {r : ℕ → ℕ} (hρ : Renaming Δ Γ ρ r) :
    ∀ {e : sexpr} {w : ℕ}, sexpr.VarsLt e Δ.length → sexpr.subst ρ e = sexpr.var w → ∃ v, e = sexpr.var v ∧ r v = w
  | .var v, w, hv, h => by
    simp only [sexpr.subst] at h
    rw [hρ.var v hv] at h
    cases h
    exact ⟨v, rfl, rfl⟩
  | .term _, _, _, h => by simp [sexpr.subst] at h
  | .app1 _ _, _, _, h => by simp [sexpr.subst] at h

theorem free'_rename {E : env} {Δ Γ : ctx} {ρ : List sexpr} {r : ℕ → ℕ} (hρ : Renaming Δ Γ ρ r) {v : var_id}
    (hv : v < Δ.length) :
    ∀ (e : sexpr) (es : List sexpr) (ps ps' : List Prop), sexpr.VarsLt e Δ.length →
      (∀ x ∈ es, sexpr.VarsLt x Δ.length) → ps.length = ps'.length →
      (∀ (n : ℕ) (p p' : Prop), ps[n]? = some p → ps'[n]? = some p' → p → p') →
      sexpr.free' E Δ v e es ps → sexpr.free' E Γ (r v) (sexpr.subst ρ e) (es.map (sexpr.subst ρ)) ps'
  | .var u, es, ps, ps', hu, _, _, _, h => by
    simp only [sexpr.subst]
    rw [hρ.var u hu]
    simp only [sexpr.free', sexpr.has_var] at h ⊢
    obtain ⟨bi, hbi, hm⟩ := h
    refine ⟨bi, by rw [hρ.ctx u hu]; exact hbi, ?_⟩
    cases bi with
    | bound s0 => simp only at hm ⊢; rw [hm]
    | reg s0 vs => simp only at hm ⊢; rw [hρ.fix u s0 vs hbi v hm]; exact hm
  | .term f, es, ps, ps', _, hes, hlen, hps, h => by
    simp only [sexpr.subst, sexpr.free'] at h ⊢
    obtain ⟨args, r', rs, o, hget, h⟩ := h
    refine ⟨args, r', rs, o, hget, ?_⟩
    rcases h with ⟨n, p, a, hp, ha, hpp, hmf⟩ | ⟨u, hu, hesu⟩
    · left
      have hn' : n < ps'.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hp).1
      refine ⟨n, ps'[n], a, List.getElem?_eq_getElem hn', ha, hps n p _ hp (List.getElem?_eq_getElem hn') hpp, ?_⟩
      obtain ⟨s0, vs, rfl, hnot⟩ := hmf
      refine ⟨s0, vs, rfl, ?_⟩
      rintro ⟨u, hu, hesu⟩
      rw [List.getElem?_map] at hesu
      cases hx : es[u]? with
      | none => rw [hx] at hesu; cases hesu
      | some x =>
        rw [hx] at hesu
        simp only [Option.map_some, Option.some.injEq] at hesu
        obtain ⟨w, rfl, hw⟩ := subst_eq_var hρ (hes x (List.mem_of_getElem? hx)) hesu
        have hwl : w < Δ.length := by
          have := hes _ (List.mem_of_getElem? hx)
          simpa [sexpr.VarsLt] using this
        exact hnot ⟨u, hu, by rw [hx, hρ.inj w v hwl hv hw]⟩
    · right
      refine ⟨u, hu, ?_⟩
      rw [List.getElem?_map, hesu]
      simp only [Option.map_some, sexpr.subst]
      rw [hρ.var v hv]
  | .app1 f x, es, ps, ps', he, hes, hlen, hps, h => by
    simp only [sexpr.subst, sexpr.free'] at h ⊢
    have := free'_rename hρ hv f (x :: es) (sexpr.free' E Δ v x [] [] :: ps)
      (sexpr.free' E Γ (r v) (sexpr.subst ρ x) [] [] :: ps') he.1
      (fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact he.2
        · exact hes y hy)
      (by simp [hlen])
      (fun n p p' hp hp' hpp => by
        cases n with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hp'
          subst hp; subst hp'
          exact free'_rename hρ hv x [] [] [] he.2 (fun _ h => by simp at h) rfl (fun _ _ _ h => by simp at h) hpp
        | succ n =>
          simp only [List.getElem?_cons_succ] at hp hp'
          exact hps n p p' hp hp' hpp) h
    simpa using this

theorem free_rename {E : env} {Δ Γ : ctx} {ρ : List sexpr} {r : ℕ → ℕ} (hρ : Renaming Δ Γ ρ r) {v : var_id}
    (hv : v < Δ.length) {e : sexpr} (he : sexpr.VarsLt e Δ.length) (h : sexpr.free E Δ e v) :
    sexpr.free E Γ (sexpr.subst ρ e) (r v) :=
  free'_rename hρ hv e [] [] [] he (fun _ h => by simp at h) rfl (fun _ _ _ h => by simp at h) h

end Verifier
