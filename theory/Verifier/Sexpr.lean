/-
Facts about the semantics' expressions that the soundness proof needs (milestone V3,
part b): the curried application under `has_var`, `ok'` and `free'`; a longer context
keeps every judgment; a well-typed expression's variables are in the context. Nothing
here is about the machine.
-/
import Spec.Mm0

namespace Verifier

open mm0

/-! ### The curried application -/

theorem has_var_app' (Γ : ctx) (v : var_id) : ∀ (es : List sexpr) (f : sexpr),
    sexpr.has_var Γ (sexpr.app' f es) v ↔ sexpr.has_var Γ f v ∨ ∃ e ∈ es, sexpr.has_var Γ e v
  | [], f => by simp [sexpr.app']
  | x :: xs, f => by
    rw [sexpr.app', has_var_app' Γ v xs]
    simp only [sexpr.has_var, List.mem_cons, exists_eq_or_imp]
    tauto

theorem has_var_app (Γ : ctx) (t : term_id) (es : List sexpr) (v : var_id) :
    sexpr.has_var Γ (sexpr.app t es) v ↔ ∃ e ∈ es, sexpr.has_var Γ e v := by
  rw [sexpr.app, has_var_app']
  simp [sexpr.has_var]

theorem ok'_app' (E : env) (Γ : ctx) : ∀ (es : List sexpr) (bis : List binder) (f : sexpr) (s : sort_id),
    List.Forall₂ (sexpr.ok_bi E Γ) es bis → sexpr.ok' E Γ f bis s → sexpr.ok' E Γ (sexpr.app' f es) [] s
  | [], [], _, _, _, h => h
  | x :: xs, bi :: bis, f, s, hall, h => by
    rw [List.forall₂_cons] at hall
    obtain ⟨hx, hall⟩ := hall
    rw [sexpr.app']
    refine ok'_app' E Γ xs bis _ s hall ?_
    cases bi with
    | bound s' =>
      simp only [sexpr.ok_bi] at hx
      obtain ⟨v, rfl, hv⟩ := hx
      exact sexpr.ok'.app_var hv h
    | reg s' vs =>
      simp only [sexpr.ok_bi] at hx
      exact sexpr.ok'.app_reg h hx
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h

/-- An application of a term to arguments that fit its binders is well-typed. -/
theorem ok_app {E : env} {Γ : ctx} {t : term_id} {bis : ctx} {ret : dep_type} {o : Option (List sort_id × sexpr)}
    (ht : E.get_term t bis ret o) {es : List sexpr} (hall : List.Forall₂ (sexpr.ok_bi E Γ) es bis) :
    sexpr.ok E Γ (sexpr.app t es) ret.1 :=
  ok'_app' E Γ es bis _ _ hall (sexpr.ok'.term ht)

theorem free'_app' (E : env) (Γ : ctx) (v : var_id) :
    ∀ (es : List sexpr) (f : sexpr) (es₀ : List sexpr) (ps₀ : List Prop),
      sexpr.free' E Γ v (sexpr.app' f es) es₀ ps₀ =
        sexpr.free' E Γ v f (es ++ es₀) (es.map (fun x => sexpr.free' E Γ v x [] []) ++ ps₀)
  | [], _, _, _ => rfl
  | x :: xs, f, es₀, ps₀ => by
    rw [sexpr.app', free'_app' E Γ v xs]
    simp only [sexpr.free', List.cons_append, List.map_cons]

/-- The free variables of an application (`FreeApp` of `mm0.mm0`), in terms of the
arguments. -/
theorem free_app (E : env) (Γ : ctx) (t : term_id) (es : List sexpr) (v : var_id) :
    sexpr.free E Γ (sexpr.app t es) v ↔ ∃ args r rs o, E.get_term t args (r, rs) o ∧
      ((∃ (n : ℕ) (e : sexpr) (a : binder), es[n]? = some e ∧ args[n]? = some a ∧
        sexpr.free E Γ e v ∧ maybe_free_args es a v) ∨
      ∃ u ∈ rs, es[u]? = some (sexpr.var v)) := by
  unfold sexpr.free
  rw [sexpr.app, free'_app', List.append_nil, List.append_nil]
  simp only [sexpr.free']
  constructor
  · rintro ⟨args, r, rs, o, ht, h⟩
    refine ⟨args, r, rs, o, ht, ?_⟩
    rcases h with ⟨n, free, a, hn, ha, hf, hm⟩ | h
    · left
      rw [List.getElem?_map] at hn
      cases he : es[n]? with
      | none => rw [he] at hn; simp at hn
      | some e =>
        rw [he] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        subst hn
        exact ⟨n, e, a, he, ha, hf, hm⟩
    · right
      exact h
  · rintro ⟨args, r, rs, o, ht, h⟩
    refine ⟨args, r, rs, o, ht, ?_⟩
    rcases h with ⟨n, e, a, he, ha, hf, hm⟩ | h
    · left
      refine ⟨n, sexpr.free' E Γ v e [] [], a, ?_, ha, hf, hm⟩
      rw [List.getElem?_map, he]
      rfl
    · right
      exact h

/-! ### Inversion -/

theorem ok'_var_inv {E : env} {Γ : ctx} {v : var_id} {bis : List binder} {s : sort_id}
    (h : sexpr.ok' E Γ (sexpr.var v) bis s) : ∃ bi, Γ[v]? = some bi ∧ bis = [] ∧ s = bi.sort := by
  generalize he : sexpr.var v = e at h
  cases h with
  | var hv => cases he; exact ⟨_, hv, rfl, rfl⟩
  | term _ => cases he
  | app_var _ _ => cases he
  | app_reg _ _ => cases he

/-! ### Variables in range -/

/-- Every variable of the expression is below `n`. -/
def sexpr.VarsLt : sexpr → ℕ → Prop
  | .var v, n => v < n
  | .term _, _ => True
  | .app1 f x, n => sexpr.VarsLt f n ∧ sexpr.VarsLt x n

theorem varsLt_app' : ∀ (es : List sexpr) (f : sexpr) (n : ℕ),
    sexpr.VarsLt (sexpr.app' f es) n ↔ sexpr.VarsLt f n ∧ ∀ e ∈ es, sexpr.VarsLt e n
  | [], f, n => by simp [sexpr.app']
  | x :: xs, f, n => by
    rw [sexpr.app', varsLt_app' xs]
    simp only [sexpr.VarsLt, List.mem_cons, forall_eq_or_imp]
    tauto

theorem varsLt_app (t : term_id) (es : List sexpr) (n : ℕ) :
    sexpr.VarsLt (sexpr.app t es) n ↔ ∀ e ∈ es, sexpr.VarsLt e n := by
  rw [sexpr.app, varsLt_app']
  simp [sexpr.VarsLt]

theorem ok'_varsLt {E : env} {Γ : ctx} : ∀ {e : sexpr} {bis : List binder} {s : sort_id},
    sexpr.ok' E Γ e bis s → sexpr.VarsLt e Γ.length := by
  intro e bis s h
  induction h with
  | var hv => exact (List.getElem?_eq_some_iff.1 hv).1
  | term _ => trivial
  | app_var hv _ ih => exact ⟨ih, (List.getElem?_eq_some_iff.1 hv).1⟩
  | app_reg _ _ ih1 ih2 => exact ⟨ih1, ih2⟩

theorem ok_bi_varsLt {E : env} {Γ : ctx} {e : sexpr} {bi : binder} (h : sexpr.ok_bi E Γ e bi) :
    sexpr.VarsLt e Γ.length := by
  cases bi with
  | bound s =>
    simp only [sexpr.ok_bi] at h
    obtain ⟨v, rfl, hv⟩ := h
    exact (List.getElem?_eq_some_iff.1 hv).1
  | reg s vs =>
    simp only [sexpr.ok_bi] at h
    exact ok'_varsLt h

/-! ### A longer context -/

theorem getElem?_append_of_lt {Γ Δ : ctx} {u : ℕ} (h : u < Γ.length) : (Γ ++ Δ)[u]? = Γ[u]? :=
  List.getElem?_append_left h

theorem has_var_append {Γ Δ : ctx} : ∀ {e : sexpr} {v : var_id}, sexpr.VarsLt e Γ.length →
    (sexpr.has_var (Γ ++ Δ) e v ↔ sexpr.has_var Γ e v)
  | .var u, v, h => by
    simp only [sexpr.has_var]
    rw [getElem?_append_of_lt h]
  | .term _, _, _ => Iff.rfl
  | .app1 f x, v, h => by
    simp only [sexpr.has_var]
    rw [has_var_append h.1, has_var_append h.2]

theorem ok'_append {E : env} {Γ Δ : ctx} : ∀ {e : sexpr} {bis : List binder} {s : sort_id},
    sexpr.ok' E Γ e bis s → sexpr.ok' E (Γ ++ Δ) e bis s := by
  intro e bis s h
  induction h with
  | var hv => exact sexpr.ok'.var (by rw [getElem?_append_of_lt (List.getElem?_eq_some_iff.1 hv).1]; exact hv)
  | term ht => exact sexpr.ok'.term ht
  | app_var hv _ ih =>
    exact sexpr.ok'.app_var (by rw [getElem?_append_of_lt (List.getElem?_eq_some_iff.1 hv).1]; exact hv) ih
  | app_reg _ _ ih1 ih2 => exact sexpr.ok'.app_reg ih1 ih2

theorem ok_bi_append {E : env} {Γ Δ : ctx} {e : sexpr} {bi : binder} (h : sexpr.ok_bi E Γ e bi) :
    sexpr.ok_bi E (Γ ++ Δ) e bi := by
  cases bi with
  | bound s =>
    simp only [sexpr.ok_bi] at h ⊢
    obtain ⟨v, rfl, hv⟩ := h
    exact ⟨v, rfl, by rw [getElem?_append_of_lt (List.getElem?_eq_some_iff.1 hv).1]; exact hv⟩
  | reg s vs =>
    simp only [sexpr.ok_bi] at h ⊢
    exact ok'_append h

theorem free'_append {E : env} {Γ Δ : ctx} {v : var_id} :
    ∀ {e : sexpr} {es : List sexpr} {ps ps' : List Prop}, sexpr.VarsLt e Γ.length →
      (∀ e' ∈ es, sexpr.VarsLt e' Γ.length) → ps.length = ps'.length →
      (∀ (n : ℕ), ∀ p ∈ ps[n]?, ∀ p' ∈ ps'[n]?, (p ↔ p')) →
      (sexpr.free' E (Γ ++ Δ) v e es ps ↔ sexpr.free' E Γ v e es ps')
  | .var u, _, _, _, h, _, _, _ => has_var_append h
  | .term f, es, ps, ps', _, _, hlen, hps => by
    simp only [sexpr.free']
    constructor
    · rintro ⟨args, r, rs, o, ht, h⟩
      refine ⟨args, r, rs, o, ht, ?_⟩
      rcases h with ⟨n, free, a, hn, ha, hf, hm⟩ | h
      · left
        have hn' : n < ps'.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hn).1
        refine ⟨n, ps'[n], a, List.getElem?_eq_getElem hn', ha, ?_, hm⟩
        exact (hps n free hn ps'[n] (List.getElem?_eq_getElem hn')).1 hf
      · right; exact h
    · rintro ⟨args, r, rs, o, ht, h⟩
      refine ⟨args, r, rs, o, ht, ?_⟩
      rcases h with ⟨n, free, a, hn, ha, hf, hm⟩ | h
      · left
        have hn' : n < ps.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hn).1
        refine ⟨n, ps[n], a, List.getElem?_eq_getElem hn', ha, ?_, hm⟩
        exact (hps n ps[n] (List.getElem?_eq_getElem hn') free hn).2 hf
      · right; exact h
  | .app1 f x, es, ps, ps', h, hes, hlen, hps => by
    simp only [sexpr.free']
    apply free'_append h.1
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact h.2
      · exact hes e' he'
    · simp [hlen]
    · intro n p hp p' hp'
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.mem_def, Option.some.injEq] at hp hp'
        subst hp; subst hp'
        exact free'_append h.2 (fun _ h => by simp at h) rfl (fun n p hp p' hp' => by simp at hp)
      | succ n =>
        simp only [List.getElem?_cons_succ] at hp hp'
        exact hps n p hp p' hp'

theorem free_append {E : env} {Γ Δ : ctx} {e : sexpr} {v : var_id} (h : sexpr.VarsLt e Γ.length) :
    sexpr.free E (Γ ++ Δ) e v ↔ sexpr.free E Γ e v :=
  free'_append h (fun _ h => by simp at h) rfl (fun _ _ hp => by simp at hp)

theorem conv'_append {E : env} {Γ Δ : ctx} : ∀ {e1 e2 : sexpr} {bis : List binder} {s : sort_id},
    conv' E Γ e1 e2 bis s → conv' E (Γ ++ Δ) e1 e2 bis s := by
  intro e1 e2 bis s h
  induction h with
  | refl h => exact conv'.refl (ok'_append h)
  | symm _ ih => exact conv'.symm ih
  | trans _ _ ih1 ih2 => exact conv'.trans ih1 ih2
  | cong h1 h2 _ _ ih1 ih2 => exact conv'.cong (ok_bi_append h1) (ok_bi_append h2) ih1 ih2
  | unfold ht hes hzs _ ih =>
    refine conv'.unfold ht (hes.imp fun _ _ h => ok_bi_append h) (hzs.imp fun y z h => ?_) ih
    rw [getElem?_append_of_lt (List.getElem?_eq_some_iff.1 h).1]
    exact h

theorem safe_subst_append {Γ Δ args : ctx} {σ : List sexpr} (hσ : ∀ e ∈ σ, sexpr.VarsLt e Γ.length)
    (h : safe_subst Γ args σ) : safe_subst (Γ ++ Δ) args σ := by
  intro u v hu hv hnv y e2 hy he2
  rw [has_var_append (hσ e2 (List.mem_of_getElem? he2))]
  exact h u v hu hv hnv y e2 hy he2

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b ∈ l₂, R a b
  | [], _, _, _, h => by simp at h
  | _ :: _, _, List.Forall₂.cons hab hl, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨b, hb, h⟩ := forall₂_mem_left hl a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem proof_append {E : env} {Γ Δ : ctx} {Hs : Set sexpr} : ∀ {e : sexpr},
    proof E Γ Hs e → proof E (Γ ++ Δ) Hs e := by
  intro e h
  induction h with
  | hyp h => exact proof.hyp h
  | thm ht hσ hs _ ih =>
    refine proof.thm ht (hσ.imp fun _ _ h => ok_bi_append h) (safe_subst_append ?_ hs) ih
    intro e he
    obtain ⟨a, _, h⟩ := forall₂_mem_left hσ e he
    exact ok_bi_varsLt h
  | conv hc _ ih => exact proof.conv (conv'_append hc) ih

theorem proof_mono_hyps {E : env} {Γ : ctx} {Hs Hs' : Set sexpr} (hH : Hs ⊆ Hs') : ∀ {e : sexpr},
    proof E Γ Hs e → proof E Γ Hs' e := by
  intro e h
  induction h with
  | hyp h => exact proof.hyp (hH h)
  | thm ht hσ hs _ ih => exact proof.thm ht hσ hs ih
  | conv hc _ ih => exact proof.conv hc ih

end Verifier
