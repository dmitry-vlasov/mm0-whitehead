/-
The type word through the commands (milestone V3, part b): binders well-formed, the
dependency of a variable and of an application in each mode, and a node's meaning kept
when a dummy extends the context.
-/
import Verifier.Store

namespace Verifier

open mm0

/-! ### Binders well-formed -/

/-- What `LoadArgs` establishes of the binders: a bound binder's dependency set is its
own number, a regular binder depends on bound binders before it. -/
def BindersWF (bs : List Binder) : Prop :=
  ∀ i b, bs[i]? = some b →
    (b.bound = true → b.deps = {countBefore bs i}) ∧ (b.bound = false → ∀ k ∈ b.deps, k < countBefore bs i)

theorem countBefore_mono (bs : List Binder) {i j : ℕ} (h : i ≤ j) : countBefore bs i ≤ countBefore bs j := by
  unfold countBefore
  have : List.range j = List.range i ++ List.range' i (j - i) := by
    rw [List.range_eq_range', List.range_eq_range']
    have := @List.range'_append 0 i (j - i) 1
    simp only [Nat.zero_add, Nat.one_mul] at this
    rw [this]
    congr 1
    omega
  rw [this, List.filter_append, List.length_append]
  omega

theorem countBefore_le_nb (bs : List Binder) {i : ℕ} (h : i ≤ bs.length) :
    countBefore bs i ≤ (boundNumbers bs).length := by
  rw [← countBefore_length]
  exact countBefore_mono bs h

/-! ### The dependency of a variable -/

theorem has_var_var_bound {Γ : ctx} {u : ℕ} {s : ℕ} (hu : Γ[u]? = some (binder.bound s)) (w : ℕ) :
    sexpr.has_var Γ (sexpr.var u) w ↔ u = w := by
  simp only [sexpr.has_var, hu, Option.some.injEq, exists_eq_left']

theorem has_var_var_reg {Γ : ctx} {u : ℕ} {s : ℕ} {vs : Finset ℕ} (hu : Γ[u]? = some (binder.reg s vs)) (w : ℕ) :
    sexpr.has_var Γ (sexpr.var u) w ↔ w ∈ vs := by
  simp only [sexpr.has_var, hu, Option.some.injEq, exists_eq_left']

theorem dep_var (E : env) (bs : List Binder) (ds : List ℕ) (isDef : Bool) (u k : ℕ) :
    Dep E bs ds isDef (sexpr.var u) k ↔ sexpr.has_var (ctxOf bs ds) (sexpr.var u) (bvVar bs k) := by
  unfold Dep
  cases isDef <;> simp [sexpr.free, sexpr.free']

theorem dep_app_thm (E : env) (bs : List Binder) (ds : List ℕ) (t : ℕ) (es : List sexpr) (k : ℕ) :
    Dep E bs ds false (sexpr.app t es) k ↔ ∃ e ∈ es, Dep E bs ds false e k := by
  unfold Dep
  simp only [Bool.false_eq_true, ite_false]
  exact has_var_app _ _ _ _

/-! ### A variable the expression has is in the context -/

theorem image_bvVar_lt {bs : List Binder} (hwf : BindersWF bs) {i : ℕ} {b : Binder} (hb : bs[i]? = some b)
    (hreg : b.bound = false) {w : ℕ} (hw : w ∈ b.deps.image (bvVar bs)) : w < bs.length := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hw
  have hlt := (hwf i b hb).2 hreg k hk
  have hi := (List.getElem?_eq_some_iff.1 hb).1
  exact bvVar_lt_of_lt (lt_of_lt_of_le hlt (countBefore_le_nb bs (le_of_lt hi)))

theorem has_var_lt {bs : List Binder} (hwf : BindersWF bs) {ds : List ℕ} :
    ∀ {e : sexpr} {w : ℕ}, sexpr.VarsLt e (bs.length + ds.length) → sexpr.has_var (ctxOf bs ds) e w →
      w < bs.length + ds.length
  | .var u, w, hlt, h => by
    simp only [sexpr.has_var] at h
    obtain ⟨bi, hu, h⟩ := h
    by_cases hub : u < bs.length
    · obtain ⟨b, hb⟩ : ∃ b, bs[u]? = some b := ⟨bs[u], List.getElem?_eq_getElem hub⟩
      rw [ctxOf_getElem_binder ds hb] at hu
      simp only [Option.some.injEq] at hu
      subst hu
      cases hbb : b.bound with
      | true =>
        rw [toMm0_bound hbb] at h
        simp only at h
        subst h
        exact hlt
      | false =>
        rw [toMm0_reg hbb] at h
        simp only at h
        have := image_bvVar_lt hwf hb hbb h
        omega
    · have hlt' : u < bs.length + ds.length := hlt
      have hd : u - bs.length < ds.length := Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt hub) hlt'
      have := ctxOf_getElem_dummy bs (List.getElem?_eq_getElem hd)
      rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hub)] at this
      rw [this] at hu
      simp only [Option.some.injEq] at hu
      subst hu
      simp only at h
      subst h
      exact hlt
  | .term _, _, _, h => h.elim
  | .app1 f x, w, hlt, h => by
    rcases h with h | h
    · exact has_var_lt hwf hlt.1 h
    · exact has_var_lt hwf hlt.2 h

theorem free'_lt {E : env} {bs : List Binder} (hwf : BindersWF bs) {ds : List ℕ} {w : ℕ} :
    ∀ {e : sexpr} {es : List sexpr} {ps : List Prop}, sexpr.VarsLt e (bs.length + ds.length) →
      (∀ e' ∈ es, sexpr.VarsLt e' (bs.length + ds.length)) →
      (∀ (n : ℕ), ∀ p ∈ ps[n]?, p → w < bs.length + ds.length) →
      sexpr.free' E (ctxOf bs ds) w e es ps → w < bs.length + ds.length
  | .var u, _, _, hlt, _, _, h => has_var_lt hwf hlt h
  | .term f, es, ps, _, hes, hps, h => by
    simp only [sexpr.free'] at h
    obtain ⟨args, r, rs, o, _, h⟩ := h
    rcases h with ⟨n, p, a, hn, _, hp, _⟩ | ⟨u, _, hu⟩
    · exact hps n p hn hp
    · have hmem := List.mem_of_getElem? hu
      have := hes _ hmem
      simpa [sexpr.VarsLt] using this
  | .app1 f x, es, ps, hlt, hes, hps, h => by
    simp only [sexpr.free'] at h
    refine free'_lt hwf hlt.1 ?_ ?_ h
    · intro e' he'
      rcases List.mem_cons.1 he' with rfl | he'
      · exact hlt.2
      · exact hes e' he'
    · intro n p hp hpp
      cases n with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.mem_def, Option.some.injEq] at hp
        subst hp
        exact free'_lt hwf hlt.2 (fun _ h => by simp at h) (fun _ _ h => by simp at h) hpp
      | succ n =>
        simp only [List.getElem?_cons_succ] at hp
        exact hps n p hp hpp

theorem free_lt {E : env} {bs : List Binder} (hwf : BindersWF bs) {ds : List ℕ} {e : sexpr} {w : ℕ}
    (hlt : sexpr.VarsLt e (bs.length + ds.length)) (h : sexpr.free E (ctxOf bs ds) e w) :
    w < bs.length + ds.length :=
  free'_lt hwf hlt (fun _ h => by simp at h) (fun _ _ h => by simp at h) h

theorem dep_lt {E : env} {bs : List Binder} (hwf : BindersWF bs) {ds : List ℕ} {isDef : Bool} {e : sexpr} {k : ℕ}
    (hlt : sexpr.VarsLt e (bs.length + ds.length)) (h : Dep E bs ds isDef e k) : bvVar bs k < bs.length + ds.length := by
  unfold Dep at h
  cases isDef with
  | true => exact free_lt hwf hlt h
  | false => exact has_var_lt hwf hlt h

/-! ### A dummy extends the context -/

/-- A node keeps its meaning when a dummy is added and the store grows by a node. -/
theorem nodeOk_dummy_ext {E : env} {bs : List Binder} (hwf : BindersWF bs) {ds : List ℕ} {isDef : Bool}
    {store : List Node} (hstore : StoreWF store) (s : ℕ) (m : Node) {p : ℕ} {n : Node} (hn : store[p]? = some n)
    (h : NodeOk E bs ds isDef store p n) : NodeOk E bs (ds ++ [s]) isDef (store ++ [m]) p n := by
  have hp : p < store.length := (List.getElem?_eq_some_iff.1 hn).1
  have hvars := h.varsLt
  have hvars' : sexpr.VarsLt (toSexpr store p) (ctxOf bs ds).length := by
    rw [ctxOf_length]
    exact hvars
  have hsx := toSexpr_append hstore m hp
  refine ⟨?_, ?_, ?_⟩
  · rw [hsx, ctxOf_append]
    exact ok'_append h.ok
  · rw [h.bound]
    constructor
    · rintro ⟨v, s', hnv, hv⟩
      refine ⟨v, s', hnv, ?_⟩
      rw [ctxOf_append, getElem?_append_of_lt (List.getElem?_eq_some_iff.1 hv).1]
      exact hv
    · rintro ⟨v, s', hnv, hv⟩
      refine ⟨v, s', hnv, ?_⟩
      have hvl : v < (ctxOf bs ds).length := by
        rw [hnv] at hn
        rw [toSexpr_var hn] at hvars'
        simpa [sexpr.VarsLt] using hvars'
      rw [ctxOf_append, getElem?_append_of_lt hvl] at hv
      exact hv
  · intro k
    rw [hsx]
    have hdep : Dep E bs (ds ++ [s]) isDef (toSexpr store p) k ↔ Dep E bs ds isDef (toSexpr store p) k := by
      unfold Dep
      rw [ctxOf_append]
      cases isDef
      · simp only [Bool.false_eq_true, ite_false]
        exact has_var_append hvars'
      · simp only [ite_true]
        exact free_append hvars'
    rw [hdep, h.deps k]
    have hnbv : nbv bs (ds ++ [s]) = nbv bs ds + 1 := by
      unfold nbv
      rw [List.length_append, List.length_singleton]
      omega
    rw [hnbv]
    constructor
    · rintro ⟨hk, hd⟩
      exact ⟨by omega, hd⟩
    · rintro ⟨hk, hd⟩
      refine ⟨?_, hd⟩
      by_contra hlt
      have hk' : k = nbv bs ds := by omega
      have h1 := dep_lt hwf hvars hd
      rw [hk', bvVar_of_ge (by unfold nbv; omega)] at h1
      unfold nbv at h1
      omega

end Verifier
