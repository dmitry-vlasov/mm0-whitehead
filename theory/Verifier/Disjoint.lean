/-
The disjointness conditions of a `Thm` step (milestone V3, part e): what `thmDisjoint`
says position by position, and from it `safe_subst` of the semantics.
-/
import Verifier.RunFacts

namespace Verifier

open mm0


/-- What `thmDisjoint` has seen after the first `m` positions. -/
structure Seen (st : State) (bs : List Binder) (ps : List ℕ) (m : ℕ) (seen : List (ℕ × Finset ℕ))
    (earlier : List (Finset ℕ)) : Prop where
  len : seen.length = countBefore bs m
  seen : ∀ i, (hi : i < m) → (hp : i < ps.length) → isBoundAt bs i → (countBefore bs i, depsAt st ps[i]) ∈ seen
  earlier : ∀ i, (hi : i < m) → (hp : i < ps.length) → depsAt st ps[i] ∈ earlier

/-- The conditions at position `j`. -/
def DisjAt (st : State) (bs : List Binder) (ps : List ℕ) (j : ℕ) : Prop :=
  ∀ (hj : j < bs.length) (hjp : j < ps.length),
    (bs[j].bound = true → ∀ i (hi : i < j), Disjoint (depsAt st ps[j]) (depsAt st (ps[i]'(by omega)))) ∧
    (bs[j].bound = false → ∀ i (hi : i < j), isBoundAt bs i → countBefore bs i ∉ bs[j].deps →
      Disjoint (depsAt st ps[j]) (depsAt st (ps[i]'(by omega))))

theorem thmDisjoint_spec {st : State} {bs : List Binder} {ps : List ℕ} (hlen : ps.length = bs.length) :
    ∀ (k m : ℕ) (seen : List (ℕ × Finset ℕ)) (earlier : List (Finset ℕ)), bs.length - m = k → m ≤ bs.length →
      thmDisjoint st (bs.drop m) (ps.drop m) seen earlier → Seen st bs ps m seen earlier →
      ∀ j, m ≤ j → DisjAt st bs ps j
  | 0, m, _, _, hk, hm, _, _, j, hj => by
    intro hjb
    omega
  | k + 1, m, seen, earlier, hk, hm, htd, hseen, j, hj => by
    have hml : m < bs.length := by omega
    have hmp : m < ps.length := by omega
    rw [List.drop_eq_getElem_cons hml, List.drop_eq_getElem_cons hmp] at htd
    obtain ⟨ty, hty, hrest⟩ := htd
    have hdm : depsAt st ps[m] = ty.deps := by simp [depsAt, hty]
    -- the conditions at `m`
    have hatm : DisjAt st bs ps m := by
      intro _ _
      constructor
      · intro hb i hi
        rw [hb] at hrest
        simp only [ite_true] at hrest
        rw [hdm]
        exact hrest.1 _ (hseen.earlier i hi (by omega))
      · intro hb i hi hbi hnot
        rw [hb] at hrest
        simp only [Bool.false_eq_true, ite_false] at hrest
        rw [hdm]
        exact hrest.1 _ (hseen.seen i hi (by omega) hbi) hnot
    by_cases hjm : j = m
    · subst hjm
      exact hatm
    · -- the rest, with the new seen
      have hnext : ∀ (seen' : List (ℕ × Finset ℕ)) (earlier' : List (Finset ℕ)),
          thmDisjoint st (bs.drop (m + 1)) (ps.drop (m + 1)) seen' earlier' → Seen st bs ps (m + 1) seen' earlier' →
          DisjAt st bs ps j :=
        fun seen' earlier' h1 h2 => thmDisjoint_spec hlen k (m + 1) seen' earlier' (by omega) (by omega) h1 h2 j (by omega)
      have hearlier : ∀ i, (hi : i < m + 1) → (hp : i < ps.length) → depsAt st ps[i] ∈ earlier ++ [ty.deps] := by
        intro i hi hp
        by_cases him : i < m
        · exact List.mem_append_left _ (hseen.earlier i him hp)
        · have : i = m := by omega
          subst this
          rw [hdm]
          simp
      cases hb : bs[m].bound
      · rw [hb] at hrest
        simp only [Bool.false_eq_true, ite_false] at hrest
        refine hnext seen (earlier ++ [ty.deps]) hrest.2 ⟨?_, ?_, hearlier⟩
        · rw [hseen.len, countBefore_succ_of_reg]
          rw [not_isBoundAt_iff hml, List.getElem?_eq_getElem hml]
          simp [hb]
        · intro i hi hp hbi
          have him : i < m := by
            by_contra h
            have : i = m := by omega
            subst this
            obtain ⟨b, hb', hbb⟩ := isBoundAt_iff.1 hbi
            rw [List.getElem?_eq_getElem hml] at hb'
            cases hb'
            rw [hb] at hbb
            cases hbb
          exact hseen.seen i him hp hbi
      · rw [hb] at hrest
        simp only [ite_true] at hrest
        have hbm : isBoundAt bs m := isBoundAt_iff.2 ⟨_, List.getElem?_eq_getElem hml, hb⟩
        refine hnext (seen ++ [(seen.length, ty.deps)]) (earlier ++ [ty.deps]) hrest.2 ⟨?_, ?_, hearlier⟩
        · rw [List.length_append, List.length_singleton, hseen.len, countBefore_succ_of_bound hbm]
        · intro i hi hp hbi
          by_cases him : i < m
          · exact List.mem_append_left _ (hseen.seen i him hp hbi)
          · have : i = m := by omega
            subst this
            rw [hdm, hseen.len]
            simp

theorem thmDisjoint_disjAt {st : State} {bs : List Binder} {ps : List ℕ} (hlen : ps.length = bs.length)
    (h : thmDisjoint st bs ps [] []) : ∀ j, DisjAt st bs ps j :=
  fun j => thmDisjoint_spec hlen bs.length 0 [] [] (by omega) (Nat.zero_le _) (by simpa using h)
    ⟨by simp [countBefore], fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    j (Nat.zero_le _)

/-- A bound position `u` and any other position `v` that `u` is not a dependency of: their
arguments' dependencies are disjoint. -/
theorem disjoint_of_thmDisjoint {st : State} {bs : List Binder} {ps : List ℕ} (hlen : ps.length = bs.length)
    (h : thmDisjoint st bs ps [] []) {u v : ℕ} (hu : u < bs.length) (hv : v < bs.length) (hub : bs[u].bound = true)
    (hnot : if bs[v].bound then v ≠ u else countBefore bs u ∉ bs[v].deps) :
    Disjoint (depsAt st (ps[u]'(by omega))) (depsAt st (ps[v]'(by omega))) := by
  have hD := thmDisjoint_disjAt hlen h
  have hubnd : isBoundAt bs u := isBoundAt_iff.2 ⟨_, List.getElem?_eq_getElem hu, hub⟩
  rcases Nat.lt_trichotomy u v with huv | rfl | huv
  · -- `v` after `u`
    cases hvb : bs[v].bound
    · rw [hvb] at hnot
      simp only [Bool.false_eq_true, ite_false] at hnot
      exact ((hD v hv (by omega)).2 hvb u huv hubnd hnot).symm
    · exact ((hD v hv (by omega)).1 hvb u huv).symm
  · rw [hub] at hnot
    simp at hnot
  · -- `v` before `u`
    exact (hD u hu (by omega)).1 hub v huv

/-! ### `safe_subst` -/

theorem has_var_args_var {bs : List Binder} {v u : ℕ} (hv : v < bs.length) :
    sexpr.has_var (bs.map (Binder.toMm0 bs)) (sexpr.var v) u ↔
      if bs[v].bound then v = u else u ∈ bs[v].deps.image (bvVar bs) := by
  have hl : (bs.map (Binder.toMm0 bs))[v]? = some (Binder.toMm0 bs bs[v]) := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hv]
    rfl
  cases hb : bs[v].bound
  · rw [has_var_var_reg (by rw [hl, toMm0_reg hb])]
    simp
  · rw [has_var_var_bound (by rw [hl, toMm0_bound hb])]
    simp

/-- `safe_subst` from the machine's checks: the arguments fit the binders, the
disjointness conditions hold, and the store means its type words, in a theorem. -/
theorem safe_subst_of {E : env} {bs : List Binder} {D : List ℕ} {st : State}
    (hst : StoreOk E bs D false st.store) {tbs : List Binder} {ps : List ℕ}
    (hargs : argsOk st tbs ps) (hdis : thmDisjoint st tbs ps [] []) :
    safe_subst (ctxOf bs D) (tbs.map (Binder.toMm0 tbs)) (ps.map (toSexpr st.store)) := by
  have hlen := argsOk_length hargs
  intro u v hu hv hnv y e2 hy he2
  obtain ⟨s, hus⟩ := hu
  have hul : u < tbs.length := by
    have := (List.getElem?_eq_some_iff.1 hus).1
    simpa using this
  have hvl : v < tbs.length := by simpa using hv
  have hub : tbs[u].bound = true := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hul] at hus
    simp only [Option.map_some, Option.some.injEq] at hus
    cases hb : tbs[u].bound
    · rw [toMm0_reg hb] at hus; cases hus
    · rfl
  -- the condition that `v` does not have `u`
  have hnot : if tbs[v].bound then v ≠ u else countBefore tbs u ∉ tbs[v].deps := by
    rw [has_var_args_var hvl] at hnv
    cases hvb : tbs[v].bound
    · rw [hvb] at hnv
      simp only [Bool.false_eq_true, ite_false] at hnv ⊢
      intro h
      apply hnv
      refine Finset.mem_image.2 ⟨_, h, ?_⟩
      exact bvVar_countBefore hul (isBoundAt_iff.2 ⟨_, List.getElem?_eq_getElem hul, hub⟩)
    · rw [hvb] at hnv
      simpa using hnv
  have hdisj := disjoint_of_thmDisjoint hlen hdis hul hvl hub hnot
  have hup : u < ps.length := by rw [hlen]; exact hul
  have hvp : v < ps.length := by rw [hlen]; exact hvl
  -- the node at `u`: a bound variable `y`, its dependency the number of `y`
  obtain ⟨tyu, htyu, _, hbu⟩ := argsOk_get hargs u tbs[u] (ps[u]'hup) (List.getElem?_eq_getElem hul)
    (List.getElem?_eq_getElem hup)
  obtain ⟨nu, hnu, rfl⟩ := State.ty_some htyu
  have hoku := hst.nodes _ nu hnu
  obtain ⟨y', s', hnuv, hy'⟩ := hoku.bound.1 (hbu hub)
  rw [hnuv] at hnu
  have hsx := toSexpr_var hnu
  rw [List.getElem?_map, List.getElem?_eq_getElem hup, Option.map_some, hsx] at hy
  simp only [Option.some.injEq, sexpr.var.injEq] at hy
  subst hy
  obtain ⟨k, hk, hky⟩ := bvVar_of_bound hy'
  have hku : k ∈ depsAt st ps[u] := by
    simp only [depsAt, htyu, Option.map_some, Option.getD_some]
    rw [hoku.deps k, hsx]
    refine ⟨hk, ?_⟩
    unfold Dep
    simp only [Bool.false_eq_true, ite_false]
    rw [has_var_var_bound hy', hky]
  -- the node at `v`
  rw [List.getElem?_map, List.getElem?_eq_getElem hvp, Option.map_some, Option.some.injEq] at he2
  subst he2
  intro hhas
  obtain ⟨tyv, htyv, _, _⟩ := argsOk_get hargs v tbs[v] (ps[v]'hvp) (List.getElem?_eq_getElem hvl)
    (List.getElem?_eq_getElem hvp)
  obtain ⟨nv, hnv', rfl⟩ := State.ty_some htyv
  have hkv : k ∈ depsAt st ps[v] := by
    simp only [depsAt, htyv, Option.map_some, Option.getD_some]
    rw [(hst.nodes _ nv hnv').deps k]
    refine ⟨hk, ?_⟩
    unfold Dep
    simp only [Bool.false_eq_true, ite_false]
    rw [hky]
    exact hhas
  exact Finset.disjoint_left.1 hdisj hku hkv

end Verifier
