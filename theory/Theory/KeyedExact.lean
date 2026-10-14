/-
The keyed engine against the reference engine, exactly, for an oriented postulate
(`docs/THEORY.md`, "The production engine", milestone 16).

With an oriented unifier (`Oriented.lean`) the join of restricted members *equals* the
join of the full members on every variable the restriction did not drop
(`joinAll_restrict_eq`): the restricted join extended by the dropped bindings
(`Subst.extend`) is an oriented idempotent unifier of the full problem and an instance
of its join, and the join an instance of it, so the two are equal. Two members with the
same restriction give joins equal off their dropped variables (`joinAll_key_eq`).
-/
import Theory.Oriented
import Theory.KeyedCorr

namespace Theory

open Unify State

/-- Every join of an oriented postulate is oriented. -/
theorem joinAll_oriented (U : Unification) (hU : U.Oriented) :
    ∀ (θs : List Subst) (J : Subst), U.joinAll θs = some J → J.Oriented
  | [], J, h => by
    simp only [Unification.joinAll, Option.some.injEq] at h
    subst h
    exact Subst.Oriented.id
  | θ :: θs, J, h => by
    cases hη : U.joinAll θs with
    | none => rw [Unification.joinAll, hη] at h; simp at h
    | some η =>
      rw [Unification.joinAll, hη] at h
      exact hU _ J h

/-- A variable that the join of the restricted members mentions is not one the
restriction dropped. -/
theorem restrictJoin_not_dropped (U : Unification) {θ : Subst} (V : Finset Var) {L₁ L₂ : List Subst}
    (hθ : θ.Idem) (hL : ∀ η ∈ L₁ ++ L₂, ApartBelow θ V η)
    {J' : Subst} (hJ' : U.joinAll (L₁ ++ θ.restrict V :: L₂) = some J') :
    ∀ w, J'.Mentions w → w ∈ θ.dom → w ∈ V := by
  intro w hw hwd
  obtain ⟨σ, hσ, hm⟩ := joinAll_mentions U _ J' hJ' w hw
  simp only [List.mem_append, List.mem_cons] at hσ
  rcases hσ with hσ | rfl | hσ
  · by_contra hV
    exact hL σ (List.mem_append_left _ hσ) w hwd hV hm
  · rcases hm with hm | ⟨u, hu, hm⟩
    · have hm' : w ∈ θ.dom.filter (· ∈ V) := hm
      exact (Finset.mem_filter.1 hm').2
    · have hu' : u ∈ θ.dom.filter (· ∈ V) := hu
      have huV : u ∈ V := (Finset.mem_filter.1 hu').2
      rw [Subst.restrict_f_of_mem huV] at hm
      exact absurd hwd (hθ.not_mem_dom hm)
  · by_contra hV
    exact hL σ (List.mem_append_right _ hσ) w hwd hV hm

/-- **Restriction, exactly**: for an oriented postulate the join with a member and the
join with its restriction agree on every variable the restriction did not drop. -/
theorem joinAll_restrict_eq (U : Unification) (hU : U.Oriented) {θ : Subst} (V : Finset Var) {L₁ L₂ : List Subst}
    (hθ : θ.Idem) (hθt : θ.Typed) (hθo : θ.Oriented) (hidem : ∀ σ ∈ L₁ ++ θ :: L₂, σ.Idem)
    (hL : ∀ η ∈ L₁ ++ L₂, ApartBelow θ V η)
    {J J' : Subst} (hJ : U.joinAll (L₁ ++ θ :: L₂) = some J) (hJ' : U.joinAll (L₁ ++ θ.restrict V :: L₂) = some J') :
    ∀ v, (v ∈ θ.dom → v ∈ V) → J.f v = J'.f v := by
  have hidem' := idem_middle (hθ.restrict V) hidem
  obtain ⟨hJt, hJi, hJa⟩ := (joinAll_spec U hidem).1 J hJ
  obtain ⟨hJt', hJi', hJa'⟩ := (joinAll_spec U hidem').1 J' hJ'
  have hJo : J.Oriented := joinAll_oriented U hU _ J hJ
  have hJo' : J'.Oriented := joinAll_oriented U hU _ J' hJ'
  -- `J` absorbs `J'`, and `θ`
  have hJJ' : J.comp J' = J := by
    obtain ⟨J₀, hJ₀, habs⟩ := (joinAll_spec U hidem').2 J hJt (hJa.restrict V)
    rw [hJ'] at hJ₀
    obtain rfl := Option.some.inj hJ₀
    exact habs
  have hJθ : J.comp θ = J := (absorbsAll_middle.1 hJa).1
  have hnd := restrictJoin_not_dropped U V hθ hL hJ'
  -- `E`: `J'` extended by the dropped bindings
  set E := J'.extend θ V with hE
  have hEvis : ∀ v, (v ∈ θ.dom → v ∈ V) → E.f v = J'.f v := fun v hv => Subst.extend_f_visible hv
  have hEbelow : ∀ v, v ∈ θ.dom → v ∉ V → E.f v = J'.apply (θ.f v) := fun v hd hv => Subst.extend_f_below hd hv
  have hnot : ∀ v, ¬ (v ∈ θ.dom ∧ v ∉ V) → (v ∈ θ.dom → v ∈ V) := fun v hv h => by
    by_contra h'
    exact hv ⟨h, h'⟩
  -- a variable of an image of `E` is fixed by `J'` and not dropped
  have hEvars : ∀ v w, w ∈ (E.f v).vars → J'.f w = .var w ∧ (w ∈ θ.dom → w ∈ V) := by
    intro v w hw
    by_cases hv : v ∈ θ.dom ∧ v ∉ V
    · rw [hEbelow v hv.1 hv.2, Subst.vars_apply, Finset.mem_biUnion] at hw
      obtain ⟨u, hu, hw⟩ := hw
      refine ⟨Subst.f_eq_of_not_mem (hJi'.not_mem_dom hw), ?_⟩
      by_cases huJ : u ∈ J'.dom
      · exact fun hwd => hnd w (Or.inr ⟨u, huJ, hw⟩) hwd
      · rw [Subst.f_eq_of_not_mem huJ] at hw
        simp only [Exp.vars, Finset.mem_singleton] at hw
        subst hw
        exact fun hwd => absurd hwd (hθ.not_mem_dom hu)
    · rw [hEvis v (hnot v hv)] at hw
      refine ⟨Subst.f_eq_of_not_mem (hJi'.not_mem_dom hw), ?_⟩
      by_cases hvJ : v ∈ J'.dom
      · exact fun hwd => hnd w (Or.inr ⟨v, hvJ, hw⟩) hwd
      · rw [Subst.f_eq_of_not_mem hvJ] at hw
        simp only [Exp.vars, Finset.mem_singleton] at hw
        subst hw
        exact hnot w hv
  -- `E` is idempotent
  have hEi : E.Idem := by
    apply Subst.ext
    funext v
    show E.apply (E.f v) = E.f v
    apply apply_eq_self_of_apart
    intro w hw
    obtain ⟨hfix, hnd'⟩ := hEvars v w hw
    have hEw : E.f w = .var w := by rw [hEvis w hnd', hfix]
    exact fun hd => (E.hdom w).1 hd hEw
  -- `E` is oriented
  have hEo : E.Oriented := by
    intro v r hvr hne
    by_cases hv : v ∈ θ.dom ∧ v ∉ V
    · rw [hEbelow v hv.1 hv.2] at hvr
      obtain ⟨w, hw⟩ := Subst.apply_eq_var hvr
      rw [hw, Subst.apply_var] at hvr
      have hwv : w ≠ v := by
        intro h
        subst h
        exact (θ.hdom w).1 hv.1 hw
      have hb1 : Var.before w v := hθo v w hw hwv
      by_cases hrw : r = w
      · subst hrw
        exact hb1
      · exact Var.before_trans (hJo' w r hvr hrw) hb1
    · rw [hEvis v (hnot v hv)] at hvr
      exact hJo' v r hvr hne
  -- `E` and `J` are instances of each other
  have hEt : E.Typed := Subst.extend_typed hJt' hθt V
  have hEabs : AbsorbsAll E (L₁ ++ θ :: L₂) := hJa'.extend hθ hL
  have hEJ : E.IsInstance J := by
    obtain ⟨J₀, hJ₀, habs⟩ := (joinAll_spec U hidem).2 E hEt hEabs
    rw [hJ] at hJ₀
    obtain rfl := Option.some.inj hJ₀
    exact ⟨E, habs.symm⟩
  have hJE : J.IsInstance E := by
    refine ⟨J, ?_⟩
    apply Subst.ext
    funext v
    show J.f v = J.apply (E.f v)
    by_cases hv : v ∈ θ.dom ∧ v ∉ V
    · rw [hEbelow v hv.1 hv.2, ← Subst.apply_comp, hJJ']
      exact (congrArg (fun τ => τ.f v) hJθ).symm
    · rw [hEvis v (hnot v hv)]
      exact (congrArg (fun τ => τ.f v) hJJ').symm
  have hEJeq : E = J := oriented_unique hEi hJi hEo hJo hEJ hJE
  intro v hv
  rw [← hEJeq, hEvis v hv]

/-- **Key, exactly**: two members with the same restriction give joins that agree on
every variable neither restriction dropped. -/
theorem joinAll_key_eq (U : Unification) (hU : U.Oriented) {θ₁ θ₂ : Subst} (V : Finset Var) {L₁ L₂ : List Subst}
    (h₁ : θ₁.Idem) (h₁t : θ₁.Typed) (h₁o : θ₁.Oriented) (h₂ : θ₂.Idem) (h₂t : θ₂.Typed) (h₂o : θ₂.Oriented)
    (hidem : ∀ σ ∈ L₁ ++ L₂, σ.Idem)
    (hL₁ : ∀ η ∈ L₁ ++ L₂, ApartBelow θ₁ V η) (hL₂ : ∀ η ∈ L₁ ++ L₂, ApartBelow θ₂ V η)
    (hkey : θ₁.restrict V = θ₂.restrict V)
    {J₁ J₂ : Subst} (hJ₁ : U.joinAll (L₁ ++ θ₁ :: L₂) = some J₁) (hJ₂ : U.joinAll (L₁ ++ θ₂ :: L₂) = some J₂) :
    ∀ v, (v ∈ θ₁.dom → v ∈ V) → (v ∈ θ₂.dom → v ∈ V) → J₁.f v = J₂.f v := by
  have hidem₁ : ∀ σ ∈ L₁ ++ θ₁ :: L₂, σ.Idem := by
    intro σ hσ
    simp only [List.mem_append, List.mem_cons] at hσ hidem
    rcases hσ with hσ | rfl | hσ
    · exact hidem σ (Or.inl hσ)
    · exact h₁
    · exact hidem σ (Or.inr hσ)
  have hidem₂ : ∀ σ ∈ L₁ ++ θ₂ :: L₂, σ.Idem := by
    intro σ hσ
    simp only [List.mem_append, List.mem_cons] at hσ hidem
    rcases hσ with hσ | rfl | hσ
    · exact hidem σ (Or.inl hσ)
    · exact h₂
    · exact hidem σ (Or.inr hσ)
  obtain ⟨J', hJ'⟩ := (joinAll_restrict_exists U V h₁ h₁t hidem₁ hL₁).1 ⟨J₁, hJ₁⟩
  have e₁ := joinAll_restrict_eq U hU V h₁ h₁t h₁o hidem₁ hL₁ hJ₁ hJ'
  rw [hkey] at hJ'
  have e₂ := joinAll_restrict_eq U hU V h₂ h₂t h₂o hidem₂ hL₂ hJ₂ hJ'
  intro v hv₁ hv₂
  rw [e₁ v hv₁, e₂ v hv₂]


/-! ### The engine's substitutions are oriented -/

theorem anode_sub_oriented {U : Unification} (hU : U.Oriented) {db : Database} {st : Statement} {s : State}
    (hs : StateInv U db st s) {j : ℕ} (hj : j < s.anodes.size) : s.anodes[j]!.sub.Oriented := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  exact hU _ _ hA.is_mgu

theorem entry_sub_oriented {U : Unification} (hU : U.Oriented) {st : Statement} {s : State} :
    ∀ (fuel i : ℕ), ∀ E ∈ sptE U st s fuel i, E.sub.Oriented
  | 0, _, E, hE => by simp [sptE] at hE
  | fuel + 1, i, E, hE => by
    simp only [sptE, List.mem_append, List.mem_flatMap] at hE
    rcases hE with hE | ⟨j, _, hE⟩
    · simp only [leafEntries, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hE
      obtain ⟨h, _, θ, hθ, rfl⟩ := hE
      exact hU _ _ hθ
    · simp only [anodeEntries, List.mem_filterMap] at hE
      obtain ⟨tup, _, hmk⟩ := hE
      split at hmk
      · simp at hmk
      · rename_i θ hθ
        split at hmk
        · simp only [Option.some.injEq] at hmk
          subst hmk
          exact joinAll_oriented U hU _ _ hθ
        · simp at hmk

/-! ### Restriction, exactly, in the engine -/

theorem restrict_step_eq {U : Unification} (hU : U.Oriented) {db : Database} {st : Statement} {s : State}
    (hs : StateInv U db st s) (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) {k : ℕ}
    (hk : k < s.anodes[j]!.children.length) {θ : Subst} (hθ : Member s st j k θ) (hθo : θ.Oriented)
    {L₁ L₂ : List Subst}
    (hmem : ∀ η ∈ L₁ ++ L₂, η = s.anodes[j]!.sub ∨ ∃ k', k' < s.anodes[j]!.children.length ∧ k' ≠ k ∧ Member s st j k' η)
    {J J' : Subst} (hJ : U.joinAll (L₁ ++ θ :: L₂) = some J)
    (hJ' : U.joinAll (L₁ ++ θ.restrict (visible st s s.anodes[j]!.children[k]!) :: L₂) = some J') :
    ∀ v, (v ∈ θ.dom → v ∈ visible st s s.anodes[j]!.children[k]!) → J.f v = J'.f v := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  have hidem : ∀ σ ∈ L₁ ++ θ :: L₂, σ.Idem := by
    intro σ hσ
    simp only [List.mem_append, List.mem_cons] at hσ
    rcases hσ with hσ | rfl | hσ
    · rcases hmem σ (List.mem_append_left _ hσ) with rfl | ⟨_, _, _, h⟩
      · exact hA.idem
      · exact h.idem
    · exact hθ.idem
    · rcases hmem σ (List.mem_append_right _ hσ) with rfl | ⟨_, _, _, h⟩
      · exact hA.idem
      · exact h.idem
  have hL : ∀ η ∈ L₁ ++ L₂, ApartBelow θ (visible st s s.anodes[j]!.children[k]!) η := by
    intro η hη w hw hwV hm
    rcases hθ.mentions w (Or.inl hw) with h | ⟨T, hT, j', hj', hb⟩
    · exact hwV h
    · obtain ⟨_, h2, h3⟩ := block_apart hs hwf hj hk hT hj' hb
      rcases hmem η hη with rfl | ⟨k', hk', hne, hη'⟩
      · exact h2 hm
      · exact h3 k' hk' hne η hη' hm
  exact joinAll_restrict_eq U hU _ hθ.idem hθ.typed hθo hidem hL hJ hJ'

theorem restrict_chain_eq {U : Unification} (hU : U.Oriented) {db : Database} {st : Statement} {s : State}
    (hs : StateInv U db st s) (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) :
    ∀ (σs τs : List Subst) (m : ℕ) (L₁ : List Subst),
      σs.length = τs.length → m + σs.length = s.anodes[j]!.children.length →
      (∀ η ∈ L₁, η = s.anodes[j]!.sub ∨ ∃ k', k' < m ∧ Member s st j k' η) →
      (∀ l, (hl : l < σs.length) → Member s st j (m + l) σs[l] ∧ σs[l].Oriented) →
      (∀ l, (hl : l < σs.length) → (hl' : l < τs.length) →
        τs[l] = σs[l].restrict (visible st s s.anodes[j]!.children[m + l]!)) →
      ∀ J J', U.joinAll (L₁ ++ σs) = some J → U.joinAll (L₁ ++ τs) = some J' →
        ∀ v, (∀ l, (hl : l < σs.length) → v ∈ σs[l].dom → v ∈ visible st s s.anodes[j]!.children[m + l]!) →
          J.f v = J'.f v
  | [], [], m, L₁, _, _, _, _, _, J, J', hJ, hJ', v, _ => by
    rw [hJ] at hJ'
    obtain rfl := Option.some.inj hJ'
    rfl
  | σ :: σs, τ :: τs, m, L₁, hlen, hm, hL₁, hσs, hτs, J, J', hJ, hJ', v, hv => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hm' : m < s.anodes[j]!.children.length := by simp only [List.length_cons] at hm; omega
    have hσ := hσs 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hσ
    have hτ0 := hτs 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hτ0
    subst hτ0
    have hv0 := hv 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hv0
    have hmem : ∀ η ∈ L₁ ++ σs, η = s.anodes[j]!.sub ∨
        ∃ k', k' < s.anodes[j]!.children.length ∧ k' ≠ m ∧ Member s st j k' η := by
      intro η hη
      rcases List.mem_append.1 hη with hη | hη
      · rcases hL₁ η hη with h | ⟨k', hk', h⟩
        · exact Or.inl h
        · exact Or.inr ⟨k', by omega, by omega, h⟩
      · obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hη
        have := hσs (l + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        exact Or.inr ⟨m + (l + 1), by simp only [List.length_cons] at hm; omega, by omega, this.1⟩
    obtain ⟨hex, _⟩ := restrict_step hs hwf hj hm' hσ.1 hmem
    obtain ⟨Jm, hJm⟩ := hex.1 ⟨J, hJ⟩
    have e1 := restrict_step_eq hU hs hwf hj hm' hσ.1 hσ.2 hmem hJ hJm v hv0
    have hassoc : ∀ (ρ : Subst) (ρs : List Subst), (L₁ ++ [ρ]) ++ ρs = L₁ ++ ρ :: ρs := by
      intro ρ ρs; simp
    have e2 := restrict_chain_eq hU hs hwf hj σs τs (m + 1) (L₁ ++ [σ.restrict (visible st s s.anodes[j]!.children[m]!)])
      hlen (by simp only [List.length_cons] at hm; omega)
      (by
        intro η hη
        rcases List.mem_append.1 hη with hη | hη
        · rcases hL₁ η hη with h | ⟨k', hk', h⟩
          · exact Or.inl h
          · exact Or.inr ⟨k', by omega, h⟩
        · simp only [List.mem_singleton] at hη
          subst hη
          exact Or.inr ⟨m, by omega, hσ.1.restrict _⟩)
      (fun l hl => by
        have := hσs (l + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show m + 1 + l = m + (l + 1) by omega]
        exact this)
      (fun l hl hl' => by
        have := hτs (l + 1) (by simp; omega) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show m + 1 + l = m + (l + 1) by omega]
        exact this)
      Jm J' (by rw [hassoc]; exact hJm) (by rw [hassoc]; exact hJ')
      v (fun l hl => by
        have := hv (l + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show m + 1 + l = m + (l + 1) by omega]
        exact this)
    rw [e1, e2]

/-! ### Facts about the variables of conditions -/

/-- A variable of an expression under an idempotent substitution is not in its domain. -/
theorem vars_apply_not_mem_dom {θ : Subst} (hθ : θ.Idem) {e : Exp} {w : Var} (hw : w ∈ (θ.apply e).vars) :
    w ∉ θ.dom := by
  rw [Subst.vars_apply, Finset.mem_biUnion] at hw
  obtain ⟨u, _, hw⟩ := hw
  exact hθ.not_mem_dom hw

/-- A visible variable of the parent that a child's entry binds is visible at the child. -/
theorem visible_not_dropped {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j k : ℕ} (hj : j < s.anodes.size) (hk : k < s.anodes[j]!.children.length) {E : Entry}
    (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!) {v : Var} (hv : v ∈ visible st s s.anodes[j]!.parent)
    (hd : v ∈ E.sub.dom) : v ∈ visible st s s.anodes[j]!.children[k]! := by
  rcases (Member.of_entry hs hwf hj hk hE).mentions v (Or.inl hd) with h | ⟨T, hT, j', hj', hb⟩
  · exact h
  · exact absurd hv (block_apart hs hwf hj hk hT hj' hb).1

/-- The variables of an assertion node's conditions: of the parent's expression, or in
the node's block. -/
theorem anode_conds_vars {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) : ∀ k ∈ s.anodes[j]!.conds, ∀ u ∈ k.1.vars ∪ k.2.vars,
      u ∈ s.enodes[s.anodes[j]!.parent]!.expr.vars ∨ s.InBlock j u := by
  intro k hk u hu
  obtain ⟨A, hA⟩ := hs.anodes j hj
  rw [hA.conds, nodeConds, List.mem_map] at hk
  obtain ⟨p, hp', rfl⟩ := hk
  have key : ∀ x ∈ A.vars, u ∈ (s.anodes[j]!.sub.apply (.var (renamed s.anodes[j]!.base x))).vars →
      u ∈ s.enodes[s.anodes[j]!.parent]!.expr.vars ∨ s.InBlock j u := by
    intro x hx hu
    rw [Subst.apply_var] at hu
    by_cases hd : renamed s.anodes[j]!.base x ∈ s.anodes[j]!.sub.dom
    · exact anode_mentions hs hwf hj (Or.inr ⟨_, hd, hu⟩)
    · rw [Subst.f_eq_of_not_mem hd] at hu
      simp only [Exp.vars, Finset.mem_singleton] at hu
      subst hu
      rw [hs.base_eq j hj]
      exact Or.inr (State.inBlock_renamed hs (List.mem_of_getElem? hA.assertion) hx j)
  have hpairs := (hwf A (List.mem_of_getElem? hA.assertion)).pairs_vars p hp'
  rcases Finset.mem_union.1 hu with hu | hu
  · exact key p.1 hpairs.1 hu
  · exact key p.2 hpairs.2 hu

/-- The variables of the conditions of a tree at `c`: of `c`'s expression, or in a block
of the tree. -/
theorem tree_conds_vars {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) : ∀ {c : ℕ} {T : SptTree}, T.At s c → ∀ k ∈ T.conds s, ∀ u ∈ k.1.vars ∪ k.2.vars,
      u ∈ s.enodes[c]!.expr.vars ∨ ∃ j' ∈ T.anodes, s.InBlock j' u := by
  intro c T hat
  induction hat with
  | leaf => intro k hk; simp [SptTree.conds] at hk
  | node i j cs hj hp hlen hcs ih =>
    intro k hk u hu
    simp only [SptTree.conds, List.mem_append, SptTree.condsList_eq_flatMap, List.mem_flatMap] at hk
    rcases hk with hk | ⟨t, ht, hk⟩
    · rcases anode_conds_vars hs hwf hj k hk u hu with h | h
      · rw [hp] at h
        exact Or.inl h
      · exact Or.inr ⟨j, by simp [SptTree.anodes], h⟩
    · obtain ⟨k', hk', rfl⟩ := List.mem_iff_getElem.1 ht
      have := ih k' hk' k (by rwa [getElem!_pos cs k' hk']) u hu
      rcases this with h | ⟨j', hj', hb⟩
      · rcases child_expr_vars hs hwf hj (hlen ▸ hk') h with h | h
        · rw [hp] at h
          exact Or.inl h
        · exact Or.inr ⟨j, by simp [SptTree.anodes], h⟩
      · refine Or.inr ⟨j', ?_, hb⟩
        simp only [SptTree.anodes, List.mem_cons]
        rw [getElem!_pos cs k' hk'] at hj'
        exact Or.inr ((SptTree.mem_anodesList' cs).2 ⟨cs[k'], List.getElem_mem hk', hj'⟩)

/-- The variables of an entry's conditions: visible at its node, or in a block of its
tree. -/
theorem entry_conds_vars {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel c : ℕ} (hc : c < s.enodes.size) {E : Entry} (hE : E ∈ sptE U st s fuel c) :
    ∀ k ∈ E.conds, ∀ w ∈ k.1.vars ∪ k.2.vars, w ∈ visible st s c ∨ ∃ j' ∈ E.tree.anodes, s.InBlock j' w := by
  have hinv := sptE_inv hs fuel c hc E hE
  intro k hk w hw
  rw [hinv.conds, List.mem_map] at hk
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  have hw' : ∃ u ∈ k₀.1.vars ∪ k₀.2.vars, w ∈ (E.sub.f u).vars := by
    simp only [Cond.apply] at hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Subst.vars_apply, Finset.mem_biUnion] at hw
      obtain ⟨u, hu, hw⟩ := hw
      exact ⟨u, Finset.mem_union_left _ hu, hw⟩
    · rw [Subst.vars_apply, Finset.mem_biUnion] at hw
      obtain ⟨u, hu, hw⟩ := hw
      exact ⟨u, Finset.mem_union_right _ hu, hw⟩
  obtain ⟨u, hu, hw⟩ := hw'
  by_cases hd : u ∈ E.sub.dom
  · rcases entry_mentions hs hwf fuel c hc E hE w (Or.inr ⟨u, hd, hw⟩) with h | h | h
    · exact Or.inl (Finset.mem_union_right _ h)
    · exact Or.inl (Finset.mem_union_left _ h)
    · exact Or.inr h
  · rw [Subst.f_eq_of_not_mem hd] at hw
    simp only [Exp.vars, Finset.mem_singleton] at hw
    subst hw
    rcases tree_conds_vars hs hwf hinv.at_ k₀ hk₀ w hu with h | h
    · exact Or.inl (Finset.mem_union_left _ h)
    · exact Or.inr h


/-! ### The judgement -/

/-- Pending, for a condition already under `J`: the name is a variable in the image of
`V` under `J`, or a constant and the expression has a variable left (`judgeK`). -/
def isPending (J : Subst) (V : Finset Var) (k : Cond) : Bool :=
  match k.1 with
  | .var y => decide (y ∈ imageVars J V)
  | _ => decide (¬ k.2.vars = ∅)

theorem judgeK_spec (c : Consts) (st : Statement) (e : Exp) (J : Subst) (k : Cond) :
    judgeK c st e J k = if (k.apply J).Holds c then some (isPending J (e.vars ∪ st.vars) (k.apply J)) else none := by
  simp only [judgeK, isPending]
  by_cases hh : (Cond.apply J k).Holds c
  · simp only [hh, not_true_eq_false, ite_false, ite_true]
    cases hk : (Cond.apply J k).1 with
    | var y =>
      by_cases hy : y ∈ imageVars J (e.vars ∪ st.vars) <;> simp [hk, hy]
    | const k' t =>
      by_cases hv : (Cond.apply J k).2.vars = ∅ <;> simp [hk, hv]
    | app f t args =>
      by_cases hv : (Cond.apply J k).2.vars = ∅ <;> simp [hk, hv]
  · simp [hh]

theorem judgeAll_spec (c : Consts) (st : Statement) (e : Exp) (J : Subst) :
    ∀ ks : List Cond, judgeAll c st e J ks =
      if ∀ k ∈ ks, (k.apply J).Holds c then
        some ((ks.map (Cond.apply J)).filter (isPending J (e.vars ∪ st.vars)))
      else none
  | [] => by simp [judgeAll]
  | k :: ks => by
    rw [judgeAll, judgeK_spec, judgeAll_spec c st e J ks]
    by_cases hh : (k.apply J).Holds c
    · rw [ite_eq_left hh]
      by_cases hall : ∀ k' ∈ ks, (k'.apply J).Holds c
      · have hall' : ∀ k' ∈ k :: ks, (k'.apply J).Holds c := List.forall_mem_cons.2 ⟨hh, hall⟩
        cases hp : isPending J (e.vars ∪ st.vars) (k.apply J)
        · dsimp only
          rw [ite_eq_left hall, ite_eq_left hall', List.map_cons, List.filter_cons, hp]
          simp
        · dsimp only
          rw [ite_eq_left hall, ite_eq_left hall', List.map_cons, List.filter_cons, hp]
          simp
      · have hall' : ¬ ∀ k' ∈ k :: ks, (k'.apply J).Holds c := fun h => hall fun k' hk' => h k' (List.mem_cons_of_mem _ hk')
        cases hp : isPending J (e.vars ∪ st.vars) (k.apply J)
        · dsimp only
          rw [ite_eq_right hall, ite_eq_right hall']
        · dsimp only
          rw [ite_eq_right hall, ite_eq_right hall']
          rfl
    · rw [ite_eq_right hh]
      dsimp only
      rw [ite_eq_right (fun h => hh (h k (List.mem_cons_self ..)))]

/-! ### Conditions of the children at the parent -/

/-- A variable of a condition of a child's entry that an entry of a child binds is
visible at that child. -/
theorem cond_var_not_dropped {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j k k' : ℕ} (hj : j < s.anodes.size) (hk : k < s.anodes[j]!.children.length)
    (hk' : k' < s.anodes[j]!.children.length) {E E' : Entry} (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!)
    (hE' : E' ∈ sptE U st s fuel s.anodes[j]!.children[k']!) (hEE : k' = k → E' = E)
    {c : Cond} (hc : c ∈ E.conds) {w : Var} (hw : w ∈ c.1.vars ∪ c.2.vars) (hd : w ∈ E'.sub.dom) :
    w ∈ visible st s s.anodes[j]!.children[k']! := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  have hck := (hA.children k hk).1
  have hinv := sptE_inv hs fuel _ hck E hE
  rcases entry_conds_vars hs hwf hck hE c hc w hw with hv | ⟨j', hj', hb⟩
  · rcases (Member.of_entry hs hwf hj hk' hE').mentions w (Or.inl hd) with h | ⟨T, hT, j'', hj'', hb'⟩
    · exact h
    · exfalso
      obtain ⟨h1, h2, h3⟩ := below_apart hs hj hk' hT hj'' hb'
      rcases Finset.mem_union.1 hv with hv | hv
      · rcases child_expr_vars hs hwf hj hk hv with h | h
        · exact h1 h
        · exact h2 h
      · exact h3 hv
  · by_cases hkk : k' = k
    · subst hkk
      obtain rfl := hEE rfl
      exfalso
      rw [hinv.conds, List.mem_map] at hc
      obtain ⟨c₀, _, rfl⟩ := hc
      rcases Finset.mem_union.1 hw with hw | hw
      · exact vars_apply_not_mem_dom hinv.idem hw hd
      · exact vars_apply_not_mem_dom hinv.idem hw hd
    · exact absurd (Or.inl hd) ((block_apart hs hwf hj hk hinv.at_ hj' hb).2.2 k' hk' hkk E'.sub (Member.of_entry hs hwf hj hk' hE'))

/-- A variable of the node's own conditions that a child's entry binds is visible at
that child. -/
theorem anode_cond_var_not_dropped {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j k : ℕ} (hj : j < s.anodes.size) (hk : k < s.anodes[j]!.children.length) {E : Entry}
    (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!) {c : Cond} (hc : c ∈ s.anodes[j]!.conds) {w : Var}
    (hw : w ∈ c.1.vars ∪ c.2.vars) (hd : w ∈ E.sub.dom) : w ∈ visible st s s.anodes[j]!.children[k]! := by
  rcases (Member.of_entry hs hwf hj hk hE).mentions w (Or.inl hd) with h | ⟨T, hT, j'', hj'', hb'⟩
  · exact h
  · exfalso
    obtain ⟨h1, h2, _⟩ := below_apart hs hj hk hT hj'' hb'
    rcases anode_conds_vars hs hwf hj c hc w hw with h | h
    · exact h1 h
    · exact h2 h

/-- A condition of a child's entry that is not pending at the child: its name is a
variable in a block of the entry's tree, not visible at the child, that the restricted
entry does not mention; or a constant, and the expression has no variable left. -/
theorem not_pending_name {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j k : ℕ} (hj : j < s.anodes.size) (hk : k < s.anodes[j]!.children.length) {E : Entry}
    (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!) {c : Cond} (hc : c ∈ E.conds)
    (hnp : isPending E.sub (visible st s s.anodes[j]!.children[k]!) c = false) :
    (∃ y, c.1 = .var y ∧ y ∉ visible st s s.anodes[j]!.children[k]! ∧ (∃ j' ∈ E.tree.anodes, s.InBlock j' y) ∧
      ¬ (E.sub.restrict (visible st s s.anodes[j]!.children[k]!)).Mentions y) ∨
    ((∀ y, c.1 ≠ .var y) ∧ c.2.vars = ∅) := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  have hck := (hA.children k hk).1
  have hinv := sptE_inv hs fuel _ hck E hE
  unfold isPending at hnp
  cases hc1 : c.1 with
  | var y =>
    rw [hc1] at hnp
    simp only [decide_eq_false_iff_not] at hnp
    have hyd : y ∉ E.sub.dom := by
      rw [hinv.conds, List.mem_map] at hc
      obtain ⟨c₀, _, rfl⟩ := hc
      have h1 : E.sub.apply c₀.1 = .var y := hc1
      exact vars_apply_not_mem_dom hinv.idem (e := c₀.1) (by rw [h1]; simp [Exp.vars])
    have hyf : E.sub.f y = .var y := Subst.f_eq_of_not_mem hyd
    have himage : y ∈ visible st s s.anodes[j]!.children[k]! → y ∈ imageVars E.sub (visible st s s.anodes[j]!.children[k]!) :=
      fun hyV => Finset.mem_biUnion.2 ⟨y, hyV, by rw [hyf]; simp [Exp.vars]⟩
    left
    refine ⟨y, rfl, fun hyV => hnp (himage hyV), ?_, ?_⟩
    · have hy : y ∈ c.1.vars ∪ c.2.vars := Finset.mem_union_left _ (by rw [hc1]; simp [Exp.vars])
      rcases entry_conds_vars hs hwf hck hE c hc y hy with h | h
      · exact absurd (himage h) hnp
      · exact h
    · rintro (hd | ⟨u, hu, hyu⟩)
      · have hd' : y ∈ E.sub.dom.filter (· ∈ visible st s s.anodes[j]!.children[k]!) := hd
        exact hyd (Finset.mem_filter.1 hd').1
      · have hu' : u ∈ E.sub.dom.filter (· ∈ visible st s s.anodes[j]!.children[k]!) := hu
        have huV := (Finset.mem_filter.1 hu').2
        rw [Subst.restrict_f_of_mem huV] at hyu
        exact hnp (Finset.mem_biUnion.2 ⟨u, huV, hyu⟩)
  | const k' t =>
    rw [hc1] at hnp
    simp only [decide_eq_false_iff_not, not_not] at hnp
    exact Or.inr ⟨fun y h => Exp.noConfusion h, hnp⟩
  | app f t args =>
    rw [hc1] at hnp
    simp only [decide_eq_false_iff_not, not_not] at hnp
    exact Or.inr ⟨fun y h => Exp.noConfusion h, hnp⟩

/-- The name of a settled condition at the parent: the join of the node's unifier with
the restricted entries of the children — the `k`-th the given entry's, the others
members — does not mention it, and it is not visible there. -/
theorem settled_at_parent {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j k : ℕ} (hj : j < s.anodes.size) (hk : k < s.anodes[j]!.children.length) {E : Entry}
    (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!) {y : Var} (hyb : ∃ j' ∈ E.tree.anodes, s.InBlock j' y)
    (hym : ¬ (E.sub.restrict (visible st s s.anodes[j]!.children[k]!)).Mentions y) {ms : List Subst}
    (hms : ∀ k', (hk' : k' < ms.length) →
      (k' = k ∧ ms[k'] = E.sub.restrict (visible st s s.anodes[j]!.children[k]!)) ∨
      (k' ≠ k ∧ k' < s.anodes[j]!.children.length ∧ Member s st j k' ms[k']))
    {J : Subst} (hJ : U.joinAll (s.anodes[j]!.sub :: ms) = some J) :
    ¬ J.Mentions y ∧ y ∉ visible st s s.anodes[j]!.parent := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  have hinv := sptE_inv hs fuel _ (hA.children k hk).1 E hE
  obtain ⟨j', hj', hb⟩ := hyb
  obtain ⟨h1, h2, h3⟩ := block_apart hs hwf hj hk hinv.at_ hj' hb
  refine ⟨fun hm => ?_, h1⟩
  obtain ⟨σ, hσ, hmσ⟩ := joinAll_mentions U _ J hJ y hm
  rcases List.mem_cons.1 hσ with rfl | hσ
  · exact h2 hmσ
  · obtain ⟨k', hk', rfl⟩ := List.mem_iff_getElem.1 hσ
    rcases hms k' hk' with ⟨_, heq⟩ | ⟨hne, hk'', hmem⟩
    · rw [heq] at hmσ
      exact hym hmσ
    · exact h3 k' hk'' hne _ hmem hmσ

/-! ### Two list facts -/

theorem flatMap_congr_index {α β γ : Type} {f : α → List γ} {g : β → List γ} :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (∀ l, (hl : l < xs.length) → (hl' : l < ys.length) → f xs[l] = g ys[l]) → xs.flatMap f = ys.flatMap g
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, hlen, h => by
    simp only [List.flatMap_cons]
    have h0 := h 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    rw [h0, flatMap_congr_index xs ys (by simpa using hlen) fun l hl hl' => by
      have := h (l + 1) (by simp; omega) (by simp; omega)
      simpa using this]

theorem filter_map_filter {α β : Type} {f : α → β} {p : β → Bool} {q : α → Bool} :
    ∀ l : List α, (∀ c ∈ l, q c = false → p (f c) = false) →
      ((l.filter q).map f).filter p = (l.map f).filter p
  | [], _ => rfl
  | c :: l, h => by
    have ih := filter_map_filter l fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    by_cases hq : q c = true
    · rw [List.filter_cons_of_pos hq, List.map_cons, List.map_cons, List.filter_cons, List.filter_cons, ih]
    · have hq' : q c = false := by simpa using hq
      rw [List.filter_cons_of_neg hq, ih, List.map_cons, List.filter_cons, h c (List.mem_cons_self ..) hq']
      simp

theorem app_not_mem_names (c : Consts) (f : ℕ) (t : Ty) (args : List Exp) (e : Exp) :
    Exp.app f t args ∉ c.names e := by
  intro h
  rw [Consts.mem_names] at h
  rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;> cases h

/-! ### A joined tuple -/

/-- A keyed entry against a reference entry at node `i`, exactly: its restricted answer
and its pending conditions. -/
structure KEq (st : Statement) (s : State) (i : ℕ) (K : KEntry) (E : Entry) : Prop where
  sub : K.sub = E.sub.restrict (visible st s i)
  conds : K.conds = E.conds.filter (isPending E.sub (visible st s i))

/-- A tuple of reference entries at the children of `j`, the keyed entries that are
their restrictions, and the two joins at `j`. -/
structure Joined (U : Unification) (st : Statement) (s : State) (fuel j : ℕ) (etup : List Entry)
    (ktup : List KEntry) (J θ : Subst) : Prop where
  len : etup.length = s.anodes[j]!.children.length
  klen : ktup.length = etup.length
  mem : ∀ l, (hl : l < etup.length) → etup[l] ∈ sptE U st s fuel s.anodes[j]!.children[l]!
  keq : ∀ l, (hl : l < etup.length) → KEq st s s.anodes[j]!.children[l]! ktup[l]! etup[l]
  hJ : U.joinAll (s.anodes[j]!.sub :: ktup.map (·.sub)) = some J
  hθ : U.joinAll (s.anodes[j]!.sub :: etup.map (·.sub)) = some θ

namespace Joined

variable {U : Unification} {db : Database} {st : Statement} {s : State} {fuel j : ℕ} {etup : List Entry}
  {ktup : List KEntry} {J θ : Subst}

theorem lt_children (h : Joined U st s fuel j etup ktup J θ) {l : ℕ} (hl : l < etup.length) :
    l < s.anodes[j]!.children.length := h.len ▸ hl

theorem lt_ktup (h : Joined U st s fuel j etup ktup J θ) {l : ℕ} (hl : l < etup.length) : l < ktup.length :=
  h.klen ▸ hl

/-- The `l`-th keyed member. -/
theorem member_eq (h : Joined U st s fuel j etup ktup J θ) {l : ℕ} (hl : l < etup.length) :
    (ktup.map (·.sub))[l]'(by simp [h.klen, hl]) = etup[l].sub.restrict (visible st s s.anodes[j]!.children[l]!) := by
  rw [List.getElem_map, ← getElem!_pos ktup l (h.lt_ktup hl)]
  exact (h.keq l hl).sub

/-- The joins agree on every variable no child's entry dropped. -/
theorem eq_nondropped (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) {v : Var}
    (hv : ∀ l, (hl : l < etup.length) → v ∈ etup[l].sub.dom → v ∈ visible st s s.anodes[j]!.children[l]!) :
    θ.f v = J.f v := by
  have hσlen : (etup.map (·.sub)).length = etup.length := by simp
  have hτlen : (ktup.map (·.sub)).length = etup.length := by simp [h.klen]
  refine restrict_chain_eq hU hs hwf hj (etup.map (·.sub)) (ktup.map (·.sub)) 0 [s.anodes[j]!.sub]
    (by rw [hσlen, hτlen]) (by rw [hσlen, Nat.zero_add]; exact h.len)
    (by intro η hη; simp only [List.mem_singleton] at hη; exact Or.inl hη)
    (fun l hl => by
      rw [hσlen] at hl
      simp only [List.getElem_map, Nat.zero_add]
      exact ⟨Member.of_entry hs hwf hj (h.lt_children hl) (h.mem l hl), entry_sub_oriented hU fuel _ _ (h.mem l hl)⟩)
    (fun l hl hl' => by
      rw [hσlen] at hl
      simp only [Nat.zero_add]
      rw [h.member_eq hl, List.getElem_map])
    θ J (by simpa using h.hθ) (by simpa using h.hJ) v
    (fun l hl => by
      rw [hσlen] at hl
      simp only [List.getElem_map, Nat.zero_add]
      exact hv l hl)

/-- The joins agree on the variables visible at the parent. -/
theorem eq_visible (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) {v : Var} (hv : v ∈ visible st s s.anodes[j]!.parent) :
    θ.f v = J.f v :=
  h.eq_nondropped hU hs hwf hj fun l hl hd => visible_not_dropped hs hwf hj (h.lt_children hl) (h.mem l hl) hv hd

theorem restrict_eq (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) :
    J.restrict (visible st s s.anodes[j]!.parent) = θ.restrict (visible st s s.anodes[j]!.parent) := by
  apply Subst.ext
  funext v
  show (if v ∈ _ then J.f v else _) = (if v ∈ _ then θ.f v else _)
  by_cases hv : v ∈ visible st s s.anodes[j]!.parent
  · rw [ite_eq_left hv, ite_eq_left hv, h.eq_visible hU hs hwf hj hv]
  · rw [ite_eq_right hv, ite_eq_right hv]

theorem imageVars_eq (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) :
    imageVars J (visible st s s.anodes[j]!.parent) = imageVars θ (visible st s s.anodes[j]!.parent) :=
  Finset.biUnion_congr rfl fun v hv => by rw [h.eq_visible hU hs hwf hj hv]

theorem isPending_eq (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) :
    isPending J (visible st s s.anodes[j]!.parent) = isPending θ (visible st s s.anodes[j]!.parent) := by
  funext k
  unfold isPending
  rw [h.imageVars_eq hU hs hwf hj]

/-- A condition of the node agrees under the two joins. -/
theorem anode_cond_eq (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) {c : Cond} (hc : c ∈ s.anodes[j]!.conds) :
    c.apply θ = c.apply J := by
  have hv : ∀ w ∈ c.1.vars ∪ c.2.vars, θ.f w = J.f w := fun w hw =>
    h.eq_nondropped hU hs hwf hj fun l hl hd =>
      anode_cond_var_not_dropped hs hwf hj (h.lt_children hl) (h.mem l hl) hc hw hd
  simp only [Cond.apply]
  rw [apply_congr_vars c.1 fun w hw => hv w (Finset.mem_union_left _ hw),
    apply_congr_vars c.2 fun w hw => hv w (Finset.mem_union_right _ hw)]

/-- A condition of a child's entry agrees under the two joins. -/
theorem child_cond_eq (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) {l : ℕ} (hl : l < etup.length) {c : Cond} (hc : c ∈ etup[l].conds) :
    c.apply θ = c.apply J := by
  have hv : ∀ w ∈ c.1.vars ∪ c.2.vars, θ.f w = J.f w := fun w hw =>
    h.eq_nondropped hU hs hwf hj fun l' hl' hd =>
      cond_var_not_dropped hs hwf hj (h.lt_children hl) (h.lt_children hl') (h.mem l hl) (h.mem l' hl')
        (fun heq => by subst heq; rfl) hc hw hd
  simp only [Cond.apply]
  rw [apply_congr_vars c.1 fun w hw => hv w (Finset.mem_union_left _ hw),
    apply_congr_vars c.2 fun w hw => hv w (Finset.mem_union_right _ hw)]

/-- A condition of a child's entry that is settled there holds under the keyed join and
is not pending at the parent. -/
theorem settled_child (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) {l : ℕ} (hl : l < etup.length) {c : Cond} (hc : c ∈ etup[l].conds)
    (hnp : isPending etup[l].sub (visible st s s.anodes[j]!.children[l]!) c = false) :
    (c.apply J).Holds st.consts ∧ isPending J (visible st s s.anodes[j]!.parent) (c.apply J) = false := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  have hlc := h.lt_children hl
  have hinv := sptE_inv hs fuel _ (hA.children l hlc).1 _ (h.mem l hl)
  have hholds := hinv.holds c hc
  rcases not_pending_name hs hwf hj hlc (h.mem l hl) hc hnp with ⟨y, hy1, _, hyb, hym⟩ | ⟨hnv, hclosed⟩
  · have hms : ∀ k', (hk' : k' < (ktup.map (·.sub)).length) →
        (k' = l ∧ (ktup.map (·.sub))[k'] = etup[l].sub.restrict (visible st s s.anodes[j]!.children[l]!)) ∨
        (k' ≠ l ∧ k' < s.anodes[j]!.children.length ∧ Member s st j k' (ktup.map (·.sub))[k']) := by
      intro k' hk'
      have hk'' : k' < etup.length := by simpa [h.klen] using hk'
      by_cases hkl : k' = l
      · subst hkl
        exact Or.inl ⟨rfl, h.member_eq hk''⟩
      · refine Or.inr ⟨hkl, h.lt_children hk'', ?_⟩
        rw [h.member_eq hk'']
        exact (Member.of_entry hs hwf hj (h.lt_children hk'') (h.mem k' hk'')).restrict _
    obtain ⟨hnm, hnv⟩ := settled_at_parent hs hwf hj hlc (h.mem l hl) hyb hym hms h.hJ
    have hc' : c = (Exp.var y, c.2) := Prod.ext hy1 rfl
    refine ⟨?_, ?_⟩
    · rw [hc']
      rw [hc'] at hholds
      exact (settled hnm c.2 st.consts).2 hholds
    · unfold isPending
      have h1 : (c.apply J).1 = .var y := by
        simp only [Cond.apply, hy1, Subst.apply_var]
        exact Subst.f_eq_of_not_mentions hnm
      rw [h1]
      simp only [decide_eq_false_iff_not]
      intro hy
      obtain ⟨v, hv, hyv⟩ := Finset.mem_biUnion.1 hy
      by_cases hvd : v ∈ J.dom
      · exact hnm (Or.inr ⟨v, hvd, hyv⟩)
      · rw [Subst.f_eq_of_not_mem hvd] at hyv
        simp only [Exp.vars, Finset.mem_singleton] at hyv
        subst hyv
        exact hnv hv
  · have h2 : (c.apply J).2 = c.2 := apply_eq_self_of_apart J c.2 fun w hw => by rw [hclosed] at hw; simp at hw
    cases hc1 : c.1 with
    | var y => exact absurd hc1 (hnv y)
    | const k' t =>
      have h1 : (c.apply J).1 = .const k' t := by simp [Cond.apply, hc1]
      refine ⟨?_, ?_⟩
      · have : c.apply J = c := Prod.ext (h1.trans hc1.symm) h2
        rw [this]
        exact hholds
      · unfold isPending
        rw [h1, h2]
        simp [hclosed]
    | app f t args =>
      have h1 : ∃ args', (c.apply J).1 = .app f t args' := ⟨J.applyList args, by simp [Cond.apply, hc1, Subst.apply]⟩
      obtain ⟨args', h1⟩ := h1
      refine ⟨?_, ?_⟩
      · show (c.apply J).1 ∉ st.consts.names (c.apply J).2
        rw [h1]
        exact app_not_mem_names _ _ _ _ _
      · unfold isPending
        rw [h1, h2]
        simp [hclosed]


theorem mem_ktup (h : Joined U st s fuel j etup ktup J θ) {l : ℕ} (hl : l < etup.length) : ktup[l]! ∈ ktup := by
  rw [getElem!_pos ktup l (h.lt_ktup hl)]
  exact List.getElem_mem _

/-- The conditions the keyed engine judges at the node all hold under its join exactly
when all the reference engine's hold under its join. -/
theorem all_hold_iff (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) :
    (∀ c ∈ s.anodes[j]!.conds ++ ktup.flatMap (·.conds), (c.apply J).Holds st.consts) ↔
    (∀ c ∈ s.anodes[j]!.conds ++ etup.flatMap (·.conds), (c.apply θ).Holds st.consts) := by
  constructor
  · intro hall c hc
    rcases List.mem_append.1 hc with hc | hc
    · rw [h.anode_cond_eq hU hs hwf hj hc]
      exact hall c (List.mem_append_left _ hc)
    · rw [List.mem_flatMap] at hc
      obtain ⟨E, hE, hcE⟩ := hc
      obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hE
      rw [h.child_cond_eq hU hs hwf hj hl hcE]
      by_cases hp : isPending etup[l].sub (visible st s s.anodes[j]!.children[l]!) c = true
      · apply hall c
        refine List.mem_append_right _ (List.mem_flatMap.2 ⟨ktup[l]!, h.mem_ktup hl, ?_⟩)
        rw [(h.keq l hl).conds, List.mem_filter]
        exact ⟨hcE, hp⟩
      · exact (h.settled_child hU hs hwf hj hl hcE (by simpa using hp)).1
  · intro hall c hc
    rcases List.mem_append.1 hc with hc | hc
    · rw [← h.anode_cond_eq hU hs hwf hj hc]
      exact hall c (List.mem_append_left _ hc)
    · rw [List.mem_flatMap] at hc
      obtain ⟨K, hK, hcK⟩ := hc
      obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hK
      have hl' : l < etup.length := h.klen ▸ hl
      rw [← getElem!_pos ktup l hl, (h.keq l hl').conds, List.mem_filter] at hcK
      rw [← h.child_cond_eq hU hs hwf hj hl' hcK.1]
      exact hall c (List.mem_append_right _ (List.mem_flatMap.2 ⟨etup[l], List.getElem_mem hl', hcK.1⟩))

theorem filter_map_flatMap {α β γ : Type} (f : α → List β) (g : β → γ) (p : γ → Bool) :
    ∀ l : List α, ((l.flatMap f).map g).filter p = l.flatMap fun a => ((f a).map g).filter p
  | [] => rfl
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.filter_append]
    rw [filter_map_flatMap f g p l]

/-- The pending conditions of the keyed engine at the node are the reference entry's
conditions filtered to the pending ones. -/
theorem pending_eq (hU : U.Oriented) (hs : StateInv U db st s) (hwf : db.WF) (hj : j < s.anodes.size)
    (h : Joined U st s fuel j etup ktup J θ) :
    ((s.anodes[j]!.conds ++ ktup.flatMap (·.conds)).map (Cond.apply J)).filter
        (isPending J (visible st s s.anodes[j]!.parent)) =
      ((s.anodes[j]!.conds ++ etup.flatMap (·.conds)).map (Cond.apply θ)).filter
        (isPending θ (visible st s s.anodes[j]!.parent)) := by
  rw [← h.isPending_eq hU hs hwf hj]
  simp only [List.map_append, List.filter_append, filter_map_flatMap]
  congr 1
  · congr 1
    exact List.map_congr_left fun c hc => (h.anode_cond_eq hU hs hwf hj hc).symm
  · apply flatMap_congr_index ktup etup h.klen
    intro l hl hl'
    rw [← getElem!_pos ktup l hl, (h.keq l hl').conds,
      filter_map_filter _ fun c hc hq => (h.settled_child hU hs hwf hj hl' hc hq).2]
    congr 1
    exact List.map_congr_left fun c hc => (h.child_cond_eq hU hs hwf hj hl' hc).symm

end Joined

/-! ### Entries built -/

theorem mem_anodeEntries_of {U : Unification} {c : Consts} {j : ℕ} {a : ANode} {sets : List (List Entry)}
    {tup : List Entry} {θ : Subst} (htup : tup ∈ tuples sets) (hθ : U.joinAll (a.sub :: tup.map (·.sub)) = some θ)
    (hall : ∀ k ∈ (a.conds ++ tup.flatMap (·.conds)).map (Cond.apply θ), k.Holds c) :
    ({ tree := .node j (tup.map (·.tree)), sub := θ,
       conds := (a.conds ++ tup.flatMap (·.conds)).map (Cond.apply θ) } : Entry) ∈ anodeEntries U c j a sets := by
  simp only [anodeEntries, List.mem_filterMap]
  refine ⟨tup, htup, ?_⟩
  rw [hθ]
  have h : ((a.conds ++ tup.flatMap (·.conds)).map (Cond.apply θ)).all (fun k => decide (k.Holds c)) = true :=
    List.all_eq_true.2 fun k hk => decide_eq_true (hall k hk)
  simp only [h, ite_true]

theorem leaf_conds_nil {U : Unification} {st : Statement} {i : ℕ} {e : Exp} {E : Entry}
    (hE : E ∈ leafEntries U st i e) : E.conds = [] := by
  simp only [leafEntries, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hE
  obtain ⟨_, _, _, _, rfl⟩ := hE
  rfl

theorem KEntry.conds_eq_of_sameKey {K K' : KEntry} (h : K.sameKey K' = true) : K.conds = K'.conds := by
  simp only [KEntry.sameKey, Bool.and_eq_true] at h
  exact beq_iff_eq.1 h.2

/-! ### The correspondence, exactly -/

/-- **Soundness, exactly**: every keyed entry stands for a reference entry with its
tree, whose restricted answer it has, with the reference entry's conditions filtered to
the pending ones. -/
theorem keyed_sound_ex {U : Unification} (hU : U.Oriented) {db : Database} {st : Statement} {s : State}
    (hs : StateInv U db st s) (hwf : db.WF) : ∀ (fuel i : ℕ), i < s.enodes.size → ∀ K ∈ keyedE U st s fuel i,
      ∃ E ∈ sptE U st s fuel i, K.tree = E.tree ∧ KEq st s i K E
  | 0, _, _, _, hK => by simp [keyedE] at hK
  | fuel + 1, i, hi, K, hK => by
    simp only [keyedE, List.mem_append, List.mem_flatMap] at hK
    rcases hK with hK | ⟨j, hj, hK⟩
    · simp only [leafK, List.mem_map] at hK
      obtain ⟨E, hE, rfl⟩ := hK
      exact ⟨E, by simp [sptE, hE], rfl, ⟨rfl, by simp [leaf_conds_nil hE]⟩⟩
    · obtain ⟨hj, hp⟩ := (mem_aChildren s i j).1 hj
      obtain ⟨A, hA⟩ := hs.anodes j hj
      have hK' := mem_of_mem_dedupKeys hK
      simp only [List.mem_filterMap] at hK'
      obtain ⟨tup, htup, hmk⟩ := hK'
      obtain ⟨hlen, hk⟩ := mem_tuplesK _ tup htup
      simp only [List.length_map] at hlen hk
      have hmemk : ∀ k, (hk' : k < tup.length) → tup[k] ∈ keyedE U st s fuel s.anodes[j]!.children[k]! := by
        intro k hk'
        have := hk k (hlen ▸ hk')
        rw [getElem!_map _ _ k (hlen ▸ hk'), getElem!_pos tup k hk'] at this
        exact this
      have ih : ∀ k, (hk' : k < tup.length) → ∃ E ∈ sptE U st s fuel s.anodes[j]!.children[k]!,
          tup[k].tree = E.tree ∧ KEq st s s.anodes[j]!.children[k]! tup[k] E :=
        fun k hk' => keyed_sound_ex hU hs hwf fuel _ (hA.children k (hlen ▸ hk')).1 _ (hmemk k hk')
      let pick : Fin tup.length → Entry := fun k => Classical.choose (ih k k.2)
      have hpick : ∀ k : Fin tup.length, pick k ∈ sptE U st s fuel s.anodes[j]!.children[k]! ∧
          tup[k].tree = (pick k).tree ∧ KEq st s s.anodes[j]!.children[k]! tup[k] (pick k) :=
        fun k => Classical.choose_spec (ih k k.2)
      let etup : List Entry := List.ofFn pick
      have hetlen : etup.length = tup.length := List.length_ofFn
      have hetget : ∀ k (hk' : k < tup.length), etup[k]'(by rw [hetlen]; exact hk') = pick ⟨k, hk'⟩ :=
        fun k hk' => List.getElem_ofFn _
      have hetup : etup ∈ tuples (s.anodes[j]!.children.map fun c => sptE U st s fuel c) := by
        refine mem_tuples_of_index _ etup (by simp [hetlen, hlen]) fun k hk' => ?_
        simp only [List.length_map] at hk'
        rw [getElem!_map _ _ k hk', getElem!_pos etup k (by rw [hetlen, hlen]; exact hk'), hetget k (hlen ▸ hk')]
        exact (hpick ⟨k, hlen ▸ hk'⟩).1
      split at hmk
      · exact absurd hmk (by simp)
      · rename_i J hJ
        have hjoined : ∀ θ, U.joinAll (s.anodes[j]!.sub :: etup.map (·.sub)) = some θ →
            Joined U st s fuel j etup tup J θ := fun θ hθ =>
          { len := by rw [hetlen, hlen]
            klen := hetlen.symm
            mem := fun l hl => by rw [hetget l (hetlen ▸ hl)]; exact (hpick ⟨l, hetlen ▸ hl⟩).1
            keq := fun l hl => by
              rw [hetget l (hetlen ▸ hl), getElem!_pos tup l (hetlen ▸ hl)]
              exact (hpick ⟨l, hetlen ▸ hl⟩).2.2
            hJ := hJ
            hθ := hθ }
        -- the reference join exists: the chain of restrictions
        have hex : ∃ θ, U.joinAll (s.anodes[j]!.sub :: etup.map (·.sub)) = some θ := by
          have hflen : (etup.map (·.sub)).length = tup.length := by simp [hetlen]
          have hτlen : (tup.map (·.sub)).length = tup.length := by simp
          have hchain := restrict_chain hs hwf hj (etup.map (·.sub)) (tup.map (·.sub)) 0 [s.anodes[j]!.sub]
            (by rw [hflen, hτlen]) (by rw [hflen]; omega)
            (by intro η hη; simp only [List.mem_singleton] at hη; exact Or.inl hη)
            (fun l hl => by
              rw [hflen] at hl
              simp only [List.getElem_map, Nat.zero_add]
              rw [hetget l hl]
              exact Member.of_entry hs hwf hj (hlen ▸ hl) (hpick ⟨l, hl⟩).1)
            (fun l hl hl' => by
              rw [hflen] at hl
              simp only [List.getElem_map, Nat.zero_add]
              rw [hetget l hl]
              exact (hpick ⟨l, hl⟩).2.2.sub)
          obtain ⟨θ, hθ⟩ := hchain.1.2 ⟨J, by simpa using hJ⟩
          exact ⟨θ, by simpa using hθ⟩
        obtain ⟨θ, hθ⟩ := hex
        have hjd := hjoined θ hθ
        rw [judgeAll_spec] at hmk
        split at hmk
        · rename_i hall
          simp only [Option.map_some, Option.some.injEq] at hmk
          subst hmk
          have hallθ := (hjd.all_hold_iff hU hs hwf hj).1 hall
          refine ⟨({ tree := .node j (etup.map (·.tree)), sub := θ,
                     conds := (s.anodes[j]!.conds ++ etup.flatMap (·.conds)).map (Cond.apply θ) } : Entry),
            ?_, ?_, ⟨?_, ?_⟩⟩
          · simp only [sptE, List.mem_append, List.mem_flatMap]
            exact Or.inr ⟨j, (mem_aChildren s i j).2 ⟨hj, hp⟩, mem_anodeEntries_of hetup hθ fun k hk => by
              obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hk
              exact hallθ c hc⟩
          · show SptTree.node j (tup.map (·.tree)) = SptTree.node j (etup.map (·.tree))
            congr 1
            apply List.ext_getElem (by simp [hetlen])
            intro k hk1 hk2
            simp only [List.getElem_map]
            have hk' : k < tup.length := by simpa using hk1
            rw [hetget k hk']
            exact (hpick ⟨k, hk'⟩).2.1
          · show J.restrict (visible st s i) = θ.restrict (visible st s i)
            have := hjd.restrict_eq hU hs hwf hj
            rwa [hp] at this
          · show ((s.anodes[j]!.conds ++ tup.flatMap (·.conds)).map (Cond.apply J)).filter
                (isPending J (s.enodes[i]!.expr.vars ∪ st.vars)) = _
            have := hjd.pending_eq hU hs hwf hj
            rw [hp] at this
            exact this
        · simp at hmk

/-- **Completeness, exactly**: every reference entry has a keyed entry with its
restricted answer and its pending conditions — the one kept for that key. -/
theorem keyed_complete_ex {U : Unification} (hU : U.Oriented) {db : Database} {st : Statement} {s : State}
    (hs : StateInv U db st s) (hwf : db.WF) : ∀ (fuel i : ℕ), i < s.enodes.size → ∀ E ∈ sptE U st s fuel i,
      ∃ K ∈ keyedE U st s fuel i, KEq st s i K E
  | 0, _, _, _, hE => by simp [sptE] at hE
  | fuel + 1, i, hi, E, hE => by
    simp only [sptE, List.mem_append, List.mem_flatMap] at hE
    rcases hE with hE | ⟨j, hj, hE⟩
    · refine ⟨{ tree := E.tree, sub := E.sub.restrict (visible st s i), conds := [] }, ?_, ⟨rfl, by simp [leaf_conds_nil hE]⟩⟩
      simp only [keyedE, List.mem_append, leafK, List.mem_map]
      exact Or.inl ⟨E, hE, rfl⟩
    · obtain ⟨hj, hp⟩ := (mem_aChildren s i j).1 hj
      obtain ⟨A, hA⟩ := hs.anodes j hj
      simp only [anodeEntries, List.mem_filterMap] at hE
      obtain ⟨etup, hetup, hmk⟩ := hE
      obtain ⟨hlen, hk⟩ := mem_tuples _ etup hetup
      simp only [List.length_map] at hlen hk
      have hmemk : ∀ k, (hk' : k < etup.length) → etup[k] ∈ sptE U st s fuel s.anodes[j]!.children[k]! := by
        intro k hk'
        have := hk k (hlen ▸ hk')
        rw [getElem!_map _ _ k (hlen ▸ hk'), getElem!_pos etup k hk'] at this
        exact this
      have ih : ∀ k, (hk' : k < etup.length) → ∃ K ∈ keyedE U st s fuel s.anodes[j]!.children[k]!,
          KEq st s s.anodes[j]!.children[k]! K etup[k] :=
        fun k hk' => keyed_complete_ex hU hs hwf fuel _ (hA.children k (hlen ▸ hk')).1 _ (hmemk k hk')
      let pick : Fin etup.length → KEntry := fun k => Classical.choose (ih k k.2)
      have hpick : ∀ k : Fin etup.length, pick k ∈ keyedE U st s fuel s.anodes[j]!.children[k]! ∧
          KEq st s s.anodes[j]!.children[k]! (pick k) etup[k] :=
        fun k => Classical.choose_spec (ih k k.2)
      let ktup : List KEntry := List.ofFn pick
      have hktlen : ktup.length = etup.length := List.length_ofFn
      have hktget : ∀ k (hk' : k < etup.length), ktup[k]'(by rw [hktlen]; exact hk') = pick ⟨k, hk'⟩ :=
        fun k hk' => List.getElem_ofFn _
      have hktup : ktup ∈ tuplesK (s.anodes[j]!.children.map fun c => keyedE U st s fuel c) := by
        refine mem_tuplesK_of_index _ ktup (by simp [hktlen, hlen]) fun k hk' => ?_
        simp only [List.length_map] at hk'
        rw [getElem!_map _ _ k hk', getElem!_pos ktup k (by rw [hktlen, hlen]; exact hk'), hktget k (hlen ▸ hk')]
        exact (hpick ⟨k, hlen ▸ hk'⟩).1
      split at hmk
      · exact absurd hmk (by simp)
      · rename_i θ hθ
        have hEeq : E = ({ tree := .node j (etup.map (·.tree)), sub := θ,
                           conds := (s.anodes[j]!.conds ++ etup.flatMap (·.conds)).map (Cond.apply θ) } : Entry) ∧
            ∀ c ∈ s.anodes[j]!.conds ++ etup.flatMap (·.conds), (c.apply θ).Holds st.consts := by
          split at hmk
          · rename_i hall
            simp only [Option.some.injEq] at hmk
            refine ⟨hmk.symm, fun c hc => ?_⟩
            have := List.all_eq_true.1 hall _ (List.mem_map_of_mem (f := Cond.apply θ) hc)
            exact of_decide_eq_true this
          · exact absurd hmk (by simp)
        obtain ⟨rfl, hallθ⟩ := hEeq
        have hjoined : ∀ J, U.joinAll (s.anodes[j]!.sub :: ktup.map (·.sub)) = some J →
            Joined U st s fuel j etup ktup J θ := fun J hJ =>
          { len := hlen
            klen := hktlen
            mem := hmemk
            keq := fun l hl => by
              rw [getElem!_pos ktup l (hktlen ▸ hl), hktget l hl]
              exact (hpick ⟨l, hl⟩).2
            hJ := hJ
            hθ := hθ }
        -- the keyed join exists
        have hex : ∃ J, U.joinAll (s.anodes[j]!.sub :: ktup.map (·.sub)) = some J := by
          have hflen : (etup.map (·.sub)).length = etup.length := by simp
          have hτlen : (ktup.map (·.sub)).length = etup.length := by simp [hktlen]
          have hchain := restrict_chain hs hwf hj (etup.map (·.sub)) (ktup.map (·.sub)) 0 [s.anodes[j]!.sub]
            (by rw [hflen, hτlen]) (by rw [hflen]; omega)
            (by intro η hη; simp only [List.mem_singleton] at hη; exact Or.inl hη)
            (fun l hl => by
              rw [hflen] at hl
              simp only [List.getElem_map, Nat.zero_add]
              exact Member.of_entry hs hwf hj (hlen ▸ hl) (hmemk l hl))
            (fun l hl hl' => by
              rw [hflen] at hl
              simp only [List.getElem_map, Nat.zero_add]
              rw [hktget l hl]
              exact (hpick ⟨l, hl⟩).2.sub)
          obtain ⟨J, hJ⟩ := hchain.1.1 ⟨θ, by simpa using hθ⟩
          exact ⟨J, by simpa using hJ⟩
        obtain ⟨J, hJ⟩ := hex
        have hjd := hjoined J hJ
        have hallJ := (hjd.all_hold_iff hU hs hwf hj).2 hallθ
        -- the keyed entry of the tuple, and the one kept for its key
        have hmemA : ∃ K ∈ anodeK U st s i j (s.anodes[j]!.children.map fun c => keyedE U st s fuel c),
            K.sameKey { tree := .node j (ktup.map (·.tree)), sub := J.restrict (visible st s i),
                        conds := ((s.anodes[j]!.conds ++ ktup.flatMap (·.conds)).map (Cond.apply J)).filter
                          (isPending J (s.enodes[i]!.expr.vars ∪ st.vars)) } = true := by
          unfold anodeK
          apply dedupKeys_spec
          simp only [List.mem_filterMap]
          refine ⟨ktup, hktup, ?_⟩
          rw [hJ]
          dsimp only
          rw [judgeAll_spec, ite_eq_left hallJ]
          rfl
        obtain ⟨K, hK, hsk⟩ := hmemA
        refine ⟨K, ?_, ⟨?_, ?_⟩⟩
        · simp only [keyedE, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨j, (mem_aChildren s i j).2 ⟨hj, hp⟩, hK⟩
        · rw [KEntry.sub_eq_of_sameKey hsk]
          show J.restrict (visible st s i) = θ.restrict (visible st s i)
          have := hjd.restrict_eq hU hs hwf hj
          rwa [hp] at this
        · rw [KEntry.conds_eq_of_sameKey hsk]
          show ((s.anodes[j]!.conds ++ ktup.flatMap (·.conds)).map (Cond.apply J)).filter
              (isPending J (s.enodes[i]!.expr.vars ∪ st.vars)) = _
          have := hjd.pending_eq hU hs hwf hj
          rw [hp] at this
          exact this

end Theory
