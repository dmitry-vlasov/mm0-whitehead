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

open Unify

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

end Theory
