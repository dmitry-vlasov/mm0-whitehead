/-
The lemma the keyed engine rests on (`docs/THEORY.md`, "The production engine",
milestone 13): two members of a join that give the same answer on the visible
variables up to instance each way, their fresh variables apart from the other members,
are interchangeable — the joins exist together, and give the same answer up to
instance each way on every variable that is visible or fresh to neither. The key of
the production engine is such an answer; which proof is kept per key is then
immaterial above.
-/
import Theory.Engine

namespace Theory

/-- `σ` is an instance of `τ` on `W`: a typed substitution takes what `τ` gives the
variables of `W` to what `σ` gives them. -/
def InstOn (W : Finset Var) (σ τ : Subst) : Prop :=
  ∃ δ : Subst, δ.Typed ∧ ∀ v ∈ W, σ.f v = δ.apply (τ.f v)

/-- The same on `W` up to instance each way. -/
def SameOn (W : Finset Var) (σ τ : Subst) : Prop := InstOn W σ τ ∧ InstOn W τ σ

theorem SameOn.symm {W : Finset Var} {σ τ : Subst} (h : SameOn W σ τ) : SameOn W τ σ := ⟨h.2, h.1⟩

theorem InstOn.refl (W : Finset Var) (σ : Subst) : InstOn W σ σ :=
  ⟨Subst.id, Subst.Typed.id, fun v _ => by simp [Subst.apply_id]⟩

theorem SameOn.refl (W : Finset Var) (σ : Subst) : SameOn W σ σ := ⟨InstOn.refl W σ, InstOn.refl W σ⟩

theorem InstOn.trans {W : Finset Var} {σ τ υ : Subst} (h₁ : InstOn W σ τ) (h₂ : InstOn W τ υ) : InstOn W σ υ := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := h₁
  obtain ⟨δ₂, hδ₂, h₂⟩ := h₂
  exact ⟨δ₁.comp δ₂, Subst.Typed.comp hδ₁ hδ₂, fun v hv => by rw [h₁ v hv, h₂ v hv, Subst.apply_comp]⟩

theorem SameOn.trans {W : Finset Var} {σ τ υ : Subst} (h₁ : SameOn W σ τ) (h₂ : SameOn W τ υ) : SameOn W σ υ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem InstOn.mono {W W' : Finset Var} {σ τ : Subst} (h : InstOn W σ τ) (hW : W' ⊆ W) : InstOn W' σ τ := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun v hv => h v (hW hv)⟩

/-- The variables in the images of a substitution. -/
def Subst.imageVars (σ : Subst) : Finset Var := σ.dom.biUnion fun u => (σ.f u).vars

theorem Subst.mem_imageVars {σ : Subst} {w : Var} : w ∈ σ.imageVars ↔ ∃ u ∈ σ.dom, w ∈ (σ.f u).vars := by
  simp [Subst.imageVars]

theorem Subst.restrict_f_of_not_mem (θ : Subst) {s : Finset Var} {v : Var} (h : v ∉ s) : (θ.restrict s).f v = .var v :=
  Subst.f_eq_of_not_mem fun hd => h (Finset.mem_filter.1 hd).2

/-- The join with `σ'` in place of `σ`, when `σ` is an instance of `σ'` on `V` and the
fresh variables of `σ'` — those in its images outside `V` — are mentioned by no other
member: it exists if the join with `σ` does, and the join with `σ` is an instance of
it on every variable in `V` or fresh to `σ'`'s images. Both members restricted to `V`
(their domains within it) and idempotent. -/
theorem joinAll_inst (U : Unification) {V : Finset Var} {σ σ' : Subst} {L₁ L₂ : List Subst}
    (hσ : σ.Idem) (hσ' : σ'.Idem) (hσ't : σ'.Typed) (hd : σ.dom ⊆ V) (hd' : σ'.dom ⊆ V)
    (hidem : ∀ η ∈ L₁ ++ L₂, η.Idem)
    (hapart : ∀ w ∈ σ'.imageVars, w ∉ V → ∀ η ∈ L₁ ++ L₂, ¬ η.Mentions w)
    (hinst : InstOn V σ σ') {J : Subst} (hJ : U.joinAll (L₁ ++ σ :: L₂) = some J) :
    ∃ J', U.joinAll (L₁ ++ σ' :: L₂) = some J' ∧
      ∀ W : Finset Var, (∀ w ∈ W, w ∉ V → w ∉ σ'.imageVars) → InstOn W J J' := by
  obtain ⟨δ, hδ, hi⟩ := hinst
  have hidemσ : ∀ η ∈ L₁ ++ σ :: L₂, η.Idem := by
    intro η hη
    simp only [List.mem_append, List.mem_cons] at hη hidem
    rcases hη with hη | rfl | hη
    · exact hidem η (Or.inl hη)
    · exact hσ
    · exact hidem η (Or.inr hη)
  have hidemσ' : ∀ η ∈ L₁ ++ σ' :: L₂, η.Idem := by
    intro η hη
    simp only [List.mem_append, List.mem_cons] at hη hidem
    rcases hη with hη | rfl | hη
    · exact hidem η (Or.inl hη)
    · exact hσ'
    · exact hidem η (Or.inr hη)
  obtain ⟨hJt, _, hJa⟩ := (joinAll_spec U hidemσ).1 J hJ
  rw [absorbsAll_middle] at hJa
  obtain ⟨hJσ, hJothers⟩ := hJa
  -- `δ₀`: `δ` on the variables of the images of `σ'`, the identity elsewhere
  set δ₀ := δ.restrict σ'.imageVars with hδ₀
  have hδ₀t : δ₀.Typed := Subst.Typed.restrict hδ _
  -- `J ∘ δ₀` agrees with `J` on every variable in `V` and on every variable not in an
  -- image of `σ'`
  have hagree : ∀ w, (w ∈ V ∨ w ∉ σ'.imageVars) → J.apply (δ₀.f w) = J.f w := by
    intro w hw
    by_cases him : w ∈ σ'.imageVars
    · have hwV : w ∈ V := hw.resolve_right (fun h => h him)
      rw [hδ₀, Subst.restrict_f_of_mem him]
      -- `w` is in an image of the idempotent `σ'`, so `σ'` does not move it
      have hwd : w ∉ σ'.dom := by
        obtain ⟨u, hu, hwu⟩ := Subst.mem_imageVars.1 him
        exact hσ'.not_mem_dom hwu
      have h1 := hi w hwV
      rw [Subst.f_eq_of_not_mem hwd, Subst.apply_var] at h1
      -- `σ.f w = δ.f w`, and `J` absorbs `σ`
      rw [← h1]
      by_cases hwσ : w ∈ σ.dom
      · exact (Subst.comp_eq_iff.1 hJσ) w hwσ
      · rw [Subst.f_eq_of_not_mem hwσ, Subst.apply_var]
    · rw [hδ₀, Subst.restrict_f_of_not_mem δ him, Subst.apply_var]
  have hagree_apply : ∀ e : Exp, (∀ w ∈ e.vars, w ∈ V ∨ w ∉ σ'.imageVars) →
      (J.comp δ₀).apply e = J.apply e := by
    intro e he
    apply apply_congr_vars
    intro w hw
    show J.apply (δ₀.f w) = J.f w
    exact hagree w (he w hw)
  -- `J ∘ δ₀` absorbs every member of the join with `σ'`
  have habs : AbsorbsAll (J.comp δ₀) (L₁ ++ σ' :: L₂) := by
    rw [absorbsAll_middle]
    constructor
    · rw [Subst.comp_eq_iff]
      intro v hv
      have hvV : v ∈ V := hd' hv
      -- `δ₀` fixes `v`, which no image of `σ'` has
      have hvim : v ∉ σ'.imageVars := by
        intro h
        obtain ⟨u, hu, hvu⟩ := Subst.mem_imageVars.1 h
        exact hσ'.not_mem_dom hvu hv
      have hδ₀v : (J.comp δ₀).f v = J.f v := by
        show J.apply (δ₀.f v) = J.f v
        exact hagree v (Or.inr hvim)
      -- `δ₀ (σ'.f v) = δ (σ'.f v) = σ.f v`
      have h2 : δ₀.apply (σ'.f v) = δ.apply (σ'.f v) := by
        apply apply_congr_vars
        intro w hw
        rw [hδ₀, Subst.restrict_f_of_mem (Subst.mem_imageVars.2 ⟨v, hv, hw⟩)]
      rw [hδ₀v, Subst.apply_comp, h2, ← hi v hvV]
      by_cases hvσ : v ∈ σ.dom
      · exact (Subst.comp_eq_iff.1 hJσ) v hvσ
      · rw [Subst.f_eq_of_not_mem hvσ, Subst.apply_var]
    · intro η hη
      rw [Subst.comp_eq_iff]
      intro y hy
      have hmy : η.Mentions y := Or.inl hy
      have hyok : y ∈ V ∨ y ∉ σ'.imageVars := by
        by_contra h
        rw [not_or, not_not] at h
        exact hapart y h.2 h.1 η hη hmy
      have hyf : (J.comp δ₀).f y = J.f y := by
        show J.apply (δ₀.f y) = J.f y
        exact hagree y hyok
      rw [hyf, hagree_apply (η.f y) (fun w hw => by
        by_contra h
        rw [not_or, not_not] at h
        exact hapart w h.2 h.1 η hη (Or.inr ⟨y, hy, hw⟩))]
      exact (Subst.comp_eq_iff.1 (hJothers η hη)) y hy
  obtain ⟨J', hJ', hJ'abs⟩ := (joinAll_spec U hidemσ').2 (J.comp δ₀) (Subst.Typed.comp hJt hδ₀t) habs
  refine ⟨J', hJ', fun W hW => ⟨J.comp δ₀, Subst.Typed.comp hJt hδ₀t, fun w hw => ?_⟩⟩
  -- `J.f w = (J ∘ δ₀).f w = (J ∘ δ₀).apply (J'.f w)`
  have h1 : (J.comp δ₀).f w = J.f w := by
    show J.apply (δ₀.f w) = J.f w
    exact hagree w (by
      by_cases hwV : w ∈ V
      · exact Or.inl hwV
      · exact Or.inr (hW w hw hwV))
  rw [← h1]
  exact ((Subst.comp_eq_iff.1 hJ'abs) w |> fun h => by
    by_cases hwd : w ∈ J'.dom
    · exact (h hwd).symm
    · rw [Subst.f_eq_of_not_mem hwd, Subst.apply_var])

/-- The two joins exist together and are the same up to instance each way on every
variable in `V` or fresh to neither member. -/
theorem joinAll_sameOn (U : Unification) {V : Finset Var} {σ σ' : Subst} {L₁ L₂ : List Subst}
    (hσ : σ.Idem) (hσt : σ.Typed) (hσ' : σ'.Idem) (hσ't : σ'.Typed) (hd : σ.dom ⊆ V) (hd' : σ'.dom ⊆ V)
    (hidem : ∀ η ∈ L₁ ++ L₂, η.Idem)
    (hapart : ∀ w ∈ σ.imageVars, w ∉ V → ∀ η ∈ L₁ ++ L₂, ¬ η.Mentions w)
    (hapart' : ∀ w ∈ σ'.imageVars, w ∉ V → ∀ η ∈ L₁ ++ L₂, ¬ η.Mentions w)
    (hsame : SameOn V σ σ') :
    ((∃ J, U.joinAll (L₁ ++ σ :: L₂) = some J) ↔ ∃ J', U.joinAll (L₁ ++ σ' :: L₂) = some J') ∧
    ∀ J J', U.joinAll (L₁ ++ σ :: L₂) = some J → U.joinAll (L₁ ++ σ' :: L₂) = some J' →
      ∀ W : Finset Var, (∀ w ∈ W, w ∉ V → w ∉ σ.imageVars ∧ w ∉ σ'.imageVars) → SameOn W J J' := by
  constructor
  · constructor
    · rintro ⟨J, hJ⟩
      obtain ⟨J', hJ', _⟩ := joinAll_inst U hσ hσ' hσ't hd hd' hidem hapart' hsame.1 hJ
      exact ⟨J', hJ'⟩
    · rintro ⟨J', hJ'⟩
      obtain ⟨J, hJ, _⟩ := joinAll_inst U hσ' hσ hσt hd' hd hidem hapart hsame.2 hJ'
      exact ⟨J, hJ⟩
  · intro J J' hJ hJ' W hW
    obtain ⟨J₁, hJ₁, h₁⟩ := joinAll_inst U hσ hσ' hσ't hd hd' hidem hapart' hsame.1 hJ
    rw [hJ'] at hJ₁
    obtain rfl := Option.some.inj hJ₁
    obtain ⟨J₂, hJ₂, h₂⟩ := joinAll_inst U hσ' hσ hσt hd' hd hidem hapart hsame.2 hJ'
    rw [hJ] at hJ₂
    obtain rfl := Option.some.inj hJ₂
    exact ⟨h₁ W (fun w hw hwV => (hW w hw hwV).2), h₂ W (fun w hw hwV => (hW w hw hwV).1)⟩

end Theory
