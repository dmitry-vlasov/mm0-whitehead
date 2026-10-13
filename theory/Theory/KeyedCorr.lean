/-
The keyed engine against the reference engine (`docs/THEORY.md`, "The production
engine", milestones 13 and 14): the invariant of a keyed entry, and the correspondence
of the two engines' entries, node by node.
-/
import Theory.Keyed
import Theory.KeyedLemmas
import Theory.Completeness

namespace Theory

open State

/-! ### The invariant of a keyed entry -/

/-- A keyed entry at expression node `i`: its tree sits at `i`; its substitution is
typed and idempotent, moves only visible variables, and mentions, beyond the visible
variables, only variables in the blocks of the assertion nodes of its tree. -/
structure KInv (s : State) (st : Statement) (i : ℕ) (K : KEntry) : Prop where
  at_ : K.tree.At s i
  typed : K.sub.Typed
  idem : K.sub.Idem
  dom : K.sub.dom ⊆ visible st s i
  mentions : ∀ v, K.sub.Mentions v → v ∈ visible st s i ∨ ∃ j ∈ K.tree.anodes, s.InBlock j v

theorem Subst.mentions_restrict {θ : Subst} {V : Finset Var} {v : Var} (h : (θ.restrict V).Mentions v) :
    θ.Mentions v := by
  rcases h with h | ⟨u, hu, hv⟩
  · exact Or.inl (Finset.mem_filter.1 h).1
  · have hu' := Finset.mem_filter.1 hu
    rw [Subst.restrict_f_of_mem hu'.2] at hv
    exact Or.inr ⟨u, hu'.1, hv⟩

theorem mem_tuplesK : ∀ (ls : List (List KEntry)) (tup : List KEntry), tup ∈ tuplesK ls →
    tup.length = ls.length ∧ ∀ k, k < ls.length → tup[k]! ∈ ls[k]!
  | [], tup, h => by
    simp only [tuplesK, List.mem_singleton] at h
    subst h
    exact ⟨rfl, fun k hk => by simp at hk⟩
  | l :: ls, tup, h => by
    simp only [tuplesK, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, tup', htup', rfl⟩ := h
    obtain ⟨hlen, hk⟩ := mem_tuplesK ls tup' htup'
    refine ⟨by simp [hlen], fun k hk' => ?_⟩
    cases k with
    | zero => simpa using hx
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk'
      simpa using hk k hk'

theorem mem_of_mem_dedupKeys {K : KEntry} : ∀ {es : List KEntry}, K ∈ dedupKeys es → K ∈ es := by
  intro es
  unfold dedupKeys
  suffices h : ∀ (acc : List KEntry), K ∈ es.foldl (fun acc K => if acc.any (·.sameKey K) then acc else acc ++ [K]) acc →
      K ∈ acc ∨ K ∈ es by
    intro hK
    exact (h [] hK).resolve_left (by simp)
  induction es with
  | nil => intro acc h; exact Or.inl h
  | cons e es ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h | h
    · split at h
      · exact Or.inl h
      · simp only [List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact Or.inl h
        · exact Or.inr (by simp)
    · exact Or.inr (by simp [h])

theorem SptTree.mem_anodesList' {j : ℕ} : ∀ cs : List SptTree, j ∈ SptTree.anodesList cs ↔ ∃ t ∈ cs, j ∈ t.anodes
  | [] => by simp [SptTree.anodesList]
  | t :: ts => by
    simp only [SptTree.anodesList, List.mem_append, SptTree.mem_anodesList' ts, List.mem_cons]
    aesop

/-- The visible variables of a child are among the parent's and the node's block. -/
theorem visible_child {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) {k : ℕ} (hk : k < s.anodes[j]!.children.length) {v : Var}
    (hv : v ∈ visible st s s.anodes[j]!.children[k]!) :
    v ∈ visible st s s.anodes[j]!.parent ∨ s.InBlock j v := by
  rcases Finset.mem_union.1 hv with h | h
  · rcases child_expr_vars hs hwf hj hk h with h | h
    · exact Or.inl (Finset.mem_union_left _ h)
    · exact Or.inr h
  · exact Or.inl (Finset.mem_union_right _ h)

/-- The keyed engine keeps the invariant. -/
theorem keyedE_inv {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) : ∀ (fuel i : ℕ), i < s.enodes.size → ∀ K ∈ keyedE U st s fuel i, KInv s st i K
  | 0, _, _, _, hK => by simp [keyedE] at hK
  | fuel + 1, i, hi, K, hK => by
    simp only [keyedE, List.mem_append, List.mem_flatMap] at hK
    rcases hK with hK | ⟨j, hj, hK⟩
    · simp only [leafK, List.mem_map, leafEntries, List.mem_filterMap, List.mem_range,
        Option.map_eq_some_iff] at hK
      obtain ⟨E, ⟨h, hh, θ, hθ, rfl⟩, rfl⟩ := hK
      refine { at_ := SptTree.At.leaf i h hi, typed := Subst.Typed.restrict (U.typed _ _ hθ) _,
               idem := (U.idem _ _ hθ).restrict _, dom := Subst.restrict_dom_subset _ _, mentions := ?_ }
      intro v hv
      have hm := mgu_mentions U hθ (Subst.mentions_restrict hv)
      rw [Problem.vars_single, Finset.mem_union] at hm
      rcases hm with hm | hm
      · exact Or.inl (Finset.mem_union_left _ hm)
      · exact Or.inl (Finset.mem_union_right _ (Statement.mem_vars_of_hyp hh hm))
    · obtain ⟨hj, hp⟩ := (mem_aChildren s i j).1 hj
      obtain ⟨A, hA⟩ := hs.anodes j hj
      have hK' := mem_of_mem_dedupKeys hK
      simp only [List.mem_filterMap] at hK'
      obtain ⟨tup, htup, hmk⟩ := hK'
      obtain ⟨hlen, hk⟩ := mem_tuplesK _ tup htup
      simp only [List.length_map] at hlen hk
      have hmem : ∀ k, k < tup.length → KInv s st (s.anodes[j]!.children[k]!) tup[k]! := by
        intro k hk'
        have := hk k (hlen ▸ hk')
        rw [getElem!_map _ _ k (hlen ▸ hk')] at this
        exact keyedE_inv (U := U) hs hwf fuel _ (hA.children k (hlen ▸ hk')).1 _ this
      split at hmk
      · exact absurd hmk (by simp)
      · rename_i J hJ
        simp only [Option.map_eq_some_iff] at hmk
        obtain ⟨pending, _, rfl⟩ := hmk
        refine { at_ := ?_, typed := Subst.Typed.restrict (joinAll_typed U _ J hJ) _,
                 idem := (joinAll_idem U _ J hJ).restrict _, dom := Subst.restrict_dom_subset _ _, mentions := ?_ }
        · refine SptTree.At.node i j _ hj hp (by simp [hlen]) ?_
          intro k hk'
          simp only [List.length_map] at hk'
          rw [getElem!_map _ _ k hk']
          exact (hmem k hk').at_
        · intro v hv
          obtain ⟨σ, hσ, hm⟩ := joinAll_mentions U _ J hJ v (Subst.mentions_restrict hv)
          simp only [List.mem_cons, List.mem_map] at hσ
          rcases hσ with rfl | ⟨K', hK', rfl⟩
          · rcases anode_mentions hs hwf hj hm with h | h
            · rw [hp] at h
              exact Or.inl (Finset.mem_union_left _ h)
            · exact Or.inr ⟨j, by simp [SptTree.anodes], h⟩
          · obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 hK'
            have hinv := hmem k hk'
            rw [getElem!_pos tup k hk'] at hinv
            rcases hinv.mentions v hm with h | ⟨j', hj', hb⟩
            · rcases visible_child hs hwf hj (hlen ▸ hk') h with h | h
              · rw [hp] at h
                exact Or.inl h
              · exact Or.inr ⟨j, by simp [SptTree.anodes], h⟩
            · refine Or.inr ⟨j', ?_, hb⟩
              simp only [SptTree.anodes, List.mem_cons]
              refine Or.inr ((SptTree.mem_anodesList' _).2 ⟨tup[k].tree, ?_, hj'⟩)
              rw [List.mem_map]
              exact ⟨tup[k], List.getElem_mem hk', rfl⟩


/-! ### Members of a join at an assertion node -/

/-- A member of the join at an assertion node, standing for child `k` of node `j`:
idempotent, typed, and mentioning beyond the visible variables of the child only
variables in blocks of assertion nodes of a tree at the child. The full and the
restricted substitutions of reference entries, and the substitutions of keyed entries,
are such members. -/
structure Member (s : State) (st : Statement) (j k : ℕ) (σ : Subst) : Prop where
  idem : σ.Idem
  typed : σ.Typed
  mentions : ∀ v, σ.Mentions v → v ∈ visible st s s.anodes[j]!.children[k]! ∨
    ∃ T : SptTree, T.At s s.anodes[j]!.children[k]! ∧ ∃ j' ∈ T.anodes, s.InBlock j' v

theorem Member.of_kinv {s : State} {st : Statement} {j k : ℕ} {K : KEntry}
    (h : KInv s st s.anodes[j]!.children[k]! K) : Member s st j k K.sub where
  idem := h.idem
  typed := h.typed
  mentions := fun v hv => (h.mentions v hv).elim Or.inl fun ⟨j', hj', hb⟩ => Or.inr ⟨K.tree, h.at_, j', hj', hb⟩

theorem Member.restrict {s : State} {st : Statement} {j k : ℕ} {σ : Subst} (h : Member s st j k σ) (V : Finset Var) :
    Member s st j k (σ.restrict V) where
  idem := h.idem.restrict V
  typed := h.typed.restrict V
  mentions := fun v hv => h.mentions v (Subst.mentions_restrict hv)

theorem Member.of_entry {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {fuel j k : ℕ} (hj : j < s.anodes.size) (hk : k < s.anodes[j]!.children.length) {E : Entry}
    (hE : E ∈ sptE U st s fuel s.anodes[j]!.children[k]!) : Member s st j k E.sub := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  have hc := (hA.children k hk).1
  have hinv := sptE_inv hs fuel _ hc E hE
  refine { idem := hinv.idem, typed := hinv.typed, mentions := fun v hv => ?_ }
  rcases entry_mentions hs hwf fuel _ hc E hE v hv with h | h | ⟨j', hj', hb⟩
  · exact Or.inl (Finset.mem_union_right _ h)
  · exact Or.inl (Finset.mem_union_left _ h)
  · exact Or.inr ⟨E.tree, hinv.at_, j', hj', hb⟩

/-- A variable in a block of a tree at a child is mentioned by no member at another
child, nor by the node's unifier, nor is it visible at the parent. -/
theorem block_apart {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) {k : ℕ} (hk : k < s.anodes[j]!.children.length) {T : SptTree}
    (hT : T.At s s.anodes[j]!.children[k]!) {j' : ℕ} (hj' : j' ∈ T.anodes) {v : Var} (hb : s.InBlock j' v) :
    v ∉ visible st s s.anodes[j]!.parent ∧ ¬ s.anodes[j]!.sub.Mentions v ∧
    ∀ k', k' < s.anodes[j]!.children.length → k' ≠ k → ∀ η, Member s st j k' η → ¬ η.Mentions v := by
  obtain ⟨h1, h2, h3⟩ := below_apart hs hj hk hT hj' hb
  refine ⟨?_, ?_, ?_⟩
  · intro hv
    rcases Finset.mem_union.1 hv with hv | hv
    · exact h1 hv
    · exact h3 hv
  · intro hm
    rcases anode_mentions hs hwf hj hm with hm | hm
    · exact h1 hm
    · exact h2 hm
  · intro k' hk' hne η hη hm
    rcases hη.mentions v hm with hv | ⟨T', hT', j'', hj'', hb'⟩
    · rcases visible_child hs hwf hj hk' hv with hv | hv
      · exact absurd hv (by
          intro h
          rcases Finset.mem_union.1 h with h | h
          · exact h1 h
          · exact h3 h)
      · exact h2 hv
    · have heq := State.inBlock_eq hb hb'
      subst heq
      have hp := parent_mem_enodes hT j' hj'
      have hp' := parent_mem_enodes hT' j' hj''
      exact hne (sibling_trees_disjoint hs hj hk' hk hT' hT _ hp' hp)

/-- The lemma of `joinAll_sameOn` at an assertion node: two members for child `k`,
restricted to its visible variables and the same on them up to instance each way, with
the other members the node's unifier and members for the other children. -/
theorem sameOn_step {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) {k : ℕ} (hk : k < s.anodes[j]!.children.length)
    {σ σ' : Subst} (hσ : Member s st j k σ) (hσ' : Member s st j k σ')
    (hd : σ.dom ⊆ visible st s s.anodes[j]!.children[k]!) (hd' : σ'.dom ⊆ visible st s s.anodes[j]!.children[k]!)
    (hsame : SameOn (visible st s s.anodes[j]!.children[k]!) σ σ') {L₁ L₂ : List Subst}
    (hmem : ∀ η ∈ L₁ ++ L₂, η = s.anodes[j]!.sub ∨ ∃ k', k' < s.anodes[j]!.children.length ∧ k' ≠ k ∧ Member s st j k' η) :
    ((∃ J, U.joinAll (L₁ ++ σ :: L₂) = some J) ↔ ∃ J', U.joinAll (L₁ ++ σ' :: L₂) = some J') ∧
    ∀ J J', U.joinAll (L₁ ++ σ :: L₂) = some J → U.joinAll (L₁ ++ σ' :: L₂) = some J' →
      SameOn (visible st s s.anodes[j]!.parent) J J' := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  have hidem : ∀ η ∈ L₁ ++ L₂, η.Idem := by
    intro η hη
    rcases hmem η hη with rfl | ⟨_, _, _, h⟩
    · exact hA.idem
    · exact h.idem
  -- a variable in an image of a member outside the child's visible variables is in a
  -- block of a tree at the child, hence apart
  have hapart : ∀ τ, Member s st j k τ → ∀ w ∈ τ.imageVars, w ∉ visible st s s.anodes[j]!.children[k]! →
      ∀ η ∈ L₁ ++ L₂, ¬ η.Mentions w := by
    intro τ hτ w hw hwV η hη
    obtain ⟨u, hu, hwu⟩ := Subst.mem_imageVars.1 hw
    rcases hτ.mentions w (Or.inr ⟨u, hu, hwu⟩) with h | ⟨T, hT, j', hj', hb⟩
    · exact absurd h hwV
    · obtain ⟨_, h2, h3⟩ := block_apart hs hwf hj hk hT hj' hb
      rcases hmem η hη with rfl | ⟨k', hk', hne, hη'⟩
      · exact h2
      · exact h3 k' hk' hne η hη'
  have hW : ∀ W : Finset Var, (∀ w ∈ W, w ∈ visible st s s.anodes[j]!.parent) →
      ∀ w ∈ W, w ∉ visible st s s.anodes[j]!.children[k]! → w ∉ σ.imageVars ∧ w ∉ σ'.imageVars := by
    intro W hWp w hw hwV
    have hvis := hWp w hw
    constructor
    · intro him
      obtain ⟨u, hu, hwu⟩ := Subst.mem_imageVars.1 him
      rcases hσ.mentions w (Or.inr ⟨u, hu, hwu⟩) with h | ⟨T, hT, j', hj', hb⟩
      · exact hwV h
      · exact (block_apart hs hwf hj hk hT hj' hb).1 hvis
    · intro him
      obtain ⟨u, hu, hwu⟩ := Subst.mem_imageVars.1 him
      rcases hσ'.mentions w (Or.inr ⟨u, hu, hwu⟩) with h | ⟨T, hT, j', hj', hb⟩
      · exact hwV h
      · exact (block_apart hs hwf hj hk hT hj' hb).1 hvis
  obtain ⟨h1, h2⟩ := joinAll_sameOn U hσ.idem hσ.typed hσ'.idem hσ'.typed hd hd' hidem
    (hapart σ hσ) (hapart σ' hσ') hsame
  exact ⟨h1, fun J J' hJ hJ' => h2 J J' hJ hJ' _ (hW _ fun w hw => hw)⟩

/-- The chain: a tuple of restricted members replaced by an equivalent tuple, one
position at a time, from position `m` on, the members before `m` already replaced in
`L₁`. The joins exist together and are the same on the parent's visible variables. -/
theorem sameOn_chain {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) :
    ∀ (σs τs : List Subst) (m : ℕ) (L₁ : List Subst),
      σs.length = τs.length → m + σs.length = s.anodes[j]!.children.length →
      (∀ η ∈ L₁, η = s.anodes[j]!.sub ∨ ∃ k', k' < m ∧ Member s st j k' η) →
      (∀ l, (hl : l < σs.length) → Member s st j (m + l) σs[l] ∧ σs[l].dom ⊆ visible st s s.anodes[j]!.children[m + l]!) →
      (∀ l, (hl : l < τs.length) → Member s st j (m + l) τs[l] ∧ τs[l].dom ⊆ visible st s s.anodes[j]!.children[m + l]!) →
      (∀ l, (hl : l < σs.length) → (hl' : l < τs.length) → SameOn (visible st s s.anodes[j]!.children[m + l]!) σs[l] τs[l]) →
      ((∃ J, U.joinAll (L₁ ++ σs) = some J) ↔ ∃ J', U.joinAll (L₁ ++ τs) = some J') ∧
      ∀ J J', U.joinAll (L₁ ++ σs) = some J → U.joinAll (L₁ ++ τs) = some J' →
        SameOn (visible st s s.anodes[j]!.parent) J J'
  | [], [], m, L₁, _, _, _, _, _, _ =>
    ⟨Iff.rfl, fun J J' hJ hJ' => by rw [hJ] at hJ'; obtain rfl := Option.some.inj hJ'; exact SameOn.refl _ _⟩
  | σ :: σs, τ :: τs, m, L₁, hlen, hm, hL₁, hσs, hτs, hsame => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hm' : m < s.anodes[j]!.children.length := by simp only [List.length_cons] at hm; omega
    have hσ := hσs 0 (by simp)
    have hτ := hτs 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hσ hτ
    have hsame0 := hsame 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hsame0
    -- the first step: `σ` to `τ`, the others `σs` after and `L₁` before
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
    obtain ⟨hex, hJ⟩ := sameOn_step hs hwf hj hm' hσ.1 hτ.1 hσ.2 hτ.2 hsame0 hmem
    -- the rest: from position `m + 1`, with `τ` moved into `L₁`
    have hrest := sameOn_chain hs hwf hj σs τs (m + 1) (L₁ ++ [τ]) hlen (by simp only [List.length_cons] at hm; omega)
      (by
        intro η hη
        rcases List.mem_append.1 hη with hη | hη
        · rcases hL₁ η hη with h | ⟨k', hk', h⟩
          · exact Or.inl h
          · exact Or.inr ⟨k', by omega, h⟩
        · simp only [List.mem_singleton] at hη
          subst hη
          exact Or.inr ⟨m, by omega, hτ.1⟩)
      (fun l hl => by
        have := hσs (l + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show m + 1 + l = m + (l + 1) by omega]
        exact this)
      (fun l hl => by
        have := hτs (l + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show m + 1 + l = m + (l + 1) by omega]
        exact this)
      (fun l hl hl' => by
        have := hsame (l + 1) (by simp; omega) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        rw [show m + 1 + l = m + (l + 1) by omega]
        exact this)
    have hassoc : ∀ (ρ : Subst) (ρs : List Subst), (L₁ ++ [ρ]) ++ ρs = L₁ ++ ρ :: ρs := by
      intro ρ ρs; simp
    rw [hassoc τ σs, hassoc τ τs] at hrest
    refine ⟨hex.trans hrest.1, fun J J' hJσ hJ'τ => ?_⟩
    obtain ⟨Jm, hJm⟩ := hex.1 ⟨J, hJσ⟩
    exact (hJ J Jm hJσ hJm).trans (hrest.2 Jm J' hJm hJ'τ)


/-! ### Restriction of a member -/

theorem sameOn_restrict (V : Finset Var) (θ : Subst) : SameOn V (θ.restrict V) θ :=
  ⟨⟨Subst.id, Subst.Typed.id, fun v hv => by rw [Subst.restrict_f_of_mem hv, Subst.apply_id]⟩,
   ⟨Subst.id, Subst.Typed.id, fun v hv => by rw [Subst.restrict_f_of_mem hv, Subst.apply_id]⟩⟩

/-- A member for child `k` replaced by its restriction to the child's visible variables:
the joins exist together and are the same on the parent's visible variables. -/
theorem restrict_step {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) {k : ℕ} (hk : k < s.anodes[j]!.children.length)
    {θ : Subst} (hθ : Member s st j k θ) {L₁ L₂ : List Subst}
    (hmem : ∀ η ∈ L₁ ++ L₂, η = s.anodes[j]!.sub ∨ ∃ k', k' < s.anodes[j]!.children.length ∧ k' ≠ k ∧ Member s st j k' η) :
    ((∃ J, U.joinAll (L₁ ++ θ :: L₂) = some J) ↔
      ∃ J', U.joinAll (L₁ ++ θ.restrict (visible st s s.anodes[j]!.children[k]!) :: L₂) = some J') ∧
    ∀ J J', U.joinAll (L₁ ++ θ :: L₂) = some J →
      U.joinAll (L₁ ++ θ.restrict (visible st s s.anodes[j]!.children[k]!) :: L₂) = some J' →
      SameOn (visible st s s.anodes[j]!.parent) J J' := by
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
  refine ⟨joinAll_restrict_exists U _ hθ.idem hθ.typed hidem hL, fun J J' hJ hJ' => ?_⟩
  obtain ⟨⟨δ, hδ, h1⟩, ⟨δ', hδ', h2⟩⟩ := joinAll_restrict_instance U _ hθ.idem hθ.typed hidem hL hJ hJ'
  refine ⟨⟨δ, hδ, fun v _ => h1 v⟩, ⟨δ', hδ', fun v hv => h2 v fun hd => ?_⟩⟩
  by_contra hvV
  rcases hθ.mentions v (Or.inl hd) with h | ⟨T, hT, j', hj', hb⟩
  · exact hvV h
  · exact (block_apart hs hwf hj hk hT hj' hb).1 hv

/-- The chain of restrictions: the full members from position `m` on replaced by their
restrictions, the members before `m` in `L₁`. -/
theorem restrict_chain {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) {j : ℕ} (hj : j < s.anodes.size) :
    ∀ (σs τs : List Subst) (m : ℕ) (L₁ : List Subst),
      σs.length = τs.length → m + σs.length = s.anodes[j]!.children.length →
      (∀ η ∈ L₁, η = s.anodes[j]!.sub ∨ ∃ k', k' < m ∧ Member s st j k' η) →
      (∀ l, (hl : l < σs.length) → Member s st j (m + l) σs[l]) →
      (∀ l, (hl : l < σs.length) → (hl' : l < τs.length) →
        τs[l] = σs[l].restrict (visible st s s.anodes[j]!.children[m + l]!)) →
      ((∃ J, U.joinAll (L₁ ++ σs) = some J) ↔ ∃ J', U.joinAll (L₁ ++ τs) = some J') ∧
      ∀ J J', U.joinAll (L₁ ++ σs) = some J → U.joinAll (L₁ ++ τs) = some J' →
        SameOn (visible st s s.anodes[j]!.parent) J J'
  | [], [], m, L₁, _, _, _, _, _ =>
    ⟨Iff.rfl, fun J J' hJ hJ' => by rw [hJ] at hJ'; obtain rfl := Option.some.inj hJ'; exact SameOn.refl _ _⟩
  | σ :: σs, τ :: τs, m, L₁, hlen, hm, hL₁, hσs, hτs => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hm' : m < s.anodes[j]!.children.length := by simp only [List.length_cons] at hm; omega
    have hσ := hσs 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hσ
    have hτ0 := hτs 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hτ0
    subst hτ0
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
        exact Or.inr ⟨m + (l + 1), by simp only [List.length_cons] at hm; omega, by omega, this⟩
    obtain ⟨hex, hJ⟩ := restrict_step hs hwf hj hm' hσ hmem
    have hrest := restrict_chain hs hwf hj σs τs (m + 1) (L₁ ++ [σ.restrict (visible st s s.anodes[j]!.children[m]!)])
      hlen (by simp only [List.length_cons] at hm; omega)
      (by
        intro η hη
        rcases List.mem_append.1 hη with hη | hη
        · rcases hL₁ η hη with h | ⟨k', hk', h⟩
          · exact Or.inl h
          · exact Or.inr ⟨k', by omega, h⟩
        · simp only [List.mem_singleton] at hη
          subst hη
          exact Or.inr ⟨m, by omega, hσ.restrict _⟩)
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
    have hassoc : ∀ (ρ : Subst) (ρs : List Subst), (L₁ ++ [ρ]) ++ ρs = L₁ ++ ρ :: ρs := by
      intro ρ ρs; simp
    rw [hassoc _ σs, hassoc _ τs] at hrest
    refine ⟨hex.trans hrest.1, fun J J' hJσ hJ'τ => ?_⟩
    obtain ⟨Jm, hJm⟩ := hex.1 ⟨J, hJσ⟩
    exact (hJ J Jm hJσ hJm).trans (hrest.2 Jm J' hJm hJ'τ)

/-! ### Without conditions -/

/-- A database without pairs: no conditions on bound variables anywhere. -/
def Database.NoPairs (db : Database) : Prop := ∀ A ∈ db.asserts, A.pairs = []

theorem anode_conds_nil {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hnp : db.NoPairs) {j : ℕ} (hj : j < s.anodes.size) : s.anodes[j]!.conds = [] := by
  obtain ⟨A, hA⟩ := hs.anodes j hj
  rw [hA.conds, nodeConds, hnp A (List.mem_of_getElem? hA.assertion)]
  rfl

theorem SptTree.conds_nil_of_nopairs {U : Unification} {db : Database} {st : Statement} {s : State}
    (hs : StateInv U db st s) (hnp : db.NoPairs) : ∀ {i : ℕ} {T : SptTree}, T.At s i → T.conds s = [] := by
  intro i T hat
  induction hat with
  | leaf => rfl
  | node i j cs hj hp hlen hcs ih =>
    simp only [SptTree.conds, anode_conds_nil hs hnp hj, List.nil_append, SptTree.condsList_eq_flatMap]
    apply List.flatMap_eq_nil_iff.2
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
    have := ih k hk
    rwa [getElem!_pos cs k hk] at this

theorem entry_conds_nil {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hnp : db.NoPairs) {fuel i : ℕ} (hi : i < s.enodes.size) {E : Entry} (hE : E ∈ sptE U st s fuel i) : E.conds = [] := by
  have hinv := sptE_inv hs fuel i hi E hE
  rw [hinv.conds, SptTree.conds_nil_of_nopairs hs hnp hinv.at_]
  rfl

theorem judgeAll_nil (c : Consts) (st : Statement) (e : Exp) (J : Subst) : judgeAll c st e J [] = some [] := rfl

theorem mem_tuplesK_of_index : ∀ (ls : List (List KEntry)) (tup : List KEntry), tup.length = ls.length →
    (∀ k, k < ls.length → tup[k]! ∈ ls[k]!) → tup ∈ tuplesK ls
  | [], [], _, _ => by simp [tuplesK]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | l :: ls, x :: tup, hlen, hk => by
    simp only [tuplesK, List.mem_flatMap, List.mem_map]
    refine ⟨x, by simpa using hk 0 (by simp), tup, ?_, rfl⟩
    refine mem_tuplesK_of_index ls tup (by simpa using hlen) fun k hk' => ?_
    have := hk (k + 1) (by simp; omega)
    simpa using this

theorem KEntry.sameKey_self (K : KEntry) : K.sameKey K = true := by
  simp [KEntry.sameKey, Subst.beq_iff]

theorem mem_foldl_dedup {K : KEntry} : ∀ (es acc : List KEntry), K ∈ acc →
    K ∈ es.foldl (fun acc K => if acc.any (·.sameKey K) then acc else acc ++ [K]) acc
  | [], acc, h => h
  | e :: es, acc, h => by
    simp only [List.foldl_cons]
    apply mem_foldl_dedup es
    split
    · exact h
    · exact List.mem_append_left _ h

theorem dedupKeys_spec {K₀ : KEntry} : ∀ (es : List KEntry), K₀ ∈ es → ∃ K ∈ dedupKeys es, K.sameKey K₀ = true := by
  intro es
  unfold dedupKeys
  suffices h : ∀ acc : List KEntry, (∃ K ∈ acc, K.sameKey K₀ = true) ∨ K₀ ∈ es →
      ∃ K ∈ es.foldl (fun acc K => if acc.any (·.sameKey K) then acc else acc ++ [K]) acc, K.sameKey K₀ = true by
    intro hK
    exact h [] (Or.inr hK)
  induction es with
  | nil =>
    intro acc h
    rcases h with ⟨K, hK, hs⟩ | h
    · exact ⟨K, hK, hs⟩
    · simp at h
  | cons e es ih =>
    intro acc h
    simp only [List.foldl_cons]
    rcases h with ⟨K, hK, hs⟩ | h
    · apply ih
      left
      refine ⟨K, ?_, hs⟩
      split
      · exact hK
      · exact List.mem_append_left _ hK
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · apply ih
        left
        split
        · rename_i hany
          simp only [List.any_eq_true] at hany
          obtain ⟨K, hK, hs⟩ := hany
          exact ⟨K, hK, hs⟩
        · exact ⟨K₀, by simp, KEntry.sameKey_self K₀⟩
      · exact ih _ (Or.inr h)

theorem KEntry.sub_eq_of_sameKey {K K' : KEntry} (h : K.sameKey K' = true) : K.sub = K'.sub := by
  simp only [KEntry.sameKey, Bool.and_eq_true] at h
  exact Subst.beq_iff.1 h.1

/-! ### The correspondence, without conditions -/

/-- Every keyed entry stands for a reference entry with the same tree, the same answer
on the visible variables up to instance each way, and no conditions. -/
theorem keyed_sound_np {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) (hnp : db.NoPairs) : ∀ (fuel i : ℕ), i < s.enodes.size → ∀ K ∈ keyedE U st s fuel i,
      ∃ E ∈ sptE U st s fuel i, K.tree = E.tree ∧ K.conds = [] ∧ SameOn (visible st s i) K.sub E.sub
  | 0, _, _, _, hK => by simp [keyedE] at hK
  | fuel + 1, i, hi, K, hK => by
    simp only [keyedE, List.mem_append, List.mem_flatMap] at hK
    rcases hK with hK | ⟨j, hj, hK⟩
    · simp only [leafK, List.mem_map] at hK
      obtain ⟨E, hE, rfl⟩ := hK
      exact ⟨E, by simp [sptE, hE], rfl, rfl, sameOn_restrict _ _⟩
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
          tup[k].tree = E.tree ∧ tup[k].conds = [] ∧ SameOn (visible st s s.anodes[j]!.children[k]!) tup[k].sub E.sub :=
        fun k hk' => keyed_sound_np hs hwf hnp fuel _ (hA.children k (hlen ▸ hk')).1 _ (hmemk k hk')
      -- the reference tuple
      let pick : Fin tup.length → Entry := fun k => Classical.choose (ih k k.2)
      have hpick : ∀ k : Fin tup.length, pick k ∈ sptE U st s fuel s.anodes[j]!.children[k]! ∧
          tup[k].tree = (pick k).tree ∧ tup[k].conds = [] ∧
          SameOn (visible st s s.anodes[j]!.children[k]!) tup[k].sub (pick k).sub :=
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
      -- the keyed join and the entry
      split at hmk
      · exact absurd hmk (by simp)
      · rename_i J' hJ'
        have hconds : s.anodes[j]!.conds ++ tup.flatMap (·.conds) = [] := by
          rw [anode_conds_nil hs hnp hj, List.nil_append, List.flatMap_eq_nil_iff]
          intro K' hK'
          obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 hK'
          exact (hpick ⟨k, hk'⟩).2.2.1
        rw [hconds, judgeAll_nil] at hmk
        simp only [Option.map_some, Option.some.injEq] at hmk
        subst hmk
        -- the two chains: keyed members to restricted reference members, then to full ones
        let σs : List Subst := tup.map (·.sub)
        let τs : List Subst := List.ofFn fun k : Fin tup.length =>
          (pick k).sub.restrict (visible st s s.anodes[j]!.children[k]!)
        let fulls : List Subst := etup.map (·.sub)
        have hσlen : σs.length = tup.length := by simp [σs]
        have hτlen : τs.length = tup.length := List.length_ofFn
        have hflen : fulls.length = tup.length := by simp [fulls, hetlen]
        have hσget : ∀ l (hl : l < tup.length), σs[l]'(by rw [hσlen]; exact hl) = tup[l].sub := fun l hl => List.getElem_map _
        have hτget : ∀ l (hl : l < tup.length), τs[l]'(by rw [hτlen]; exact hl) =
            (pick ⟨l, hl⟩).sub.restrict (visible st s s.anodes[j]!.children[l]!) := fun l hl => List.getElem_ofFn _
        have hfget : ∀ l (hl : l < tup.length), fulls[l]'(by rw [hflen]; exact hl) = (pick ⟨l, hl⟩).sub := by
          intro l hl
          simp only [fulls, List.getElem_map, hetget l hl]
        have hchain1 := sameOn_chain hs hwf hj σs τs 0 [s.anodes[j]!.sub] (by rw [hσlen, hτlen])
          (by rw [hσlen]; omega) (by intro η hη; simp only [List.mem_singleton] at hη; exact Or.inl hη)
          (fun l hl => by
            rw [hσlen] at hl
            rw [hσget l hl]
            have hinv := keyedE_inv hs hwf fuel _ (hA.children l (hlen ▸ hl)).1 _ (hmemk l hl)
            simp only [Nat.zero_add]
            exact ⟨Member.of_kinv hinv, hinv.dom⟩)
          (fun l hl => by
            rw [hτlen] at hl
            rw [hτget l hl]
            simp only [Nat.zero_add]
            exact ⟨(Member.of_entry hs hwf hj (hlen ▸ hl) (hpick ⟨l, hl⟩).1).restrict _, Subst.restrict_dom_subset _ _⟩)
          (fun l hl hl' => by
            rw [hσlen] at hl
            rw [hσget l hl, hτget l hl]
            simp only [Nat.zero_add]
            exact (hpick ⟨l, hl⟩).2.2.2.trans (sameOn_restrict _ _).symm)
        have hchain2 := restrict_chain hs hwf hj fulls τs 0 [s.anodes[j]!.sub] (by rw [hflen, hτlen])
          (by rw [hflen]; omega) (by intro η hη; simp only [List.mem_singleton] at hη; exact Or.inl hη)
          (fun l hl => by
            rw [hflen] at hl
            rw [hfget l hl]
            simp only [Nat.zero_add]
            exact Member.of_entry hs hwf hj (hlen ▸ hl) (hpick ⟨l, hl⟩).1)
          (fun l hl hl' => by
            rw [hflen] at hl
            rw [hfget l hl, hτget l hl]
            simp only [Nat.zero_add])
        have hJ'σ : U.joinAll ([s.anodes[j]!.sub] ++ σs) = some J' := by simpa [σs] using hJ'
        obtain ⟨Jτ, hJτ⟩ := hchain1.1.1 ⟨J', hJ'σ⟩
        obtain ⟨J, hJ⟩ := hchain2.1.2 ⟨Jτ, hJτ⟩
        have hsame1 := hchain1.2 J' Jτ hJ'σ hJτ
        have hsame2 := hchain2.2 J Jτ hJ hJτ
        refine ⟨{ tree := .node j (etup.map (·.tree)), sub := J,
                  conds := (s.anodes[j]!.conds ++ etup.flatMap (·.conds)).map (Cond.apply J) }, ?_, ?_, rfl, ?_⟩
        · simp only [sptE, List.mem_append, List.mem_flatMap]
          refine Or.inr ⟨j, (mem_aChildren s i j).2 ⟨hj, hp⟩, ?_⟩
          simp only [anodeEntries, List.mem_filterMap]
          refine ⟨etup, hetup, ?_⟩
          have hJfull : U.joinAll (s.anodes[j]!.sub :: etup.map (·.sub)) = some J := by simpa [fulls] using hJ
          rw [hJfull]
          have hcondsE : s.anodes[j]!.conds ++ etup.flatMap (·.conds) = [] := by
            rw [anode_conds_nil hs hnp hj, List.nil_append, List.flatMap_eq_nil_iff]
            intro E hE
            obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 hE
            rw [hetget k (hetlen ▸ hk')]
            exact entry_conds_nil hs hnp (hA.children k (by rw [← hlen, ← hetlen]; exact hk')).1 (hpick _).1
          simp [hcondsE]
        · show SptTree.node j (tup.map (·.tree)) = SptTree.node j (etup.map (·.tree))
          congr 1
          apply List.ext_getElem (by simp [hetlen])
          intro k hk1 hk2
          simp only [List.getElem_map]
          have hk' : k < tup.length := by simpa using hk1
          rw [hetget k hk']
          exact (hpick ⟨k, hk'⟩).2.1
        · simp only [hp] at hsame1 hsame2
          exact (sameOn_restrict _ _).trans (hsame1.trans hsame2.symm)


/-- Every reference entry has a keyed entry with the same answer on the visible
variables up to instance each way: the one kept for its key. -/
theorem keyed_complete_np {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    (hwf : db.WF) (hnp : db.NoPairs) : ∀ (fuel i : ℕ), i < s.enodes.size → ∀ E ∈ sptE U st s fuel i,
      ∃ K ∈ keyedE U st s fuel i, SameOn (visible st s i) K.sub E.sub
  | 0, _, _, _, hE => by simp [sptE] at hE
  | fuel + 1, i, hi, E, hE => by
    simp only [sptE, List.mem_append, List.mem_flatMap] at hE
    rcases hE with hE | ⟨j, hj, hE⟩
    · refine ⟨{ tree := E.tree, sub := E.sub.restrict (visible st s i), conds := [] }, ?_, sameOn_restrict _ _⟩
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
          SameOn (visible st s s.anodes[j]!.children[k]!) K.sub etup[k].sub :=
        fun k hk' => keyed_complete_np hs hwf hnp fuel _ (hA.children k (hlen ▸ hk')).1 _ (hmemk k hk')
      -- the keyed tuple
      let pick : Fin etup.length → KEntry := fun k => Classical.choose (ih k k.2)
      have hpick : ∀ k : Fin etup.length, pick k ∈ keyedE U st s fuel s.anodes[j]!.children[k]! ∧
          SameOn (visible st s s.anodes[j]!.children[k]!) (pick k).sub etup[k].sub :=
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
      -- the reference join is the entry's answer
      split at hmk
      · exact absurd hmk (by simp)
      · rename_i J hJ
        have hEsub : E.sub = J := by
          split at hmk
          · simp only [Option.some.injEq] at hmk
            rw [← hmk]
          · exact absurd hmk (by simp)
        -- the two chains: full reference members to restricted ones, then to the keyed members
        let fulls : List Subst := etup.map (·.sub)
        let τs : List Subst := List.ofFn fun k : Fin etup.length =>
          etup[k].sub.restrict (visible st s s.anodes[j]!.children[k]!)
        let σs : List Subst := ktup.map (·.sub)
        have hflen : fulls.length = etup.length := by simp [fulls]
        have hτlen : τs.length = etup.length := List.length_ofFn
        have hσlen : σs.length = etup.length := by simp [σs, hktlen]
        have hfget : ∀ l (hl : l < etup.length), fulls[l]'(by rw [hflen]; exact hl) = etup[l].sub :=
          fun l hl => List.getElem_map _
        have hτget : ∀ l (hl : l < etup.length), τs[l]'(by rw [hτlen]; exact hl) =
            etup[l].sub.restrict (visible st s s.anodes[j]!.children[l]!) := fun l hl => List.getElem_ofFn _
        have hσget : ∀ l (hl : l < etup.length), σs[l]'(by rw [hσlen]; exact hl) = (pick ⟨l, hl⟩).sub := by
          intro l hl
          simp only [σs, List.getElem_map, hktget l hl]
        have hchain2 := restrict_chain hs hwf hj fulls τs 0 [s.anodes[j]!.sub] (by rw [hflen, hτlen])
          (by rw [hflen]; omega) (by intro η hη; simp only [List.mem_singleton] at hη; exact Or.inl hη)
          (fun l hl => by
            rw [hflen] at hl
            rw [hfget l hl]
            simp only [Nat.zero_add]
            exact Member.of_entry hs hwf hj (hlen ▸ hl) (hmemk l hl))
          (fun l hl hl' => by
            rw [hflen] at hl
            rw [hfget l hl, hτget l hl]
            simp only [Nat.zero_add])
        have hchain1 := sameOn_chain hs hwf hj σs τs 0 [s.anodes[j]!.sub] (by rw [hσlen, hτlen])
          (by rw [hσlen]; omega) (by intro η hη; simp only [List.mem_singleton] at hη; exact Or.inl hη)
          (fun l hl => by
            rw [hσlen] at hl
            rw [hσget l hl]
            have hinv := keyedE_inv hs hwf fuel _ (hA.children l (hlen ▸ hl)).1 _ (hpick ⟨l, hl⟩).1
            simp only [Nat.zero_add]
            exact ⟨Member.of_kinv hinv, hinv.dom⟩)
          (fun l hl => by
            rw [hτlen] at hl
            rw [hτget l hl]
            simp only [Nat.zero_add]
            exact ⟨(Member.of_entry hs hwf hj (hlen ▸ hl) (hmemk l hl)).restrict _, Subst.restrict_dom_subset _ _⟩)
          (fun l hl hl' => by
            rw [hσlen] at hl
            rw [hσget l hl, hτget l hl]
            simp only [Nat.zero_add]
            exact (hpick ⟨l, hl⟩).2.trans (sameOn_restrict _ _).symm)
        have hJf : U.joinAll ([s.anodes[j]!.sub] ++ fulls) = some J := by simpa [fulls] using hJ
        obtain ⟨Jτ, hJτ⟩ := hchain2.1.1 ⟨J, hJf⟩
        obtain ⟨J', hJ'⟩ := hchain1.1.2 ⟨Jτ, hJτ⟩
        have hsame2 := hchain2.2 J Jτ hJf hJτ
        have hsame1 := hchain1.2 J' Jτ hJ' hJτ
        -- the keyed entry of the tuple, and the one kept for its key
        have hconds : s.anodes[j]!.conds ++ ktup.flatMap (·.conds) = [] := by
          rw [anode_conds_nil hs hnp hj, List.nil_append, List.flatMap_eq_nil_iff]
          intro K' hK'
          obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 hK'
          rw [hktget k (hktlen ▸ hk')]
          obtain ⟨_, _, _, hc, _⟩ := keyed_sound_np hs hwf hnp fuel _
            (hA.children k (by rw [← hlen, ← hktlen]; exact hk')).1 _ (hpick ⟨k, hktlen ▸ hk'⟩).1
          exact hc
        have hJ'' : U.joinAll (s.anodes[j]!.sub :: ktup.map (·.sub)) = some J' := by simpa [σs] using hJ'
        have hmemA : ∃ K ∈ anodeK U st s i j (s.anodes[j]!.children.map fun c => keyedE U st s fuel c),
            K.sameKey { tree := .node j (ktup.map (·.tree)), sub := J'.restrict (visible st s i), conds := [] } = true := by
          unfold anodeK
          apply dedupKeys_spec
          simp only [List.mem_filterMap]
          refine ⟨ktup, hktup, ?_⟩
          simp only [hJ'', hconds, judgeAll_nil, Option.map_some]
        obtain ⟨K, hK, hsk⟩ := hmemA
        refine ⟨K, ?_, ?_⟩
        · simp only [keyedE, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨j, (mem_aChildren s i j).2 ⟨hj, hp⟩, hK⟩
        · rw [KEntry.sub_eq_of_sameKey hsk, hEsub]
          simp only [hp] at hsame1 hsame2
          exact (sameOn_restrict _ _).trans (hsame1.trans hsame2.symm)

end Theory
