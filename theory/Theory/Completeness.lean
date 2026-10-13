/-
Completeness (the 2017 paper's Theorem 3, the draft's 4.6): every proof of an instance
of the statement is, after enough rounds, an instance of the proof of an entry at the
root congruent to it.

The first part, here: what the rounds do. A state grows (`Le`): nodes are kept, marks
are kept, attempts are kept. After a round exactly the nodes that existed before it
are expanded (`expandAll_expanded_iff`); a node that exists after round `m` has tried
every assertion by round `m + 1` (`tried_of_lt`); and an assertion node was made in the
round after its parent appeared, so its children are bounded by that round's size
(`anode_round`).
-/
import Theory.Generality

namespace Theory

open State

/-! ### A state grows -/

@[simp] theorem ENode.default_expanded : (default : ENode).expanded = false := rfl

/-- `s'` extends `s`: the nodes of `s` are in `s'`, unchanged but for marks, which are
kept; the numbering is the same; the attempts are kept. -/
structure State.Le (s s' : State) : Prop where
  esize : s.enodes.size ≤ s'.enodes.size
  expr : ∀ k, k < s.enodes.size → s'.enodes[k]!.expr = s.enodes[k]!.expr
  parent : ∀ k, k < s.enodes.size → s'.enodes[k]!.parent = s.enodes[k]!.parent
  expanded : ∀ k, k < s.enodes.size → s.enodes[k]!.expanded = true → s'.enodes[k]!.expanded = true
  asize : s.anodes.size ≤ s'.anodes.size
  anode : ∀ j, j < s.anodes.size → s'.anodes[j]! = s.anodes[j]!
  freshBase : s'.freshBase = s.freshBase
  stride : s'.stride = s.stride
  tried : ∀ x ∈ s.tried, x ∈ s'.tried

theorem State.Le.refl (s : State) : s.Le s where
  esize := le_refl _
  expr := fun _ _ => rfl
  parent := fun _ _ => rfl
  expanded := fun _ _ h => h
  asize := le_refl _
  anode := fun _ _ => rfl
  freshBase := rfl
  stride := rfl
  tried := fun _ h => h

theorem State.Le.trans {s₁ s₂ s₃ : State} (h₁ : s₁.Le s₂) (h₂ : s₂.Le s₃) : s₁.Le s₃ where
  esize := le_trans h₁.esize h₂.esize
  expr := fun k hk => by rw [h₂.expr k (lt_of_lt_of_le hk h₁.esize), h₁.expr k hk]
  parent := fun k hk => by rw [h₂.parent k (lt_of_lt_of_le hk h₁.esize), h₁.parent k hk]
  expanded := fun k hk h => h₂.expanded k (lt_of_lt_of_le hk h₁.esize) (h₁.expanded k hk h)
  asize := le_trans h₁.asize h₂.asize
  anode := fun j hj => by rw [h₂.anode j (lt_of_lt_of_le hj h₁.asize), h₁.anode j hj]
  freshBase := by rw [h₂.freshBase, h₁.freshBase]
  stride := by rw [h₂.stride, h₁.stride]
  tried := fun x hx => h₂.tried x (h₁.tried x hx)

theorem le_addNode (i a : ℕ) (s : State) (A : Assertion) (θ : Subst) : s.Le (addNode i a s A θ) where
  esize := by rw [addNode_enodes_size]; omega
  expr := fun k hk => by rw [addNode_enode_old _ _ _ _ _ k hk]
  parent := fun k hk => by rw [addNode_enode_old _ _ _ _ _ k hk]
  expanded := fun k hk h => by rw [addNode_enode_old _ _ _ _ _ k hk]; exact h
  asize := by rw [addNode_anodes_size]; omega
  anode := fun j hj => addNode_anode_old _ _ _ _ _ j hj
  freshBase := rfl
  stride := rfl
  tried := fun _ h => h

theorem le_recordAt (i a B : ℕ) (s : State) : s.Le (recordAt i a B s) where
  esize := le_refl _
  expr := fun _ _ => rfl
  parent := fun _ _ => rfl
  expanded := fun _ _ h => h
  asize := le_refl _
  anode := fun _ _ => rfl
  freshBase := rfl
  stride := rfl
  tried := fun _ h => List.mem_cons_of_mem _ h

theorem le_mark (i : ℕ) (s : State) : s.Le (mark i s) where
  esize := by simp [mark]
  expr := fun k _ => expr_modify s i k
  parent := fun k _ => parent_modify s i k
  expanded := fun k _ h => by
    simp only [mark, getElem!_modify]
    split_ifs
    · rfl
    · exact h
  asize := le_refl _
  anode := fun _ _ => rfl
  freshBase := rfl
  stride := rfl
  tried := fun _ h => h

theorem le_tryAssertion (U : Unification) (db : Database) (i a : ℕ) (s : State) :
    s.Le (tryAssertion U db i a s) := by
  rcases tryAssertion_cases U db i a s with ⟨h, _⟩ | ⟨A, θ, _, _, h⟩
  · rw [h]; exact le_recordAt _ _ _ _
  · rw [h]; exact (le_addNode _ _ _ _ _).trans (le_recordAt _ _ _ _)

theorem le_foldl {β : Type} (f : State → β → State) (hf : ∀ (s : State) (b : β), s.Le (f s b)) :
    ∀ (l : List β) (s : State), s.Le (l.foldl f s)
  | [], s => State.Le.refl s
  | b :: l, s => (hf s b).trans (le_foldl f hf l (f s b))

theorem le_expandNode (U : Unification) (db : Database) (i : ℕ) (s : State) : s.Le (expandNode U db i s) := by
  unfold expandNode
  exact (le_foldl (fun t a => tryAssertion U db i a t) (fun t a => le_tryAssertion U db i a t)
    (List.range db.asserts.length) s).trans (le_mark _ _)

theorem le_expandAll (U : Unification) (db : Database) (s : State) : s.Le (expandAll U db s) :=
  le_foldl (fun t i => expandNode U db i t) (fun t i => le_expandNode U db i t) _ s

theorem run_le (U : Unification) (db : Database) (st : Statement) :
    ∀ m k, (run U db st m).Le (run U db st (m + k))
  | _, 0 => State.Le.refl _
  | m, k + 1 => (run_le U db st m k).trans (le_expandAll U db _)

theorem run_le_of_le (U : Unification) (db : Database) (st : Statement) {m n : ℕ} (h : m ≤ n) :
    (run U db st m).Le (run U db st n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact run_le U db st m k

/-! ### What a round does -/

/-- After its expansion a node is marked. -/
theorem mark_expanded (i : ℕ) (s : State) (hi : i < s.enodes.size) : (mark i s).enodes[i]!.expanded = true := by
  show (s.enodes.modify i fun n => { n with expanded := true })[i]!.expanded = true
  rw [getElem!_modify]
  simp [hi]

/-- A node marked after an attempt was marked before it: attempts mark nothing, and
the nodes they make are unmarked. -/
theorem expanded_tryAssertion (U : Unification) (db : Database) (i a k : ℕ) (s : State) :
    (tryAssertion U db i a s).enodes[k]!.expanded = true → k < s.enodes.size ∧ s.enodes[k]!.expanded = true := by
  intro h
  rcases tryAssertion_cases U db i a s with ⟨heq, _⟩ | ⟨A, θ, _, _, heq⟩
  · rw [heq] at h
    change s.enodes[k]!.expanded = true at h
    by_cases hk : k < s.enodes.size
    · exact ⟨hk, h⟩
    · rw [getElem!_neg _ k hk] at h
      simp at h
  · rw [heq] at h
    change (addNode i a s A θ).enodes[k]!.expanded = true at h
    by_cases hk : k < s.enodes.size
    · rw [addNode_enode_old _ _ _ _ _ k hk] at h
      exact ⟨hk, h⟩
    · exfalso
      by_cases hk' : k < (addNode i a s A θ).enodes.size
      · rw [addNode_enodes_size] at hk'
        have hkA : k - s.enodes.size < A.hyps.length := by omega
        have : k = s.enodes.size + (k - s.enodes.size) := by omega
        rw [this] at h
        have hk'' : s.enodes.size + (k - s.enodes.size) < (addNode i a s A θ).enodes.size := by
          rw [addNode_enodes_size]; omega
        rw [getElem!_pos (addNode i a s A θ).enodes _ hk''] at h
        simp only [addNode] at h
        rw [Array.getElem_append_right (by omega)] at h
        simp [newENodes, Nat.add_sub_cancel_left] at h
      · rw [getElem!_neg _ k hk'] at h
        simp at h

theorem expanded_foldl_tryAssertion (U : Unification) (db : Database) (i : ℕ) :
    ∀ (l : List ℕ) (s : State) (k : ℕ),
      (l.foldl (fun t a => tryAssertion U db i a t) s).enodes[k]!.expanded = true →
      k < s.enodes.size ∧ s.enodes[k]!.expanded = true
  | [], s, k, h => by
    simp only [List.foldl_nil] at h
    refine ⟨?_, h⟩
    by_contra hk
    rw [getElem!_neg _ k hk] at h
    simp at h
  | a :: l, s, k, h => by
    simp only [List.foldl_cons] at h
    exact expanded_tryAssertion U db i a k s (expanded_foldl_tryAssertion U db i l _ k h).2

theorem expanded_expandNode_iff (U : Unification) (db : Database) (i : ℕ) (s : State) (hi : i < s.enodes.size)
    (k : ℕ) :
    (expandNode U db i s).enodes[k]!.expanded = true ↔
      k < s.enodes.size ∧ (s.enodes[k]!.expanded = true ∨ k = i) := by
  have hle := le_foldl (fun t a => tryAssertion U db i a t) (fun t a => le_tryAssertion U db i a t)
    (List.range db.asserts.length) s
  unfold expandNode
  simp only [mark, getElem!_modify]
  constructor
  · intro h
    split_ifs at h with hk
    · obtain ⟨_, hik⟩ := hk
      subst hik
      exact ⟨hi, Or.inr rfl⟩
    · exact (expanded_foldl_tryAssertion U db i _ s k h).imp_right Or.inl
  · rintro ⟨hk, hor⟩
    rcases hor with hex | rfl
    · split_ifs
      · rfl
      · exact hle.expanded k hk hex
    · simp [lt_of_lt_of_le hk hle.esize]

theorem expanded_foldl_expandNode_iff (U : Unification) (db : Database) :
    ∀ (l : List ℕ) (s : State), (∀ i ∈ l, i < s.enodes.size) → ∀ k,
      (l.foldl (fun t i => expandNode U db i t) s).enodes[k]!.expanded = true ↔
        k < s.enodes.size ∧ (s.enodes[k]!.expanded = true ∨ k ∈ l)
  | [], s, _, k => by
    simp only [List.foldl_nil, List.not_mem_nil, or_false]
    constructor
    · intro h
      refine ⟨?_, h⟩
      by_contra hk
      rw [getElem!_neg s.enodes k hk] at h
      simp at h
    · exact fun h => h.2
  | i :: l, s, hl, k => by
    simp only [List.foldl_cons, List.mem_cons]
    have hi : i < s.enodes.size := hl i List.mem_cons_self
    have hle := le_expandNode U db i s
    rw [expanded_foldl_expandNode_iff U db l (expandNode U db i s)
      (fun i' hi' => lt_of_lt_of_le (hl i' (List.mem_cons_of_mem _ hi')) hle.esize) k,
      expanded_expandNode_iff U db i s hi k]
    constructor
    · rintro ⟨_, ⟨hk, hor⟩ | hmem⟩
      · rcases hor with hex | rfl
        · exact ⟨hk, Or.inl hex⟩
        · exact ⟨hk, Or.inr (Or.inl rfl)⟩
      · exact ⟨hl k (List.mem_cons_of_mem _ hmem), Or.inr (Or.inr hmem)⟩
    · rintro ⟨hk, hex | rfl | hmem⟩
      · exact ⟨lt_of_lt_of_le hk hle.esize, Or.inl ⟨hk, Or.inl hex⟩⟩
      · exact ⟨lt_of_lt_of_le hk hle.esize, Or.inl ⟨hk, Or.inr rfl⟩⟩
      · exact ⟨lt_of_lt_of_le hk hle.esize, Or.inr hmem⟩

/-- After a round, exactly the nodes that existed before it are expanded. -/
theorem expandAll_expanded_iff (U : Unification) (db : Database) (s : State) (k : ℕ) :
    (expandAll U db s).enodes[k]!.expanded = true ↔ k < s.enodes.size := by
  unfold expandAll
  rw [expanded_foldl_expandNode_iff U db _ s (fun i hi => List.mem_range.1 (List.mem_of_mem_filter hi)) k]
  constructor
  · exact fun h => h.1
  · intro hk
    refine ⟨hk, ?_⟩
    by_cases hex : s.enodes[k]!.expanded = true
    · exact Or.inl hex
    · exact Or.inr (List.mem_filter.2 ⟨List.mem_range.2 hk, by simp [hex]⟩)

theorem run_expanded_iff (U : Unification) (db : Database) (st : Statement) :
    ∀ (n k : ℕ), (run U db st (n + 1)).enodes[k]!.expanded = true ↔ k < (run U db st n).enodes.size :=
  fun n k => expandAll_expanded_iff U db (run U db st n) k

theorem run_zero_unexpanded (U : Unification) (db : Database) (st : Statement) (k : ℕ) :
    (run U db st 0).enodes[k]!.expanded = false := by
  by_cases hk : k = 0
  · subst hk; simp [run, init]
  · have : ¬ k < (run U db st 0).enodes.size := by simp [run, init]; omega
    rw [getElem!_neg _ k this]
    rfl

/-! ### Attempts -/

theorem tried_foldl_expandNode (U : Unification) (db : Database) :
    ∀ (l : List ℕ) (s : State), ∀ i ∈ l, ∀ a, a < db.asserts.length →
      ∃ B, (i, a, B) ∈ (l.foldl (fun t i => expandNode U db i t) s).tried
  | [], _, i, hi, _, _ => by simp at hi
  | i' :: l, s, i, hi, a, ha => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | hi
    · obtain ⟨B, hB⟩ : ∃ B, (i, a, B) ∈ (expandNode U db i s).tried := by
        unfold expandNode
        simp only [mark]
        exact foldl_tried U db i _ s a (List.mem_range.2 ha)
      exact ⟨B, (le_foldl (fun t i => expandNode U db i t) (fun t i => le_expandNode U db i t) l _).tried _ hB⟩
    · exact tried_foldl_expandNode U db l _ i hi a ha

/-- A node not expanded before a round has tried every assertion after it. -/
theorem expandAll_tried (U : Unification) (db : Database) (s : State) (i : ℕ) (hi : i < s.enodes.size)
    (hex : ¬ s.enodes[i]!.expanded = true) (a : ℕ) (ha : a < db.asserts.length) :
    ∃ B, (i, a, B) ∈ (expandAll U db s).tried := by
  unfold expandAll
  exact tried_foldl_expandNode U db _ s i (List.mem_filter.2 ⟨List.mem_range.2 hi, by simp [hex]⟩) a ha

/-- A node that exists after round `m` has tried every assertion after round `m + 1`. -/
theorem tried_of_lt (U : Unification) (db : Database) (st : Statement) :
    ∀ (m i : ℕ), i < (run U db st m).enodes.size → ∀ a, a < db.asserts.length →
      ∃ B, (i, a, B) ∈ (run U db st (m + 1)).tried
  | 0, i, hi, a, ha => by
    have hex : ¬ (run U db st 0).enodes[i]!.expanded = true := by simp [run_zero_unexpanded]
    exact expandAll_tried U db _ i hi hex a ha
  | m + 1, i, hi, a, ha => by
    by_cases him : i < (run U db st m).enodes.size
    · obtain ⟨B, hB⟩ := tried_of_lt U db st m i him a ha
      exact ⟨B, (le_expandAll U db _).tried _ hB⟩
    · have hex : ¬ (run U db st (m + 1)).enodes[i]!.expanded = true := by
        rw [run_expanded_iff]; exact him
      exact expandAll_tried U db _ i hi hex a ha

/-! ### When an assertion node was made -/

/-- The assertion nodes a step adds have the expanded node as parent, and children
within the result. -/
theorem anodes_tryAssertion (U : Unification) (db : Database) (i a : ℕ) (s : State) (j : ℕ)
    (hj : s.anodes.size ≤ j) (hj' : j < (tryAssertion U db i a s).anodes.size) :
    (tryAssertion U db i a s).anodes[j]!.parent = i ∧
    ∀ k, k < (tryAssertion U db i a s).anodes[j]!.children.length →
      (tryAssertion U db i a s).anodes[j]!.children[k]! < (tryAssertion U db i a s).enodes.size := by
  rcases tryAssertion_cases U db i a s with ⟨heq, _⟩ | ⟨A, θ, _, _, heq⟩
  · rw [heq] at hj' ⊢
    simp only [recordAt] at hj' ⊢
    omega
  · rw [heq] at hj' ⊢
    simp only [recordAt] at hj' ⊢
    rw [addNode_anodes_size] at hj'
    have : j = s.anodes.size := by omega
    subst this
    rw [addNode_anode_new]
    refine ⟨rfl, ?_⟩
    intro k hk
    simp only [List.length_map, List.length_range] at hk
    simp only
    rw [getElem!_map_range _ _ k hk, addNode_enodes_size]
    omega

theorem anodes_foldl_tryAssertion (U : Unification) (db : Database) (i : ℕ) :
    ∀ (l : List ℕ) (s : State) (j : ℕ), s.anodes.size ≤ j →
      j < (l.foldl (fun t a => tryAssertion U db i a t) s).anodes.size →
      (l.foldl (fun t a => tryAssertion U db i a t) s).anodes[j]!.parent = i ∧
      ∀ k, k < (l.foldl (fun t a => tryAssertion U db i a t) s).anodes[j]!.children.length →
        (l.foldl (fun t a => tryAssertion U db i a t) s).anodes[j]!.children[k]! <
          (l.foldl (fun t a => tryAssertion U db i a t) s).enodes.size
  | [], _, _, h1, h2 => by simp only [List.foldl_nil] at h2; omega
  | a :: l, s, j, h1, h2 => by
    simp only [List.foldl_cons] at h2 ⊢
    have hle := le_foldl (fun t a => tryAssertion U db i a t) (fun t a => le_tryAssertion U db i a t) l (tryAssertion U db i a s)
    by_cases hj : j < (tryAssertion U db i a s).anodes.size
    · have := anodes_tryAssertion U db i a s j h1 hj
      rw [hle.anode j hj]
      exact ⟨this.1, fun k hk => lt_of_lt_of_le (this.2 k hk) hle.esize⟩
    · exact anodes_foldl_tryAssertion U db i l _ j (by omega) h2

theorem anodes_expandNode (U : Unification) (db : Database) (i : ℕ) (s : State) (j : ℕ)
    (hj : s.anodes.size ≤ j) (hj' : j < (expandNode U db i s).anodes.size) :
    (expandNode U db i s).anodes[j]!.parent = i ∧
    ∀ k, k < (expandNode U db i s).anodes[j]!.children.length →
      (expandNode U db i s).anodes[j]!.children[k]! < (expandNode U db i s).enodes.size := by
  unfold expandNode at hj' ⊢
  simp only [mark] at hj' ⊢
  have := anodes_foldl_tryAssertion U db i (List.range db.asserts.length) s j hj hj'
  simpa using this

/-- An assertion node added by a round has as parent a node that was in the round's
list — it existed and was not expanded — and children within the round's result. -/
theorem anodes_foldl_expandNode (U : Unification) (db : Database) :
    ∀ (l : List ℕ) (s : State) (j : ℕ), s.anodes.size ≤ j →
      j < (l.foldl (fun t i => expandNode U db i t) s).anodes.size →
      (l.foldl (fun t i => expandNode U db i t) s).anodes[j]!.parent ∈ l ∧
      ∀ k, k < (l.foldl (fun t i => expandNode U db i t) s).anodes[j]!.children.length →
        (l.foldl (fun t i => expandNode U db i t) s).anodes[j]!.children[k]! <
          (l.foldl (fun t i => expandNode U db i t) s).enodes.size
  | [], _, _, h1, h2 => by simp only [List.foldl_nil] at h2; omega
  | i :: l, s, j, h1, h2 => by
    simp only [List.foldl_cons] at h2 ⊢
    have hle := le_foldl (fun t i => expandNode U db i t) (fun t i => le_expandNode U db i t) l (expandNode U db i s)
    by_cases hj : j < (expandNode U db i s).anodes.size
    · have := anodes_expandNode U db i s j h1 hj
      rw [hle.anode j hj]
      exact ⟨by rw [this.1]; exact List.mem_cons_self, fun k hk => lt_of_lt_of_le (this.2 k hk) hle.esize⟩
    · have := anodes_foldl_expandNode U db l _ j (by omega) h2
      exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem anodes_expandAll (U : Unification) (db : Database) (s : State) (j : ℕ)
    (hj : s.anodes.size ≤ j) (hj' : j < (expandAll U db s).anodes.size) :
    ((expandAll U db s).anodes[j]!.parent < s.enodes.size ∧
      ¬ s.enodes[(expandAll U db s).anodes[j]!.parent]!.expanded = true) ∧
    ∀ k, k < (expandAll U db s).anodes[j]!.children.length →
      (expandAll U db s).anodes[j]!.children[k]! < (expandAll U db s).enodes.size := by
  unfold expandAll at hj' ⊢
  have := anodes_foldl_expandNode U db _ s j hj hj'
  refine ⟨?_, this.2⟩
  have hmem := List.mem_filter.1 this.1
  exact ⟨List.mem_range.1 hmem.1, by simpa using hmem.2⟩

/-- Every assertion node of a run was made in the round after its parent appeared:
there is a round `r` before which the parent did not exist, in which it existed and
was not expanded, and whose expansion gave the node, with its children within the
round's result. -/
theorem anode_round (U : Unification) (db : Database) (st : Statement) :
    ∀ (n j : ℕ), j < (run U db st n).anodes.size → ∃ r, r < n ∧
      (run U db st n).anodes[j]!.parent < (run U db st r).enodes.size ∧
      ¬ (run U db st r).enodes[(run U db st n).anodes[j]!.parent]!.expanded = true ∧
      ∀ k, k < (run U db st n).anodes[j]!.children.length →
        (run U db st n).anodes[j]!.children[k]! < (run U db st (r + 1)).enodes.size
  | 0, j, hj => by simp [run, init] at hj
  | n + 1, j, hj => by
    by_cases hjn : j < (run U db st n).anodes.size
    · obtain ⟨r, hr, h1, h2, h3⟩ := anode_round U db st n j hjn
      have hle := le_expandAll U db (run U db st n)
      refine ⟨r, by omega, ?_, ?_, ?_⟩ <;> rw [show run U db st (n + 1) = expandAll U db (run U db st n) from rfl, hle.anode j hjn]
      · exact h1
      · exact h2
      · exact h3
    · refine ⟨n, by omega, ?_⟩
      have := anodes_expandAll U db (run U db st n) j (by omega) hj
      exact ⟨this.1.1, this.1.2, this.2⟩

/-- A node that is a parent and existed after round `m` had its assertion nodes made
by round `m + 1`, with children within that round's result. -/
theorem children_lt_of_parent (U : Unification) (db : Database) (st : Statement) {n m j : ℕ}
    (hj : j < (run U db st n).anodes.size)
    (hm : (run U db st n).anodes[j]!.parent < (run U db st m).enodes.size) :
    ∀ k, k < (run U db st n).anodes[j]!.children.length →
      (run U db st n).anodes[j]!.children[k]! < (run U db st (m + 1)).enodes.size := by
  obtain ⟨r, hr, h1, h2, h3⟩ := anode_round U db st n j hj
  intro k hk
  refine lt_of_lt_of_le (h3 k hk) ?_
  -- r ≤ m: were r > m, the parent would be expanded in round r, since it existed after round m ≤ r - 1
  have hrm : r ≤ m := by
    by_contra hlt
    rw [Nat.not_le] at hlt
    apply h2
    cases r with
    | zero => omega
    | succ r' =>
      rw [run_expanded_iff]
      exact lt_of_lt_of_le hm (run_le_of_le U db st (by omega)).esize
  exact (run_le_of_le U db st (by omega)).esize

/-! ### Heights -/

mutual
/-- The height of a proof tree: a leaf is 0, a step one more than its children. -/
def PTree.height : PTree → ℕ
  | .hyp _ _ => 0
  | .step _ _ _ cs => PTree.heightList cs + 1
def PTree.heightList : List PTree → ℕ
  | [] => 0
  | t :: ts => max t.height (PTree.heightList ts)
end

theorem PTree.height_child : ∀ (cs : List PTree) (k : ℕ), k < cs.length → cs[k]!.height ≤ PTree.heightList cs
  | [], _, hk => by simp at hk
  | c :: cs, 0, _ => by simp [PTree.heightList]
  | c :: cs, k + 1, hk => by
    simp only [List.length_cons] at hk
    simp only [PTree.heightList, List.getElem!_cons_succ]
    exact le_trans (PTree.height_child cs k (by omega)) (le_max_right _ _)

mutual
/-- The depth an entry for a tree needs: a leaf 1, a node one more than its children. -/
def SptTree.fuel : SptTree → ℕ
  | .leaf _ _ => 1
  | .node _ cs => SptTree.fuelList cs + 1
def SptTree.fuelList : List SptTree → ℕ
  | [] => 0
  | t :: ts => max t.fuel (SptTree.fuelList ts)
end

theorem SptTree.fuel_child : ∀ (cs : List SptTree) (k : ℕ), k < cs.length → cs[k]!.fuel ≤ SptTree.fuelList cs
  | [], _, hk => by simp at hk
  | c :: cs, 0, _ => by simp [SptTree.fuelList]
  | c :: cs, k + 1, hk => by
    simp only [List.length_cons] at hk
    simp only [SptTree.fuelList, List.getElem!_cons_succ]
    exact le_trans (SptTree.fuel_child cs k (by omega)) (le_max_right _ _)

theorem SptTree.fuelList_le : ∀ (cs : List SptTree) (b : ℕ), (∀ k, k < cs.length → cs[k]!.fuel ≤ b) →
    SptTree.fuelList cs ≤ b
  | [], _, _ => Nat.zero_le _
  | c :: cs, b, h => by
    simp only [SptTree.fuelList]
    refine max_le (by simpa using h 0 (by simp)) ?_
    exact SptTree.fuelList_le cs b (fun k hk => by simpa using h (k + 1) (by simp; omega))

/-- The depth a tree needs is within the state: along every path the expression nodes
go up. -/
theorem fuel_le {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s) :
    ∀ {i : ℕ} {T : SptTree}, T.At s i → T.fuel + i ≤ s.enodes.size := by
  intro i T hat
  induction hat with
  | leaf i h hi => simp only [SptTree.fuel]; omega
  | node i j cs hj hp hlen hcs ih =>
    obtain ⟨A, hinv⟩ := hs.anodes j hj
    obtain ⟨n, hn, hch⟩ := hinv.children_eq
    have hi : i < s.enodes.size := by rw [← hp]; exact hinv.parent_lt
    simp only [SptTree.fuel]
    have : SptTree.fuelList cs ≤ s.enodes.size - i - 1 := by
      apply SptTree.fuelList_le
      intro k hk
      have hkA : k < A.hyps.length := by rw [hch] at hlen; simp at hlen; omega
      have := ih k hk
      rw [hch, getElem!_map_range _ _ k hkA] at this
      rw [hp] at hn
      omega
    omega

/-! ### The variant of a proof -/

/-- A substitution overridden at the renamed binders of an assertion by what a step
gives them. -/
def override (ρ : Subst) (B : ℕ) (A : Assertion) (θπ : Subst) : Subst :=
  Subst.ofFun (ρ.dom ∪ (A.vars.map (renamed B)).toFinset)
    (fun v => if B ≤ v.id ∧ (⟨v.id - B, v.ty⟩ : Var) ∈ A.vars then θπ.f ⟨v.id - B, v.ty⟩ else ρ.f v)
    (fun v hv => by
      rw [Finset.mem_union, not_or, List.mem_toFinset, List.mem_map] at hv
      split_ifs with h
      · exfalso
        apply hv.2
        refine ⟨⟨v.id - B, v.ty⟩, h.2, ?_⟩
        obtain ⟨id, ty⟩ := v
        simp only [renamed, Var.mk.injEq, and_true]
        simp only at h
        omega
      · exact Subst.f_eq_of_not_mem hv.1)

theorem override_f_renamed (ρ : Subst) (B : ℕ) (A : Assertion) (θπ : Subst) {x : Var} (hx : x ∈ A.vars) :
    (override ρ B A θπ).f (renamed B x) = θπ.f x := by
  have h1 : B ≤ (renamed B x).id := by simp [renamed]
  have h2 : (⟨(renamed B x).id - B, (renamed B x).ty⟩ : Var) = x := by
    obtain ⟨id, ty⟩ := x
    simp [renamed]
  simp only [override, Subst.ofFun]
  rw [h2]
  simp [h1, hx]

theorem override_f_lt (ρ : Subst) (B : ℕ) (A : Assertion) (θπ : Subst) {v : Var} (hv : v.id < B) :
    (override ρ B A θπ).f v = ρ.f v := by
  simp only [override, Subst.ofFun]
  split_ifs with h
  · exfalso; omega
  · rfl

theorem override_typed {ρ θπ : Subst} (hρ : ρ.Typed) (hθ : θπ.Typed) (B : ℕ) (A : Assertion) :
    (override ρ B A θπ).Typed := by
  intro v
  simp only [override, Subst.ofFun]
  split_ifs
  · exact hθ ⟨v.id - B, v.ty⟩
  · exact hρ v

/-- The override solves the equation of an assertion at a fresh base. -/
theorem override_solves {ρ θπ : Subst} {B : ℕ} {A : Assertion} (hwfA : A.WF) {e : Exp}
    (he : ∀ v ∈ e.vars, v.id < B) {g : Exp} (hρ : ρ.apply e = g) (hθ : θπ.apply A.concl = g) :
    Solves (override ρ B A θπ) [(e, A.concl.rename B)] := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  show (override ρ B A θπ).apply e = (override ρ B A θπ).apply (A.concl.rename B)
  rw [apply_congr_vars e (fun v hv => override_f_lt ρ B A θπ (he v hv)), hρ,
    apply_rename_eq A.concl (fun x hx => override_f_renamed ρ B A θπ (List.mem_toFinset.1 (hwfA.concl_vars hx))), hθ]

/-- The assertion node at an expression node for an assertion, if any. -/
def findNode (s : State) (i a : ℕ) : Option ℕ :=
  (aChildren s i).find? fun j => s.anodes[j]!.assertion == a

theorem findNode_some {s : State} {i a j : ℕ} (h : findNode s i a = some j) :
    j ∈ aChildren s i ∧ s.anodes[j]!.assertion = a := by
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  exact ⟨h2, by simpa using h1⟩

theorem findNode_some_of_mem {s : State} {i a j : ℕ} (hj : j ∈ aChildren s i) (ha : s.anodes[j]!.assertion = a) :
    ∃ j', findNode s i a = some j' := by
  cases h : findNode s i a with
  | some j' => exact ⟨j', rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.1 h j hj
    simp [ha] at this

mutual
/-- The variant of a proof in a state: at each step the assertion node of the state
for its assertion, at each leaf its hypothesis. -/
def treeOf (s : State) : PTree → ℕ → SptTree
  | .hyp h _, i => .leaf i h
  | .step _ a _ cs, i =>
    match findNode s i a with
    | some j => .node j (treeOfList s cs s.anodes[j]!.children)
    | none => .leaf i 0
def treeOfList (s : State) : List PTree → List ℕ → List SptTree
  | c :: cs, e :: es => treeOf s c e :: treeOfList s cs es
  | _, _ => []
end

theorem treeOfList_length (s : State) : ∀ (cs : List PTree) (es : List ℕ), cs.length = es.length →
    (treeOfList s cs es).length = cs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c :: cs, e :: es, h => by
    simp only [treeOfList, List.length_cons]
    rw [treeOfList_length s cs es (by simpa using h)]

theorem treeOfList_getElem (s : State) : ∀ (cs : List PTree) (es : List ℕ) (k : ℕ), k < cs.length → k < es.length →
    (treeOfList s cs es)[k]! = treeOf s cs[k]! es[k]!
  | [], _, _, hk, _ => by simp at hk
  | _ :: _, [], _, _, hk => by simp at hk
  | c :: cs, e :: es, 0, _, _ => by simp [treeOfList]
  | c :: cs, e :: es, k + 1, hk, hk' => by
    simp only [treeOfList, List.getElem!_cons_succ]
    exact treeOfList_getElem s cs es k (by simpa using hk) (by simpa using hk')

/-- The variant of a proof is in the graph after as many rounds as the proof is high,
and the proof follows it. -/
theorem treeOf_at {U : Unification} {db : Database} (hwf : db.WF) {st : Statement} (n : ℕ) {σ : Subst} :
    ∀ {π : PTree}, Shape db (st.subst σ) π →
      ∀ (m i : ℕ), i < (run U db st m).enodes.size → m + π.height + 1 ≤ n →
      ∀ ρ : Subst, ρ.Typed → π.expr = ρ.apply (run U db st n).enodes[i]!.expr →
      (treeOf (run U db st n) π i).At (run U db st n) i ∧
        Matches (run U db st n) π (treeOf (run U db st n) π i) := by
  intro π hsh
  induction hsh with
  | hyp h e hh he =>
    intro m i hi hn ρ hρ hexpr
    have hi' : i < (run U db st n).enodes.size :=
      lt_of_lt_of_le hi (run_le_of_le U db st (by omega : m ≤ n)).esize
    exact ⟨SptTree.At.leaf i h hi', Matches.leaf h e i⟩
  | step e a θπ cs A hA hθ hdom he hcse hall ih =>
    intro m i hi hn ρ hρ hexpr
    simp only [PTree.expr] at hexpr
    simp only [PTree.height] at hn
    have hs := run_inv U db hwf st n
    have hs₁ := run_inv U db hwf st (m + 1)
    have hwfA : A.WF := hwf A (List.mem_of_getElem? hA)
    have haN : a < db.asserts.length := (List.getElem?_eq_some_iff.1 hA).1
    have hle₁ : (run U db st (m + 1)).Le (run U db st n) := run_le_of_le U db st (by omega)
    have hle₀ : (run U db st m).Le (run U db st (m + 1)) := run_le_of_le U db st (by omega)
    have hi₁ : i < (run U db st (m + 1)).enodes.size := lt_of_lt_of_le hi hle₀.esize
    have hin : i < (run U db st n).enodes.size := lt_of_lt_of_le hi₁ hle₁.esize
    -- the attempt at `(i, a)` is recorded by round `m + 1`
    obtain ⟨B, hB⟩ := tried_of_lt U db st m i hi a haN
    have hBn : (i, a, B) ∈ (run U db st n).tried := hle₁.tried _ hB
    -- its node exists: the override solves its equation
    have hexists : ∃ j, j < (run U db st n).anodes.size ∧ (run U db st n).anodes[j]!.parent = i ∧
        (run U db st n).anodes[j]!.assertion = a := by
      rcases hs.tried_spec i a B hBn A hA with h | hnone
      · exact h
      · exfalso
        have hfresh := hs.tried_fresh i a B hBn
        have hsol := override_solves hwfA hfresh hexpr.symm he.symm
        obtain ⟨θ', hθ', _⟩ := U.mostGeneral _ _ (override_typed hρ hθ B A) hsol
        rw [hnone] at hθ'
        simp at hθ'
    obtain ⟨j, hj, hp, ha⟩ := hexists
    obtain ⟨j', hfind⟩ := findNode_some_of_mem ((mem_aChildren _ i j).2 ⟨hj, hp⟩) ha
    obtain ⟨hj'mem, ha'⟩ := findNode_some hfind
    obtain ⟨hj', hp'⟩ := (mem_aChildren _ i j').1 hj'mem
    obtain ⟨A', hinv⟩ := hs.anodes j' hj'
    have hAA : A' = A := by
      have h1 := hinv.assertion
      rw [ha', hA] at h1
      exact (Option.some.inj h1).symm
    subst hAA
    have hbase : (run U db st n).anodes[j']!.base = (run U db st n).baseOf j' := hs.base_eq j' hj'
    -- the children are within round `m + 1`
    have hchild_lt : ∀ k, k < (run U db st n).anodes[j']!.children.length →
        (run U db st n).anodes[j']!.children[k]! < (run U db st (m + 1)).enodes.size :=
      children_lt_of_parent U db st hj' (by rw [hp']; exact hi)
    -- the local substitution of the children
    set ρ' := override ρ (run U db st n).anodes[j']!.base A' θπ with hρ'
    have hρ't : ρ'.Typed := override_typed hρ hθ _ _
    have hpv := hinv.parent_vars_lt
    rw [hp'] at hpv
    have hρ'e : ρ'.apply (run U db st n).enodes[i]!.expr = e := by
      rw [apply_congr_vars _ (fun v hv => override_f_lt ρ _ A' θπ (hpv v hv))]
      exact hexpr.symm
    have hren : ∀ q : Exp, q.vars ⊆ A'.vars.toFinset →
        ρ'.apply (q.rename (run U db st n).anodes[j']!.base) = θπ.apply q :=
      fun q hq => apply_rename_eq q (fun x hx => override_f_renamed ρ _ A' θπ (List.mem_toFinset.1 (hq hx)))
    have habs : ρ'.comp (run U db st n).anodes[j']!.sub = ρ' := by
      have hmgu := hinv.is_mgu
      rw [hp'] at hmgu
      obtain ⟨θ'', hθ'', hinst⟩ := U.mostGeneral
        [((run U db st n).enodes[i]!.expr, A'.concl.rename (run U db st n).anodes[j']!.base)] ρ' hρ't
        (fun p hp'' => by
          rw [List.mem_singleton] at hp''
          subst hp''
          show ρ'.apply _ = ρ'.apply _
          rw [hρ'e, hren A'.concl hwfA.concl_vars]
          exact he)
      rw [hmgu] at hθ''
      obtain rfl := Option.some.inj hθ''
      exact Subst.comp_eq_of_instance hinv.idem hinst
    have hlencs : cs.length = (run U db st n).anodes[j']!.children.length := by
      rw [hinv.children_len]
      have := congrArg List.length hcse
      simpa using this
    have hchild : ∀ k, k < cs.length →
        (treeOf (run U db st n) cs[k]! (run U db st n).anodes[j']!.children[k]!).At (run U db st n)
          (run U db st n).anodes[j']!.children[k]! ∧
        Matches (run U db st n) cs[k]! (treeOf (run U db st n) cs[k]! (run U db st n).anodes[j']!.children[k]!) := by
      intro k hk
      have hkA : k < A'.hyps.length := by rw [← hinv.children_len, ← hlencs]; exact hk
      have hmem : cs[k]! ∈ cs := by rw [getElem!_pos cs k hk]; exact List.getElem_mem hk
      refine ih _ hmem (m + 1) _ (hchild_lt k (hlencs ▸ hk)) ?_ ρ' hρ't ?_
      · have := PTree.height_child cs k hk
        omega
      · rw [(hinv.children k (hlencs ▸ hk)).2, ← Subst.apply_comp, habs,
          hren _ (hwfA.hyps_vars _ (by rw [getElem!_pos A'.hyps k hkA]; exact List.getElem_mem hkA))]
        rw [← getElem!_map' PTree.expr cs k hk, hcse, getElem!_map' θπ.apply A'.hyps k hkA]
    have hT : treeOf (run U db st n) (.step e a θπ cs) i =
        .node j' (treeOfList (run U db st n) cs (run U db st n).anodes[j']!.children) := by
      simp [treeOf, hfind]
    rw [hT]
    have hlen' := treeOfList_length (run U db st n) cs _ hlencs
    refine ⟨SptTree.At.node i j' _ hj' hp' (by rw [hlen']; exact hlencs) ?_,
      Matches.node e a θπ cs j' _ ha' (by rw [hlen']) ?_⟩
    · intro k hk
      rw [hlen'] at hk
      rw [treeOfList_getElem _ cs _ k hk (hlencs ▸ hk)]
      exact (hchild k hk).1
    · intro k hk
      rw [treeOfList_getElem _ cs _ k hk (hlencs ▸ hk)]
      exact (hchild k hk).2

/-! ### The entry of a variant -/

theorem mem_tuples_of_index : ∀ (ls : List (List Entry)) (tup : List Entry), tup.length = ls.length →
    (∀ k, k < ls.length → tup[k]! ∈ ls[k]!) → tup ∈ tuples ls
  | [], [], _, _ => by simp [tuples]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | l :: ls, x :: tup, h, hk => by
    simp only [tuples, List.mem_flatMap, List.mem_map]
    refine ⟨x, by simpa using hk 0 (by simp), tup, ?_, rfl⟩
    exact mem_tuples_of_index ls tup (by simpa using h) (fun k hk' => by simpa using hk (k + 1) (by simp; omega))

theorem sptE_mono (U : Unification) (st : Statement) (s : State) :
    ∀ (f f' : ℕ), f ≤ f' → ∀ i E, E ∈ sptE U st s f i → E ∈ sptE U st s f' i
  | 0, _, _, _, _, hE => by simp [sptE] at hE
  | f + 1, 0, h, _, _, _ => by omega
  | f + 1, f' + 1, h, i, E, hE => by
    simp only [sptE, List.mem_append, List.mem_flatMap] at hE ⊢
    rcases hE with hE | ⟨j, hj, hE⟩
    · exact Or.inl hE
    · refine Or.inr ⟨j, hj, ?_⟩
      simp only [anodeEntries, List.mem_filterMap] at hE ⊢
      obtain ⟨tup, htup, hmk⟩ := hE
      refine ⟨tup, ?_, hmk⟩
      obtain ⟨hlen, hk⟩ := mem_tuples _ tup htup
      simp only [List.length_map] at hlen
      refine mem_tuples_of_index _ tup (by simpa using hlen) ?_
      intro k hk'
      simp only [List.length_map] at hk'
      have := hk k (by simpa using hk')
      rw [getElem!_map _ _ k hk'] at this ⊢
      exact sptE_mono U st s f f' (by omega) _ _ this

theorem mem_condsList_of_index (s : State) : ∀ (cs : List SptTree) (k : ℕ), k < cs.length →
    ∀ c ∈ cs[k]!.conds s, c ∈ SptTree.condsList s cs
  | [], _, hk => by simp at hk
  | t :: ts, 0, _ => fun c hc => by
    simp only [SptTree.condsList, List.mem_append]
    exact Or.inl (by simpa using hc)
  | t :: ts, k + 1, hk => fun c hc => by
    simp only [SptTree.condsList, List.mem_append]
    exact Or.inr (mem_condsList_of_index s ts k (by simpa using hk) c (by simpa using hc))

/-- A tree the answer absorbs, whose conditions hold under the answer, has an entry at
the depth it needs, with that tree. -/
theorem entry_exists {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s) :
    ∀ {T : SptTree} {i : ℕ}, T.At s i → ∀ ρ : Subst, ρ.Typed → Absorbs s st ρ T →
      (∀ k ∈ (T.conds s).map (Cond.apply ρ), k.Holds st.consts) →
      ∀ fuel, T.fuel ≤ fuel → ∃ E ∈ sptE U st s fuel i, E.tree = T := by
  intro T i hat
  induction hat with
  | leaf i h hi =>
    intro ρ hρ habs _ fuel hfuel
    cases habs with
    | leaf _ _ hh heq =>
      cases fuel with
      | zero => simp [SptTree.fuel] at hfuel
      | succ f =>
        obtain ⟨θ, hθ, _⟩ := U.mostGeneral [(s.enodes[i]!.expr, st.hyps[h]!)] ρ hρ (fun p hp => by
          rw [List.mem_singleton] at hp
          subst hp
          exact heq)
        refine ⟨{ tree := .leaf i h, sub := θ, conds := [] }, ?_, rfl⟩
        simp only [sptE, List.mem_append]
        left
        simp only [leafEntries, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff]
        exact ⟨h, hh, θ, hθ, rfl⟩
  | node i j cs hj hp hlen hcs ih =>
    intro ρ hρ habs hconds fuel hfuel
    cases habs with
    | node _ _ hab hcsabs =>
      cases fuel with
      | zero => simp [SptTree.fuel] at hfuel
      | succ f =>
        simp only [SptTree.fuel] at hfuel
        obtain ⟨A, hinv⟩ := hs.anodes j hj
        -- an entry for each child
        have hchild : ∀ k, k < cs.length → ∃ E ∈ sptE U st s f s.anodes[j]!.children[k]!, E.tree = cs[k]! := by
          intro k hk
          have hmem : cs[k]! ∈ cs := by rw [getElem!_pos cs k hk]; exact List.getElem_mem hk
          refine ih k hk ρ hρ (hcsabs _ hmem) ?_ f ?_
          · intro c hc
            apply hconds
            rw [List.mem_map] at hc ⊢
            obtain ⟨c', hc', rfl⟩ := hc
            exact ⟨c', by
              simp only [SptTree.conds, List.mem_append]
              exact Or.inr (mem_condsList_of_index s cs k hk c' hc'), rfl⟩
          · have := SptTree.fuel_child cs k hk
            omega
        choose Es hEs using hchild
        -- the tuple of them
        let tup : List Entry := (List.range cs.length).map fun k => if hk : k < cs.length then Es k hk else default
        have htupget : ∀ k (hk : k < cs.length), tup[k]! = Es k hk := by
          intro k hk
          simp only [tup]
          rw [getElem!_map_range _ _ k hk]
          simp [hk]
        have htuplen : tup.length = cs.length := by simp [tup]
        have htup : tup ∈ tuples (s.anodes[j]!.children.map fun c => sptE U st s f c) := by
          refine mem_tuples_of_index _ tup (by simp [htuplen, hlen]) ?_
          intro k hk
          simp only [List.length_map] at hk
          rw [getElem!_map _ _ k hk, htupget k (hlen ▸ hk)]
          exact (hEs k (hlen ▸ hk)).1
        have htrees : tup.map (·.tree) = cs := by
          apply List.ext_getElem (by simp [htuplen])
          intro k h1 h2
          rw [List.getElem_map, ← getElem!_pos tup k (by simpa using h1), htupget k h2, (hEs k h2).2,
            getElem!_pos cs k h2]
        -- the children's entries have the invariant
        have hinvk : ∀ k (hk : k < cs.length), EntryInv s st s.anodes[j]!.children[k]! (Es k hk) :=
          fun k hk => sptE_inv hs f _ (hinv.children k (hlen ▸ hk)).1 _ (hEs k hk).1
        -- the join exists and ρ is an instance of it
        have hidem : ∀ σ ∈ s.anodes[j]!.sub :: tup.map (·.sub), σ.Idem := by
          intro σ hσ
          rcases List.mem_cons.1 hσ with rfl | hσ
          · exact hinv.idem
          · rw [List.mem_map] at hσ
            obtain ⟨E, hE, rfl⟩ := hσ
            obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hE
            have hk' : k < cs.length := by rw [← htuplen]; exact hk
            rw [← getElem!_pos tup k hk, htupget k hk']
            exact (hinvk k hk').idem
        have habsall : ∀ σ ∈ s.anodes[j]!.sub :: tup.map (·.sub), ρ.comp σ = ρ := by
          intro σ hσ
          rcases List.mem_cons.1 hσ with rfl | hσ
          · exact hab
          · rw [List.mem_map] at hσ
            obtain ⟨E, hE, rfl⟩ := hσ
            obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hE
            have hk' : k < cs.length := by rw [← htuplen]; exact hk
            rw [← getElem!_pos tup k hk, htupget k hk']
            have hmem : cs[k]! ∈ cs := by
              rw [getElem!_pos cs k hk']; exact List.getElem_mem hk'
            have habsk : Absorbs s st ρ (Es k hk').tree := by rw [(hEs k hk').2]; exact hcsabs _ hmem
            exact Subst.comp_eq_of_instance (hinvk k hk').idem
              (entry_mostGeneral hs f _ (hinv.children k (hlen ▸ hk')).1 _ (hEs k hk').1 ρ hρ habsk)
        obtain ⟨θ, hjoin, hinst⟩ := joinAll_mostGeneral U _ ρ hρ hidem habsall
        have hθabs := joinAll_absorbs U _ θ hjoin
        have hρθ : ρ = ρ.comp θ := (Subst.comp_eq_of_instance (joinAll_idem U _ θ hjoin) hinst).symm
        -- the conditions hold under the join
        have hall : ((s.anodes[j]!.conds ++ tup.flatMap (·.conds)).map (Cond.apply θ)).all
            (fun k => decide (k.Holds st.consts)) = true := by
          rw [List.all_eq_true]
          intro c hc
          rw [decide_eq_true_iff]
          rw [List.mem_map] at hc
          obtain ⟨c', hc', rfl⟩ := hc
          rw [List.mem_append] at hc'
          rcases hc' with hc' | hc'
          · refine holds_of_instance hρ hρθ (hconds _ ?_)
            exact List.mem_map_of_mem (by simp only [SptTree.conds, List.mem_append]; exact Or.inl hc')
          · rw [List.mem_flatMap] at hc'
            obtain ⟨E, hE, hcE⟩ := hc'
            obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hE
            have hk' : k < cs.length := by rw [← htuplen]; exact hk
            rw [← getElem!_pos tup k hk, htupget k hk'] at hcE
            rw [(hinvk k hk').conds, List.mem_map] at hcE
            obtain ⟨c'', hc'', rfl⟩ := hcE
            rw [Cond.apply_comp, hθabs _ (by
              rw [List.mem_cons, List.mem_map]
              exact Or.inr ⟨Es k hk', by rw [← htupget k hk', getElem!_pos tup k hk]; exact List.getElem_mem hk, rfl⟩)]
            refine holds_of_instance hρ hρθ (hconds _ ?_)
            refine List.mem_map_of_mem ?_
            simp only [SptTree.conds, List.mem_append]
            refine Or.inr (mem_condsList_of_index s cs k hk' c'' ?_)
            rw [← (hEs k hk').2]
            exact hc''
        let E₀ : Entry :=
          ⟨SptTree.node j (tup.map fun E => E.tree), θ,
            (s.anodes[j]!.conds ++ tup.flatMap fun E => E.conds).map (Cond.apply θ)⟩
        refine ⟨E₀, ?_, by simp only [E₀]; rw [htrees]⟩
        simp only [sptE, List.mem_append, List.mem_flatMap]
        refine Or.inr ⟨j, (mem_aChildren s i j).2 ⟨hj, hp⟩, ?_⟩
        simp only [anodeEntries, List.mem_filterMap]
        refine ⟨tup, htup, ?_⟩
        rw [hjoin]
        simp only [hall, ↓reduceIte]
        rfl

/-! ### Congruence from matching -/

mutual
theorem congruent_of_matches (db : Database) (s : State) (θ : Subst) :
    ∀ {π : PTree} {T : SptTree}, Matches s π T → π.Congruent (proofOf db s θ T)
  | _, _, .leaf h e i => by simp [proofOf, PTree.Congruent]
  | _, _, .node e a θπ cs j ts ha hlen hcs => by
    simp only [proofOf, PTree.Congruent]
    exact ⟨ha.symm, congruentList_of_matches db s θ cs ts hlen hcs⟩
theorem congruentList_of_matches (db : Database) (s : State) (θ : Subst) :
    ∀ (cs : List PTree) (ts : List SptTree), cs.length = ts.length →
      (∀ k, k < cs.length → Matches s cs[k]! ts[k]!) → PTree.CongruentList cs (proofsOf db s θ ts)
  | [], [], _, _ => by simp [proofsOf, PTree.CongruentList]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: cs, t :: ts, h, hk => by
    simp only [proofsOf, PTree.CongruentList]
    exact ⟨congruent_of_matches db s θ (by simpa using hk 0 (by simp)),
      congruentList_of_matches db s θ cs ts (by simpa using h) (fun k hk' => by simpa using hk (k + 1) (by simp; omega))⟩
end

/-! ### Completeness -/

/-- Completeness: after as many rounds as the proof is high, the root has an entry whose
tree the proof follows, and the proof is an instance of the entry's proof. -/
theorem completeness' {U : Unification} {db : Database} (hwf : db.WF) {st : Statement} {σ : Subst}
    (hσ : σ.Typed) {π : PTree} (hπ : IsProof db (st.subst σ) π) :
    ∃ n : ℕ, ∃ E ∈ (run U db st n).rootEntries U st,
      π.Congruent (E.proof db (run U db st n)) ∧ π.IsInstance db (E.proof db (run U db st n)) := by
  refine ⟨π.height + 1, ?_⟩
  have hs := run_inv U db hwf st (π.height + 1)
  have hroot : 0 < (run U db st 0).enodes.size := (init_inv U db st).root_lt
  obtain ⟨hat, hm⟩ := treeOf_at (U := U) hwf (π.height + 1) hπ.1.1 0 0 hroot (by omega) σ hσ
    (by rw [hs.root_expr]; exact hπ.2.1)
  -- the global substitution, as for generality
  have hnd : ((assign π (treeOf (run U db st (π.height + 1)) π 0)).map Prod.fst).Nodup := by
    rw [assign_keys hm]
    exact anodes_nodup hs hat
  have hLtyped : ∀ p ∈ assign π (treeOf (run U db st (π.height + 1)) π 0), p.2.Typed := assign_typed hm hπ.1.1
  have hρ : (build db (run U db st (π.height + 1)) σ (assign π (treeOf (run U db st (π.height + 1)) π 0))).Typed :=
    build_typed db _ hσ _ hLtyped
  have hρσ : ∀ v : Var, v.id < (run U db st (π.height + 1)).freshBase →
      (build db (run U db st (π.height + 1)) σ (assign π (treeOf (run U db st (π.height + 1)) π 0))).f v = σ.f v :=
    fun v hv => build_f_lt db _ σ _ v hv
  have hρa : ∀ (j : ℕ) (θπ : Subst), (j, θπ) ∈ assign π (treeOf (run U db st (π.height + 1)) π 0) →
      ∀ x ∈ nodeBinders db (run U db st (π.height + 1)) j,
      (build db (run U db st (π.height + 1)) σ (assign π (treeOf (run U db st (π.height + 1)) π 0))).f
        (renamed ((run U db st (π.height + 1)).baseOf j) x) = θπ.f x := by
    intro j θπ hL x hx
    have hj : j < (run U db st (π.height + 1)).anodes.size :=
      anodes_lt hat j (by rw [← assign_keys hm]; exact List.mem_map_of_mem (f := Prod.fst) hL)
    obtain ⟨A, hinv⟩ := hs.anodes j hj
    have hxA : x ∈ A.vars := by simpa [nodeBinders, getElem!_of_getElem? hinv.assertion] using hx
    exact build_f_renamed db _ σ _ hnd hs.stride_pos hL hx
      (hs.stride_gt A (List.mem_of_getElem? hinv.assertion) x hxA)
  have hexpr : π.expr = (build db (run U db st (π.height + 1)) σ (assign π (treeOf (run U db st (π.height + 1)) π 0))).apply
      (run U db st (π.height + 1)).enodes[0]!.expr := by
    rw [hs.root_expr, hπ.2.1]
    simp only [Statement.subst]
    symm
    apply apply_congr_vars
    intro v hv
    exact hρσ v (hs.fresh_gt v (Or.inl hv))
  obtain ⟨hπeq, habs⟩ := sim hwf hs _ hρ _ hρσ hρa hat hm hπ.1.1 (fun p hp => hp) hexpr
  -- the conditions hold under the substitution, since the proof is valid
  have hconds : ∀ k ∈ ((treeOf (run U db st (π.height + 1)) π 0).conds (run U db st (π.height + 1))).map
      (Cond.apply (build db (run U db st (π.height + 1)) σ (assign π (treeOf (run U db st (π.height + 1)) π 0)))),
      k.Holds st.consts := by
    intro k hk
    rw [← conds_proofOf hwf hs hat, ← hπeq] at hk
    exact hπ.1.2 k hk
  -- the entry
  obtain ⟨E, hE, hET⟩ := entry_exists hs hat _ hρ habs hconds _ (le_refl _)
  have hEroot : E ∈ (run U db st (π.height + 1)).rootEntries U st := by
    unfold rootEntries
    exact sptE_mono U st _ _ _ (by have := fuel_le hs hat; omega) 0 E hE
  have hat' : E.tree.At (run U db st (π.height + 1)) 0 := by rw [hET]; exact hat
  have habs' : Absorbs (run U db st (π.height + 1)) st
      (build db (run U db st (π.height + 1)) σ (assign π (treeOf (run U db st (π.height + 1)) π 0))) E.tree := by
    rw [hET]; exact habs
  refine ⟨E, hEroot, ?_, ?_⟩
  · rw [Entry.proof, hET]
    exact congruent_of_matches db _ E.sub hm
  · obtain ⟨δ, hδ⟩ := entry_mostGeneral hs _ 0 hs.root_lt E hEroot _ hρ habs'
    refine ⟨δ, ?_⟩
    rw [Entry.proof, proofOf_subst hs _ _ hat', ← hδ, hET]
    exact hπeq

end Theory
