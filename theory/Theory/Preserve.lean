/-
The engine keeps the invariants of `Spt.lean`: a state made by `run` satisfies
`StateInv`, and every entry of its SPT sets satisfies `EntryInv`. With `valid_of_inv`
this gives `soundness_valid`.
-/
import Theory.Spt

namespace Theory

open State

/-! ### Folds -/

theorem foldl_inv {α β : Type} (P : α → Prop) (f : α → β → α) (l : List β)
    (h : ∀ a, ∀ b ∈ l, P a → P (f a b)) : ∀ a, P a → P (l.foldl f a) := by
  induction l with
  | nil => intro a ha; exact ha
  | cons b l ih =>
    intro a ha
    exact ih (fun a b hb => h a b (List.mem_cons_of_mem _ hb)) _ (h a b List.mem_cons_self ha)

theorem getElem!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (k : ℕ)
    (hk : k < l.length) : (l.map f)[k]! = f l[k]! := by
  rw [getElem!_pos (l.map f) k (by simp [hk]), getElem!_pos l k hk]
  simp

theorem getElem!_map_range {α : Type} [Inhabited α] (f : ℕ → α) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f)[k]! = f k := by
  rw [getElem!_pos ((List.range n).map f) k (by simp [hk])]
  simp

/-! ### What a change of state keeps -/

/-- An assertion node's invariant moves to a state with the same expression nodes
where it looks, and no fewer. -/
theorem ANodeInv.mono {db : Database} {s s' : State} {a : ANode} {A : Assertion} (h : ANodeInv db s a A)
    (hsize : s.enodes.size ≤ s'.enodes.size)
    (hsame : ∀ k, k < s.enodes.size → s'.enodes[k]!.expr = s.enodes[k]!.expr) :
    ANodeInv db s' a A where
  parent_lt := lt_of_lt_of_le h.parent_lt hsize
  assertion := h.assertion
  typed := h.typed
  unifies := by rw [hsame _ h.parent_lt]; exact h.unifies
  children_len := h.children_len
  children := fun k hk =>
    ⟨lt_of_lt_of_le (h.children k hk).1 hsize, by rw [hsame _ (h.children k hk).1]; exact (h.children k hk).2⟩
  conds := h.conds

theorem StateInv.mono {db : Database} {st : Statement} {s s' : State} (h : StateInv db st s)
    (hsize : s.enodes.size ≤ s'.enodes.size)
    (hsame : ∀ k, k < s.enodes.size → s'.enodes[k]!.expr = s.enodes[k]!.expr)
    (hanodes : s'.anodes = s.anodes) : StateInv db st s' where
  root_lt := lt_of_lt_of_le h.root_lt hsize
  root_expr := by rw [hsame 0 h.root_lt]; exact h.root_expr
  anodes := fun j hj => by
    rw [hanodes] at hj ⊢
    obtain ⟨A, hA⟩ := h.anodes j hj
    exact ⟨A, hA.mono hsize hsame⟩

/-- Marking a node expanded changes no expression. -/
theorem expr_modify (s : State) (i k : ℕ) :
    (s.enodes.modify i fun n => { n with expanded := true })[k]!.expr = s.enodes[k]!.expr := by
  by_cases hk : k < s.enodes.size
  · have hk' : k < (s.enodes.modify i fun n => { n with expanded := true }).size := by simpa using hk
    rw [getElem!_pos _ k hk', getElem!_pos _ k hk]
    by_cases hik : i = k
    · subst hik
      rw [Array.getElem_modify_self]
    · rw [Array.getElem_modify_of_ne hik]
  · have hk' : ¬ k < (s.enodes.modify i fun n => { n with expanded := true }).size := by simpa using hk
    rw [getElem!_neg _ k hk', getElem!_neg _ k hk]

/-! ### `addNode` -/

theorem addNode_enodes_size (i a : ℕ) (s : State) (A : Assertion) (θ : Subst) :
    (addNode i a s A θ).enodes.size = s.enodes.size + A.hyps.length := by
  simp [addNode, newENodes]

theorem addNode_anodes_size (i a : ℕ) (s : State) (A : Assertion) (θ : Subst) :
    (addNode i a s A θ).anodes.size = s.anodes.size + 1 := by
  simp [addNode]

theorem addNode_enode_old (i a : ℕ) (s : State) (A : Assertion) (θ : Subst) (k : ℕ) (hk : k < s.enodes.size) :
    (addNode i a s A θ).enodes[k]! = s.enodes[k]! := by
  have hk' : k < (addNode i a s A θ).enodes.size := by rw [addNode_enodes_size]; omega
  rw [getElem!_pos _ k hk', getElem!_pos _ k hk]
  simp only [addNode]
  rw [Array.getElem_append_left hk]

theorem addNode_enode_new (i a : ℕ) (s : State) (A : Assertion) (θ : Subst) (k : ℕ) (hk : k < A.hyps.length) :
    (addNode i a s A θ).enodes[s.enodes.size + k]!.expr =
      θ.apply (A.hyps[k]!.rename (s.baseOf s.anodes.size)) := by
  have hk' : s.enodes.size + k < (addNode i a s A θ).enodes.size := by rw [addNode_enodes_size]; omega
  rw [getElem!_pos (addNode i a s A θ).enodes (s.enodes.size + k) hk']
  simp only [addNode]
  rw [Array.getElem_append_right (by omega)]
  simp [newENodes, Nat.add_sub_cancel_left]

theorem addNode_anode_old (i a : ℕ) (s : State) (A : Assertion) (θ : Subst) (j : ℕ) (hj : j < s.anodes.size) :
    (addNode i a s A θ).anodes[j]! = s.anodes[j]! := by
  have hj' : j < (addNode i a s A θ).anodes.size := by rw [addNode_anodes_size]; omega
  rw [getElem!_pos _ j hj', getElem!_pos _ j hj]
  simp only [addNode]
  rw [Array.getElem_push_lt hj]

theorem addNode_anode_new (i a : ℕ) (s : State) (A : Assertion) (θ : Subst) :
    (addNode i a s A θ).anodes[s.anodes.size]! =
      { parent := i, assertion := a, base := s.baseOf s.anodes.size, sub := θ,
        children := (List.range A.hyps.length).map (s.enodes.size + ·),
        conds := nodeConds A (s.baseOf s.anodes.size) θ } := by
  have hj' : s.anodes.size < (addNode i a s A θ).anodes.size := by rw [addNode_anodes_size]; omega
  rw [getElem!_pos (addNode i a s A θ).anodes s.anodes.size hj']
  simp [addNode]

/-- The new assertion node has its invariant, when it unifies. -/
theorem addNode_inv {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv db st s)
    {i a : ℕ} (hi : i < s.enodes.size) {A : Assertion} (hA : db.asserts[a]? = some A) {θ : Subst}
    (hθ : U.mgu [(s.enodes[i]!.expr, A.concl.rename (s.baseOf s.anodes.size))] = some θ) :
    StateInv db st (addNode i a s A θ) := by
  have hsize : s.enodes.size ≤ (addNode i a s A θ).enodes.size := by rw [addNode_enodes_size]; omega
  have hsame : ∀ k, k < s.enodes.size → (addNode i a s A θ).enodes[k]!.expr = s.enodes[k]!.expr :=
    fun k hk => by rw [addNode_enode_old _ _ _ _ _ k hk]
  refine ⟨lt_of_lt_of_le hs.root_lt hsize, by rw [hsame 0 hs.root_lt]; exact hs.root_expr, ?_⟩
  intro j hj
  rw [addNode_anodes_size] at hj
  by_cases hjs : j < s.anodes.size
  · rw [addNode_anode_old _ _ _ _ _ j hjs]
    obtain ⟨A', hA'⟩ := hs.anodes j hjs
    exact ⟨A', hA'.mono hsize hsame⟩
  · have hj' : j = s.anodes.size := by omega
    subst hj'
    rw [addNode_anode_new]
    refine ⟨A, ?_⟩
    have hsolves := U.solves _ _ hθ (s.enodes[i]!.expr, A.concl.rename (s.baseOf s.anodes.size))
      (List.mem_singleton_self _)
    exact {
      parent_lt := lt_of_lt_of_le hi hsize
      assertion := hA
      typed := U.typed _ _ hθ
      unifies := by simp only; rw [hsame i hi]; exact hsolves
      children_len := by simp
      children := fun k hk => by
        simp only [List.length_map, List.length_range] at hk
        rw [getElem!_map_range _ _ k hk]
        exact ⟨by rw [addNode_enodes_size]; omega, addNode_enode_new i a s A θ k hk⟩
      conds := rfl }

theorem tryAssertion_cases (U : Unification) (db : Database) (i a : ℕ) (s : State) :
    tryAssertion U db i a s = s ∨
      ∃ A θ, db.asserts[a]? = some A ∧
        U.mgu [(s.enodes[i]!.expr, A.concl.rename (s.baseOf s.anodes.size))] = some θ ∧
        tryAssertion U db i a s = addNode i a s A θ := by
  unfold tryAssertion
  split
  · left; rfl
  · split
    · left; rfl
    · right; exact ⟨_, _, by assumption, by assumption, rfl⟩

theorem size_le_tryAssertion (U : Unification) (db : Database) (i a : ℕ) (s : State) :
    s.enodes.size ≤ (tryAssertion U db i a s).enodes.size := by
  rcases tryAssertion_cases U db i a s with h | ⟨A, θ, _, _, h⟩
  · rw [h]
  · rw [h, addNode_enodes_size]; omega

theorem tryAssertion_inv {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv db st s)
    {i : ℕ} (hi : i < s.enodes.size) (a : ℕ) : StateInv db st (tryAssertion U db i a s) := by
  rcases tryAssertion_cases U db i a s with h | ⟨A, θ, hA, hθ, h⟩
  · rw [h]; exact hs
  · rw [h]; exact addNode_inv hs hi hA hθ

/-! ### Expansion -/

theorem expandNode_inv {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv db st s)
    {i : ℕ} (hi : i < s.enodes.size) :
    StateInv db st (expandNode U db i s) ∧ s.enodes.size ≤ (expandNode U db i s).enodes.size := by
  unfold expandNode
  let s₁ : State := { s with enodes := s.enodes.modify i fun n => { n with expanded := true } }
  have hs₁ : StateInv db st s₁ :=
    hs.mono (by simp [s₁]) (fun k _ => expr_modify s i k) rfl
  have hi₁ : i < s₁.enodes.size := by simpa [s₁] using hi
  have := foldl_inv (fun t : State => StateInv db st t ∧ s₁.enodes.size ≤ t.enodes.size)
    (fun t a => tryAssertion U db i a t) (List.range db.asserts.length)
    (fun t a _ ⟨ht, hle⟩ => ⟨tryAssertion_inv ht (lt_of_lt_of_le hi₁ hle) a,
      le_trans hle (size_le_tryAssertion U db i a t)⟩) s₁ ⟨hs₁, le_refl _⟩
  exact ⟨this.1, by simpa [s₁] using this.2⟩

theorem expandAll_inv {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv db st s) :
    StateInv db st (expandAll U db s) := by
  unfold expandAll
  have := foldl_inv (fun t : State => StateInv db st t ∧ s.enodes.size ≤ t.enodes.size)
    (fun t i => expandNode U db i t) ((List.range s.enodes.size).filter fun i => !s.enodes[i]!.expanded)
    (fun t i hi ⟨ht, hle⟩ => by
      have hi' : i < s.enodes.size := List.mem_range.1 (List.mem_of_mem_filter hi)
      obtain ⟨h1, h2⟩ := expandNode_inv ht (lt_of_lt_of_le hi' hle)
      exact ⟨h1, le_trans hle h2⟩) s ⟨hs, le_refl _⟩
  exact this.1

theorem init_inv (db : Database) (st : Statement) : StateInv db st (init db st) where
  root_lt := by simp [init]
  root_expr := by simp [init]
  anodes := fun j hj => by simp [init] at hj

theorem run_inv (U : Unification) (db : Database) (st : Statement) : ∀ n, StateInv db st (run U db st n)
  | 0 => init_inv db st
  | n + 1 => expandAll_inv (run_inv U db st n)

/-! ### The entries -/

theorem mem_tuples : ∀ (ls : List (List Entry)) (tup : List Entry), tup ∈ tuples ls →
    tup.length = ls.length ∧ ∀ k, k < ls.length → tup[k]! ∈ ls[k]!
  | [], tup, h => by
    simp only [tuples, List.mem_singleton] at h
    subst h
    exact ⟨rfl, fun k hk => by simp at hk⟩
  | l :: ls, tup, h => by
    simp only [tuples, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, hx, t, ht, rfl⟩ := h
    obtain ⟨hlen, hk⟩ := mem_tuples ls t ht
    refine ⟨by simp [hlen], ?_⟩
    intro k hk'
    cases k with
    | zero => simpa using hx
    | succ k =>
      simp only [List.length_cons] at hk'
      have := hk k (by omega)
      simpa using this

theorem mem_aChildren (s : State) (i j : ℕ) : j ∈ aChildren s i ↔ j < s.anodes.size ∧ s.anodes[j]!.parent = i := by
  simp [aChildren, List.mem_filter, List.mem_range]

theorem Cond.apply_comp (θ σ : Subst) (k : Cond) : Cond.apply θ (Cond.apply σ k) = Cond.apply (θ.comp σ) k := by
  simp [Cond.apply, Subst.apply_comp]

/-- An entry of an assertion node's set has the invariant, when its children's do. -/
theorem anodeEntries_inv {U : Unification} {st : Statement} {s : State}
    {i j : ℕ} (hj : j < s.anodes.size) (hp : s.anodes[j]!.parent = i)
    {sets : List (List Entry)} (hsets : sets.length = s.anodes[j]!.children.length)
    (hinv : ∀ k, k < sets.length → ∀ E ∈ sets[k]!, EntryInv s st (s.anodes[j]!.children[k]!) E) :
    ∀ E ∈ anodeEntries U st.consts j s.anodes[j]! sets, EntryInv s st i E := by
  intro E hE
  simp only [anodeEntries, List.mem_filterMap] at hE
  obtain ⟨tup, htup, hmk⟩ := hE
  obtain ⟨hlen, hk⟩ := mem_tuples sets tup htup
  split at hmk
  · exact absurd hmk (by simp)
  · rename_i θ hjoin
    split at hmk
    · rename_i hall
      simp only [Option.some.injEq] at hmk
      subst hmk
      have habs := joinAll_absorbs U _ θ hjoin
      have hself : θ.comp s.anodes[j]!.sub = θ := habs _ List.mem_cons_self
      have hmem : ∀ k, k < tup.length → EntryInv s st (s.anodes[j]!.children[k]!) tup[k]! :=
        fun k hk' => hinv k (hlen ▸ hk') _ (hk k (hlen ▸ hk'))
      have htupabs : ∀ e ∈ tup, θ.comp e.sub = θ :=
        fun e he => habs _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
      refine {
        at_ := ?_
        absorbs := ?_
        typed := joinAll_typed U _ θ hjoin
        conds := ?_
        holds := ?_ }
      · refine SptTree.At.node i j _ hj hp (by simp [hlen, hsets]) ?_
        intro k hk'
        simp only [List.length_map] at hk'
        rw [getElem!_map _ tup k hk']
        exact (hmem k hk').at_
      · refine Absorbs.node j _ hself ?_
        intro c hc
        rw [List.mem_map] at hc
        obtain ⟨e, he, rfl⟩ := hc
        obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 he
        rw [← getElem!_pos tup k hk']
        exact (hmem k hk').absorbs.of_comp (htupabs _ (by rw [getElem!_pos tup k hk']; exact List.getElem_mem hk'))
      · simp only [SptTree.conds, SptTree.condsList_eq_flatMap, List.map_append, List.flatMap_map]
        congr 1
        rw [List.map_flatMap, List.map_flatMap]
        apply flatMap_congr_mem
        intro e he
        obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 he
        have hinvk := hmem k hk'
        rw [getElem!_pos tup k hk'] at hinvk
        rw [hinvk.conds, List.map_map]
        apply List.map_congr_left
        intro c _
        simp only [Function.comp]
        rw [Cond.apply_comp, htupabs _ he]
      · intro k hk
        have := List.all_eq_true.1 hall k hk
        exact of_decide_eq_true this
    · exact absurd hmk (by simp)

/-- Every entry of the SPT set of an expression node has the invariant, at any depth. -/
theorem sptE_inv {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv db st s) :
    ∀ (fuel i : ℕ), i < s.enodes.size → ∀ E ∈ sptE U st s fuel i, EntryInv s st i E
  | 0, _, _, _, hE => by simp [sptE] at hE
  | fuel + 1, i, hi, E, hE => by
    simp only [sptE, List.mem_append, List.mem_flatMap] at hE
    rcases hE with hE | ⟨j, hj, hE⟩
    · simp only [leafEntries, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hE
      obtain ⟨h, hh, θ, hθ, rfl⟩ := hE
      exact {
        at_ := SptTree.At.leaf i h
        absorbs := Absorbs.leaf i h hh (U.solves _ _ hθ _ (List.mem_singleton_self _))
        typed := U.typed _ _ hθ
        conds := rfl
        holds := fun k hk => by simp at hk }
    · obtain ⟨hj, hp⟩ := (mem_aChildren s i j).1 hj
      refine anodeEntries_inv hj hp (by simp) ?_ E hE
      intro k hk E' hE'
      obtain ⟨A, hA⟩ := hs.anodes j hj
      simp only [List.length_map] at hk
      rw [getElem!_map _ _ k hk] at hE'
      exact sptE_inv (U := U) hs fuel _ (hA.children k hk).1 E' hE'

end Theory
