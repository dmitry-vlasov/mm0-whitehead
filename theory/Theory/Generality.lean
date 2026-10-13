/-
Generality (the 2017 paper's Theorem 2, the draft's 4.5): the proof of an entry at the
root is more general than every proof of an instance of the statement congruent to it.

The argument. A proof `π` congruent to the entry's tree `T` gives a substitution `ρ`
on the whole state: the instance's substitution on the statement's variables, and at
the renamed binders of every assertion node of `T` what `π`'s step there gives them.
This is well defined because the nodes of `T` are distinct (their numbering keeps
their variables apart, and a tree never visits a node twice: `anodes_nodup`). Then `ρ`
solves the equation of every node of `T` and every leaf (`sim`), so it absorbs the
tree, so it is an instance of the entry's answer, which is most general among what
absorbs the tree (`entry_mostGeneral`); and `π` is the proof of `T` under `ρ`.
-/
import Theory.General

namespace Theory

open State

/-! ### Lookup in an assignment -/

def look : List (ℕ × Subst) → ℕ → Option Subst
  | [], _ => none
  | (j, θ) :: L, k => if j = k then some θ else look L k

theorem look_mem : ∀ (L : List (ℕ × Subst)) (k : ℕ) (θ : Subst), look L k = some θ → (k, θ) ∈ L
  | [], _, _, h => by simp [look] at h
  | (j, θ') :: L, k, θ, h => by
    simp only [look] at h
    split_ifs at h with hjk
    · subst hjk
      simp only [Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (look_mem L k θ h)

theorem look_of_nodup : ∀ (L : List (ℕ × Subst)), (L.map Prod.fst).Nodup →
    ∀ (k : ℕ) (θ : Subst), (k, θ) ∈ L → look L k = some θ
  | [], _, _, _, h => by simp at h
  | (j, θ') :: L, hnd, k, θ, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [look]
    rcases List.mem_cons.1 h with heq | h
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp
    · have hne : j ≠ k := by
        rintro rfl
        exact hnd.1 (List.mem_map_of_mem (f := Prod.fst) h)
      simp only [hne, ↓reduceIte]
      exact look_of_nodup L hnd.2 k θ h

/-! ### The nodes above a node -/

def anc (s : State) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, e =>
    match up s e with
    | some p => p :: anc s fuel p
    | none => []

/-- The expression nodes above a node, up to the root. -/
def chain (s : State) (e : ℕ) : List ℕ := anc s (e + 1) e

theorem anc_fuel {s : State} (hup : ∀ e p, up s e = some p → p < e) :
    ∀ e fuel, e < fuel → anc s fuel e = chain s e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ n =>
      unfold chain
      cases hu : up s e with
      | none => simp [anc, hu]
      | some p =>
        have hp := hup e p hu
        simp only [anc, hu]
        rw [ih p hp n (by omega), ih p hp e hp]

theorem chain_eq {s : State} (hup : ∀ e p, up s e = some p → p < e) {e p : ℕ} (h : up s e = some p) :
    chain s e = p :: chain s p := by
  have h1 : chain s e = p :: anc s e p := by
    unfold chain
    simp [anc, h]
  rw [h1, anc_fuel hup p e (hup e p h)]

theorem chain_nil {s : State} {e : ℕ} (h : up s e = none) : chain s e = [] := by
  simp [chain, anc, h]

theorem chain_lt {s : State} (hup : ∀ e p, up s e = some p → p < e) : ∀ e, ∀ x ∈ chain s e, x < e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro x hx
    cases hu : up s e with
    | none => rw [chain_nil hu] at hx; simp at hx
    | some p =>
      rw [chain_eq hup hu] at hx
      have hp := hup e p hu
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hp
      · exact lt_trans (ih p hp x hx) hp

theorem chain_suffix {s : State} (hup : ∀ e p, up s e = some p → p < e) :
    ∀ e x, x ∈ e :: chain s e → ∃ L, e :: chain s e = L ++ x :: chain s x := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨[], rfl⟩
    · cases hu : up s e with
      | none => rw [chain_nil hu] at hx; simp at hx
      | some p =>
        rw [chain_eq hup hu] at hx ⊢
        obtain ⟨L, hL⟩ := ih p (hup e p hu) x hx
        exact ⟨e :: L, by rw [List.cons_append, ← hL]⟩

/-! ### The nodes of a tree -/

mutual
/-- The expression nodes at the positions of a tree. -/
def SptTree.enodes (s : State) : SptTree → List ℕ
  | .leaf i _ => [i]
  | .node j cs => s.anodes[j]!.parent :: SptTree.enodesList s cs
def SptTree.enodesList (s : State) : List SptTree → List ℕ
  | [] => []
  | t :: ts => SptTree.enodes s t ++ SptTree.enodesList s ts
end

mutual
/-- The assertion nodes of a tree. -/
def SptTree.anodes : SptTree → List ℕ
  | .leaf _ _ => []
  | .node j cs => j :: SptTree.anodesList cs
def SptTree.anodesList : List SptTree → List ℕ
  | [] => []
  | t :: ts => SptTree.anodes t ++ SptTree.anodesList ts
end

theorem SptTree.enodesList_eq_flatMap (s : State) :
    ∀ cs : List SptTree, SptTree.enodesList s cs = cs.flatMap (SptTree.enodes s)
  | [] => rfl
  | t :: ts => by simp [SptTree.enodesList, enodesList_eq_flatMap s ts]

theorem SptTree.anodesList_eq_flatMap :
    ∀ cs : List SptTree, SptTree.anodesList cs = cs.flatMap SptTree.anodes
  | [] => rfl
  | t :: ts => by simp [SptTree.anodesList, anodesList_eq_flatMap ts]

/-- Every node of a tree at `c` has `c` above it or is it. -/
theorem mem_chain_of_at {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s) :
    ∀ {c : ℕ} {T : SptTree}, T.At s c → ∀ e ∈ T.enodes s, c ∈ e :: chain s e := by
  intro c T hat
  induction hat with
  | leaf i h =>
    intro e he
    simp only [SptTree.enodes, List.mem_singleton] at he
    subst he
    exact List.mem_cons_self
  | node i j cs hj hp hlen hcs ih =>
    intro e he
    simp only [SptTree.enodes, hp, List.mem_cons] at he
    rcases he with rfl | he
    · exact List.mem_cons_self
    · rw [SptTree.enodesList_eq_flatMap, List.mem_flatMap] at he
      obtain ⟨t, ht, het⟩ := he
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
      rw [← getElem!_pos cs k hk] at het
      obtain ⟨L, hL⟩ := chain_suffix hs.up_lt e _ (ih k hk e het)
      have hupc := hs.up_children j hj k (hlen ▸ hk)
      rw [hp] at hupc
      rw [chain_eq hs.up_lt hupc] at hL
      rw [hL]
      simp

theorem parent_mem_enodes {s : State} : ∀ {c : ℕ} {T : SptTree}, T.At s c →
    ∀ j ∈ T.anodes, s.anodes[j]!.parent ∈ T.enodes s := by
  intro c T hat
  induction hat with
  | leaf _ _ => intro j hj; simp [SptTree.anodes] at hj
  | node i j cs hj hp hlen hcs ih =>
    intro j' hj'
    simp only [SptTree.anodes, List.mem_cons] at hj'
    simp only [SptTree.enodes, List.mem_cons]
    rcases hj' with rfl | hj'
    · exact Or.inl rfl
    · rw [SptTree.anodesList_eq_flatMap, List.mem_flatMap] at hj'
      obtain ⟨t, ht, hjt⟩ := hj'
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
      rw [← getElem!_pos cs k hk] at hjt
      refine Or.inr ?_
      rw [SptTree.enodesList_eq_flatMap, List.mem_flatMap]
      exact ⟨cs[k]!, by rw [getElem!_pos cs k hk]; exact List.getElem_mem hk, ih k hk j' hjt⟩

theorem anodes_lt {s : State} : ∀ {c : ℕ} {T : SptTree}, T.At s c → ∀ j ∈ T.anodes, j < s.anodes.size := by
  intro c T hat
  induction hat with
  | leaf _ _ => intro j hj; simp [SptTree.anodes] at hj
  | node i j cs hj hp hlen hcs ih =>
    intro j' hj'
    simp only [SptTree.anodes, List.mem_cons] at hj'
    rcases hj' with rfl | hj'
    · exact hj
    · rw [SptTree.anodesList_eq_flatMap, List.mem_flatMap] at hj'
      obtain ⟨t, ht, hjt⟩ := hj'
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
      rw [← getElem!_pos cs k hk] at hjt
      exact ih k hk j' hjt

theorem le_of_mem_enodes {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    {c : ℕ} {T : SptTree} (hat : T.At s c) : ∀ e ∈ T.enodes s, c ≤ e := by
  intro e he
  rcases List.mem_cons.1 (mem_chain_of_at hs hat e he) with rfl | h
  · exact le_refl _
  · exact le_of_lt (chain_lt hs.up_lt e c h)

/-- Two children's subtrees share no expression node. -/
theorem sibling_disjoint {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s)
    {i j : ℕ} {cs : List SptTree} (hat : SptTree.At s i (.node j cs)) :
    ∀ k k', k < cs.length → k' < cs.length → ∀ e, e ∈ cs[k]!.enodes s → e ∈ cs[k']!.enodes s → k = k' := by
  cases hat with
  | node _ _ _ hj hp hlen hcs =>
    intro k k' hk hk' e he he'
    obtain ⟨L, hL⟩ := chain_suffix hs.up_lt e _ (mem_chain_of_at hs (hcs k hk) e he)
    obtain ⟨L', hL'⟩ := chain_suffix hs.up_lt e _ (mem_chain_of_at hs (hcs k' hk') e he')
    have hu := hs.up_children j hj k (hlen ▸ hk)
    have hu' := hs.up_children j hj k' (hlen ▸ hk')
    rw [chain_eq hs.up_lt hu] at hL
    rw [chain_eq hs.up_lt hu'] at hL'
    have heq := List.append_inj_right' (hL.symm.trans hL') (by simp)
    simp only [List.cons.injEq] at heq
    obtain ⟨A, hinv⟩ := hs.anodes j hj
    obtain ⟨n, _, hch⟩ := hinv.children_eq
    have hkA : k < A.hyps.length := by rw [hch] at hlen; simp at hlen; omega
    have hk'A : k' < A.hyps.length := by rw [hch] at hlen; simp at hlen; omega
    rw [hch, getElem!_map_range _ _ k hkA, getElem!_map_range _ _ k' hk'A] at heq
    omega

theorem nodup_flatMap_index {α β : Type} [Inhabited α] (f : α → List β) :
    ∀ (l : List α), (∀ k, k < l.length → (f l[k]!).Nodup) →
      (∀ k k', k < l.length → k' < l.length → ∀ x, x ∈ f l[k]! → x ∈ f l[k']! → k = k') →
      (l.flatMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h1, h2 => by
    simp only [List.flatMap_cons]
    refine List.Nodup.append (by simpa using h1 0 (by simp)) ?_ ?_
    · refine nodup_flatMap_index f l (fun k hk => by simpa using h1 (k + 1) (by simp; omega)) ?_
      intro k k' hk hk' x hx hx'
      have := h2 (k + 1) (k' + 1) (by simp; omega) (by simp; omega) x (by simpa using hx) (by simpa using hx')
      omega
    · intro x hx hx'
      rw [List.mem_flatMap] at hx'
      obtain ⟨b, hb, hxb⟩ := hx'
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hb
      have := h2 0 (k + 1) (by simp) (by simp; omega) x (by simpa using hx)
        (by simp only [List.getElem!_cons_succ]; rw [getElem!_pos l k hk]; exact hxb)
      omega

/-- A tree never visits an assertion node twice. -/
theorem anodes_nodup {U : Unification} {db : Database} {st : Statement} {s : State} (hs : StateInv U db st s) :
    ∀ {c : ℕ} {T : SptTree}, T.At s c → T.anodes.Nodup := by
  intro c T hat
  induction hat with
  | leaf _ _ => simp [SptTree.anodes]
  | node i j cs hj hp hlen hcs ih =>
    have hat' : SptTree.At s i (.node j cs) := SptTree.At.node i j cs hj hp hlen hcs
    simp only [SptTree.anodes, SptTree.anodesList_eq_flatMap]
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · intro hj'
      rw [List.mem_flatMap] at hj'
      obtain ⟨t, ht, hjt⟩ := hj'
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
      rw [← getElem!_pos cs k hk] at hjt
      have hle := le_of_mem_enodes hs (hcs k hk) _ (parent_mem_enodes (hcs k hk) j hjt)
      rw [hp] at hle
      obtain ⟨A, hinv⟩ := hs.anodes j hj
      obtain ⟨n, hn, hch⟩ := hinv.children_eq
      have hkA : k < A.hyps.length := by rw [hch] at hlen; simp at hlen; omega
      rw [hch, getElem!_map_range _ _ k hkA] at hle
      rw [hp] at hn
      omega
    · exact nodup_flatMap_index _ cs (fun k hk => ih k hk) fun k k' hk hk' x hx hx' =>
        sibling_disjoint hs hat' k k' hk hk' _ (parent_mem_enodes (hcs k hk) x hx)
          (parent_mem_enodes (hcs k' hk') x hx')

/-! ### A proof along a tree -/

/-- A proof follows a tree: the same assertions at the steps, the same hypotheses at
the leaves. -/
inductive Matches (s : State) : PTree → SptTree → Prop
  | leaf (h : ℕ) (e : Exp) (i : ℕ) : Matches s (.hyp h e) (.leaf i h)
  | node (e : Exp) (a : ℕ) (θ : Subst) (cs : List PTree) (j : ℕ) (ts : List SptTree)
      (ha : s.anodes[j]!.assertion = a) (hlen : cs.length = ts.length)
      (hcs : ∀ k, k < cs.length → Matches s cs[k]! ts[k]!) : Matches s (.step e a θ cs) (.node j ts)

mutual
theorem matches_of_congruent (db : Database) (s : State) (θ₀ : Subst) :
    ∀ (T : SptTree) (π : PTree), π.Congruent (proofOf db s θ₀ T) → Matches s π T
  | .leaf i h, .hyp h' e, hc => by
    simp only [proofOf, PTree.Congruent] at hc
    subst hc
    exact Matches.leaf _ _ _
  | .leaf _ _, .step _ _ _ _, hc => by simp [proofOf, PTree.Congruent] at hc
  | .node _ _, .hyp _ _, hc => by simp [proofOf, PTree.Congruent] at hc
  | .node j ts, .step e a θ cs, hc => by
    simp only [proofOf, PTree.Congruent] at hc
    obtain ⟨ha, hcl⟩ := hc
    have := matchesList_of_congruentList db s θ₀ ts cs hcl
    exact Matches.node e a θ cs j ts ha.symm this.1 this.2
theorem matchesList_of_congruentList (db : Database) (s : State) (θ₀ : Subst) :
    ∀ (ts : List SptTree) (cs : List PTree), PTree.CongruentList cs (proofsOf db s θ₀ ts) →
      cs.length = ts.length ∧ ∀ k, k < cs.length → Matches s cs[k]! ts[k]!
  | [], [], _ => ⟨rfl, fun k hk => by simp at hk⟩
  | [], _ :: _, hc => by simp [proofsOf, PTree.CongruentList] at hc
  | _ :: _, [], hc => by simp [proofsOf, PTree.CongruentList] at hc
  | t :: ts, c :: cs, hc => by
    simp only [proofsOf, PTree.CongruentList] at hc
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨hlen, hk⟩ := matchesList_of_congruentList db s θ₀ ts cs h2
    refine ⟨by simp [hlen], ?_⟩
    intro k hk'
    cases k with
    | zero => simpa using matches_of_congruent db s θ₀ t c h1
    | succ k =>
      simp only [List.length_cons] at hk'
      simpa using hk k (by omega)
end

mutual
/-- The step substitutions of a proof along a tree, by assertion node. -/
def assign : PTree → SptTree → List (ℕ × Subst)
  | .step _ _ θ cs, .node j ts => (j, θ) :: assignList cs ts
  | _, _ => []
def assignList : List PTree → List SptTree → List (ℕ × Subst)
  | c :: cs, t :: ts => assign c t ++ assignList cs ts
  | _, _ => []
end

theorem mem_assignList : ∀ (cs : List PTree) (ts : List SptTree), cs.length = ts.length →
    ∀ p, p ∈ assignList cs ts ↔ ∃ k, k < cs.length ∧ p ∈ assign cs[k]! ts[k]!
  | [], [], _, p => by simp [assignList]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: cs, t :: ts, h, p => by
    simp only [assignList, List.mem_append, List.length_cons] at h ⊢
    rw [mem_assignList cs ts (by omega)]
    constructor
    · rintro (hp | ⟨k, hk, hp⟩)
      · exact ⟨0, by omega, by simpa using hp⟩
      · exact ⟨k + 1, by omega, by simpa using hp⟩
    · rintro ⟨k, hk, hp⟩
      cases k with
      | zero => exact Or.inl (by simpa using hp)
      | succ k => exact Or.inr ⟨k, by omega, by simpa using hp⟩

theorem assignList_keys : ∀ (cs : List PTree) (ts : List SptTree), cs.length = ts.length →
    (∀ k, k < cs.length → (assign cs[k]! ts[k]!).map Prod.fst = ts[k]!.anodes) →
    (assignList cs ts).map Prod.fst = SptTree.anodesList ts
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | c :: cs, t :: ts, h, hk => by
    simp only [assignList, SptTree.anodesList, List.map_append]
    have h0 := hk 0 (by simp)
    simp only [List.getElem!_cons_zero] at h0
    rw [h0, assignList_keys cs ts (by simpa using h)
      (fun k hk' => by simpa using hk (k + 1) (by simp; omega))]

theorem assign_keys {s : State} : ∀ {π : PTree} {T : SptTree}, Matches s π T →
    (assign π T).map Prod.fst = T.anodes := by
  intro π T hm
  induction hm with
  | leaf _ _ _ => simp [assign, SptTree.anodes]
  | node e a θ cs j ts ha hlen hcs ih =>
    simp only [assign, SptTree.anodes, List.map_cons, List.cons.injEq, true_and]
    exact assignList_keys cs ts hlen ih

theorem assign_typed {db : Database} {st : Statement} {s : State} :
    ∀ {π : PTree} {T : SptTree}, Matches s π T → Shape db st π → ∀ p ∈ assign π T, p.2.Typed := by
  intro π T hm
  induction hm with
  | leaf _ _ _ => intro _ p hp; simp [assign] at hp
  | node e a θ cs j ts ha hlen hcs ih =>
    intro hsh p hp
    cases hsh with
    | step _ _ _ _ A hA hθ _ _ _ hall =>
      simp only [assign, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hθ
      · rw [mem_assignList cs ts hlen] at hp
        obtain ⟨k, hk, hp⟩ := hp
        exact ih k hk (hall _ (by rw [getElem!_pos cs k hk]; exact List.getElem_mem hk)) p hp

/-! ### The global substitution of a proof -/

/-- The assertion node a variable belongs to, and the binder it renames. -/
def nodeOf (s : State) (v : Var) : ℕ := (v.id - s.freshBase) / s.stride
def binderOf (s : State) (v : Var) : Var := ⟨(v.id - s.freshBase) % s.stride, v.ty⟩

/-- The binders of the assertion of a node. -/
def nodeBinders (db : Database) (s : State) (j : ℕ) : List Var := db.asserts[s.anodes[j]!.assertion]!.vars

def assignCands (db : Database) (s : State) (L : List (ℕ × Subst)) : Finset Var :=
  (L.map fun p => ((nodeBinders db s p.1).map (renamed (s.baseOf p.1))).toFinset).foldr (· ∪ ·) ∅

theorem mem_assignCands (db : Database) (s : State) (L : List (ℕ × Subst)) (v : Var) :
    v ∈ assignCands db s L ↔ ∃ p ∈ L, ∃ x ∈ nodeBinders db s p.1, v = renamed (s.baseOf p.1) x := by
  unfold assignCands
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.foldr_cons, Finset.mem_union, List.mem_toFinset, List.mem_map, ih,
      List.mem_cons]
    aesop

def buildF (db : Database) (s : State) (σ : Subst) (L : List (ℕ × Subst)) (v : Var) : Exp :=
  if v.id < s.freshBase then σ.f v
  else
    match look L (nodeOf s v) with
    | some θπ => if binderOf s v ∈ nodeBinders db s (nodeOf s v) then θπ.f (binderOf s v) else .var v
    | none => .var v

theorem renamed_nodeOf_binderOf (s : State) (v : Var) (hv : s.freshBase ≤ v.id) :
    renamed (s.baseOf (nodeOf s v)) (binderOf s v) = v := by
  obtain ⟨id, ty⟩ := v
  simp only [renamed, baseOf, nodeOf, binderOf, Var.mk.injEq, and_true] at hv ⊢
  have := Nat.div_add_mod' (id - s.freshBase) s.stride
  omega

theorem buildF_eq_var (db : Database) (s : State) (σ : Subst) (L : List (ℕ × Subst)) (v : Var)
    (hv : v ∉ σ.dom ∪ assignCands db s L) : buildF db s σ L v = .var v := by
  rw [Finset.mem_union, not_or] at hv
  by_cases hlt : v.id < s.freshBase
  · simp only [buildF, hlt, ↓reduceIte]
    exact Subst.f_eq_of_not_mem hv.1
  · simp only [buildF, hlt, ↓reduceIte]
    cases hl : look L (nodeOf s v) with
    | none => rfl
    | some θπ =>
      by_cases hb : binderOf s v ∈ nodeBinders db s (nodeOf s v)
      · exfalso
        apply hv.2
        rw [mem_assignCands]
        exact ⟨_, look_mem L _ _ hl, _, hb, (renamed_nodeOf_binderOf s v (by omega)).symm⟩
      · simp [hb]

/-- The substitution of a proof along a tree: the instance's substitution below the
fresh variables, and at the renamed binders of each node of the tree what the step
there gives them. -/
def build (db : Database) (s : State) (σ : Subst) (L : List (ℕ × Subst)) : Subst :=
  Subst.ofFun (σ.dom ∪ assignCands db s L) (buildF db s σ L) (buildF_eq_var db s σ L)

theorem build_f_lt (db : Database) (s : State) (σ : Subst) (L : List (ℕ × Subst)) (v : Var)
    (hv : v.id < s.freshBase) : (build db s σ L).f v = σ.f v := by
  simp [build, Subst.ofFun, buildF, hv]

theorem build_f_renamed (db : Database) (s : State) (σ : Subst) (L : List (ℕ × Subst))
    (hnd : (L.map Prod.fst).Nodup) (hpos : 0 < s.stride) {j : ℕ} {θπ : Subst} (hL : (j, θπ) ∈ L)
    {x : Var} (hx : x ∈ nodeBinders db s j) (hxs : x.id < s.stride) :
    (build db s σ L).f (renamed (s.baseOf j) x) = θπ.f x := by
  have hnode : nodeOf s (renamed (s.baseOf j) x) = j := by
    simp only [nodeOf, renamed, baseOf]
    rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hxs]
    simp
  have hbind : binderOf s (renamed (s.baseOf j) x) = x := by
    simp only [binderOf, renamed, baseOf]
    cases x with
    | mk id ty =>
      simp only [Var.mk.injEq, and_true]
      rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hxs]
  have hge : ¬ (renamed (s.baseOf j) x).id < s.freshBase := by simp only [renamed, baseOf]; omega
  simp only [build, Subst.ofFun, buildF, hge, ↓reduceIte, hnode, hbind, look_of_nodup L hnd j θπ hL, hx]

theorem build_typed (db : Database) (s : State) {σ : Subst} (hσ : σ.Typed) (L : List (ℕ × Subst))
    (hL : ∀ p ∈ L, p.2.Typed) : (build db s σ L).Typed := by
  intro v
  show v.ty.fits (buildF db s σ L v).ty ∧ (v.ty.name = true → (buildF db s σ L v).IsName)
  by_cases hlt : v.id < s.freshBase
  · simp only [buildF, hlt, ↓reduceIte]
    exact hσ v
  · simp only [buildF, hlt, ↓reduceIte]
    cases hl : look L (nodeOf s v) with
    | none => exact ⟨Ty.fits_refl _, fun _ => trivial⟩
    | some θπ =>
      by_cases hb : binderOf s v ∈ nodeBinders db s (nodeOf s v)
      · simp only [hb, ↓reduceIte]
        have := hL _ (look_mem L _ _ hl) (binderOf s v)
        simpa [binderOf] using this
      · simp only [hb, ↓reduceIte]
        exact ⟨Ty.fits_refl _, fun _ => trivial⟩

/-! ### Two lemmas on application -/

mutual
theorem apply_congr_vars {ρ σ : Subst} : ∀ e : Exp, (∀ v ∈ e.vars, ρ.f v = σ.f v) → ρ.apply e = σ.apply e
  | .var v, h => by simp only [Subst.apply_var]; exact h v (by simp [Exp.vars])
  | .const _ _, _ => by simp [Subst.apply]
  | .app _ _ args, h => by
    simp only [Subst.apply]
    congr 1
    exact applyList_congr_vars args (by simpa [Exp.vars] using h)
theorem applyList_congr_vars {ρ σ : Subst} :
    ∀ es : List Exp, (∀ v ∈ Exp.varsList es, ρ.f v = σ.f v) → ρ.applyList es = σ.applyList es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Subst.applyList]
    rw [apply_congr_vars e (fun v hv => h v (by simp [Exp.varsList, hv])),
      applyList_congr_vars es (fun v hv => h v (by simp [Exp.varsList, hv]))]
end

mutual
theorem apply_rename_eq {ρ θ : Subst} {b : ℕ} :
    ∀ q : Exp, (∀ x ∈ q.vars, ρ.f (renamed b x) = θ.f x) → ρ.apply (q.rename b) = θ.apply q
  | .var x, h => by
    simp only [Exp.rename, Subst.apply_var]
    exact h x (by simp [Exp.vars])
  | .const _ _, _ => by simp [Exp.rename, Subst.apply]
  | .app _ _ args, h => by
    simp only [Exp.rename, Subst.apply]
    congr 1
    exact applyList_rename_eq args (by simpa [Exp.vars] using h)
theorem applyList_rename_eq {ρ θ : Subst} {b : ℕ} :
    ∀ es : List Exp, (∀ x ∈ Exp.varsList es, ρ.f (renamed b x) = θ.f x) →
      ρ.applyList (Exp.renameList b es) = θ.applyList es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Exp.renameList, Subst.applyList]
    rw [apply_rename_eq e (fun x hx => h x (by simp [Exp.varsList, hx])),
      applyList_rename_eq es (fun x hx => h x (by simp [Exp.varsList, hx]))]
end

/-! ### The simulation lemma -/

/-- A proof along a tree, under a substitution that is the instance's on the
statement's variables and the steps' on the renamed binders, is the proof of the tree
under that substitution, which absorbs the tree. -/
theorem sim {U : Unification} {db : Database} (hwf : db.WF) {st : Statement} {s : State}
    (hs : StateInv U db st s) {σ : Subst} (ρ : Subst) (hρ : ρ.Typed) (L : List (ℕ × Subst))
    (hρσ : ∀ v : Var, v.id < s.freshBase → ρ.f v = σ.f v)
    (hρa : ∀ (j : ℕ) (θπ : Subst), (j, θπ) ∈ L → ∀ x ∈ nodeBinders db s j,
      ρ.f (renamed (s.baseOf j) x) = θπ.f x) :
    ∀ {i : ℕ} {T : SptTree} {π : PTree}, T.At s i → Matches s π T → Shape db (st.subst σ) π →
      (∀ p ∈ assign π T, p ∈ L) → π.expr = ρ.apply s.enodes[i]!.expr →
      π = proofOf db s ρ T ∧ Absorbs s st ρ T := by
  intro i T π hat
  induction hat generalizing π with
  | leaf i h =>
    intro hm hsh _ hexpr
    cases hm with
    | leaf _ e _ =>
      cases hsh with
      | hyp _ _ hh he =>
        simp only [PTree.expr] at hexpr
        have hh' : h < st.hyps.length := by simpa [Statement.subst] using hh
        refine ⟨by simp [proofOf, hexpr], Absorbs.leaf i h hh' ?_⟩
        rw [← hexpr, he]
        simp only [Statement.subst]
        rw [getElem!_map' _ _ h hh']
        symm
        apply apply_congr_vars
        intro v hv
        exact hρσ v (hs.fresh_gt v (Or.inr ⟨_, by rw [getElem!_pos st.hyps h hh']; exact List.getElem_mem hh', hv⟩))
  | node i j ts hj hp hlen hts ih =>
    intro hm hsh hsub hexpr
    cases hm with
    | node e a θπ cs _ _ ha hlen' hcs =>
      simp only [PTree.expr] at hexpr
      cases hsh with
      | step _ _ _ _ A hA hθ hdom he hcse hall =>
        obtain ⟨A', hinv⟩ := hs.anodes j hj
        have hAA : A' = A := by
          have h1 := hinv.assertion
          rw [ha, hA] at h1
          exact (Option.some.inj h1).symm
        subst hAA
        have hwfA : A'.WF := hwf A' (List.mem_of_getElem? hinv.assertion)
        have hA! : db.asserts[s.anodes[j]!.assertion]! = A' := getElem!_of_getElem? hinv.assertion
        have hbase : s.anodes[j]!.base = s.baseOf j := hs.base_eq j hj
        have hbind : nodeBinders db s j = A'.vars := by simp [nodeBinders, hA!]
        have hjL : (j, θπ) ∈ L := hsub _ (by simp [assign])
        have hren : ∀ q : Exp, q.vars ⊆ A'.vars.toFinset →
            ρ.apply (q.rename s.anodes[j]!.base) = θπ.apply q := by
          intro q hq
          rw [hbase]
          apply apply_rename_eq
          intro x hx
          exact hρa j θπ hjL x (by rw [hbind]; exact List.mem_toFinset.1 (hq hx))
        have hsolve : ρ.apply s.enodes[i]!.expr = ρ.apply (A'.concl.rename s.anodes[j]!.base) := by
          rw [← hexpr, hren A'.concl hwfA.concl_vars]
          exact he
        have habs : ρ.comp s.anodes[j]!.sub = ρ := by
          have hmgu := hinv.is_mgu
          rw [hp] at hmgu
          obtain ⟨θ', hθ', hinst⟩ := U.mostGeneral [(s.enodes[i]!.expr, A'.concl.rename s.anodes[j]!.base)] ρ hρ
            (fun p hp' => by
              rw [List.mem_singleton] at hp'
              subst hp'
              exact hsolve)
          rw [hmgu] at hθ'
          obtain rfl := Option.some.inj hθ'
          exact Subst.comp_eq_of_instance hinv.idem hinst
        have hchild : ∀ k, k < cs.length → cs[k]! = proofOf db s ρ ts[k]! ∧ Absorbs s st ρ ts[k]! := by
          intro k hk
          have hk' : k < ts.length := hlen' ▸ hk
          have hkA : k < A'.hyps.length := by rw [← hinv.children_len, ← hlen]; exact hk'
          refine ih k hk' (hcs k hk) (hall _ (by rw [getElem!_pos cs k hk]; exact List.getElem_mem hk)) ?_ ?_
          · intro p hp'
            exact hsub p (by
              simp only [assign, List.mem_cons]
              exact Or.inr ((mem_assignList cs ts hlen' p).2 ⟨k, hk, hp'⟩))
          · have h1 : cs[k]!.expr = θπ.apply A'.hyps[k]! := by
              rw [← getElem!_map' PTree.expr cs k hk, hcse, getElem!_map' θπ.apply A'.hyps k hkA]
            rw [h1, (hinv.children k (hlen ▸ hk')).2, ← Subst.apply_comp, habs,
              hren _ (hwfA.hyps_vars _ (by rw [getElem!_pos A'.hyps k hkA]; exact List.getElem_mem hkA))]
        refine ⟨?_, Absorbs.node j ts habs ?_⟩
        · simp only [proofOf, hp]
          have hθeq : θπ = stepSub db s.anodes[j]! ρ := by
            apply Subst.ext
            funext x
            by_cases hx : x ∈ A'.vars
            · rw [stepSub_f_of_mem A' hA! hx, ← Subst.apply_comp, habs, Subst.apply_var, hbase]
              exact (hρa j θπ hjL x (hbind ▸ hx)).symm
            · have h1 : (stepSub db s.anodes[j]! ρ).f x = .var x := by
                simp [stepSub, Subst.ofFun, hA!, hx]
              rw [h1]
              exact Subst.f_eq_of_not_mem (fun h => hx (List.mem_toFinset.1 (hdom h)))
          have hcs' : cs = proofsOf db s ρ ts := by
            rw [proofsOf_eq_map]
            apply List.ext_getElem (by simp [hlen'])
            intro n h1 h2
            rw [List.getElem_map, ← getElem!_pos cs n h1, ← getElem!_pos ts n (by simpa using h2)]
            exact (hchild n h1).1
          rw [hexpr, ← ha, hθeq, hcs']
        · intro t ht
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
          rw [← getElem!_pos ts k hk]
          exact (hchild k (hlen' ▸ hk)).2

/-! ### An entry's answer is most general -/

/-- The answer of an entry is most general among the typed substitutions that absorb
its tree. -/
theorem entry_mostGeneral {U : Unification} {db : Database} {st : Statement} {s : State}
    (hs : StateInv U db st s) :
    ∀ (fuel i : ℕ), i < s.enodes.size → ∀ E ∈ sptE U st s fuel i,
      ∀ ρ : Subst, ρ.Typed → Absorbs s st ρ E.tree → ρ.IsInstance E.sub
  | 0, _, _, E, hE => by simp [sptE] at hE
  | fuel + 1, i, hi, E, hE => by
    intro ρ hρ habs
    simp only [sptE, List.mem_append, List.mem_flatMap] at hE
    rcases hE with hE | ⟨j, hj, hE⟩
    · simp only [leafEntries, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff] at hE
      obtain ⟨h, hh, θ, hθ, rfl⟩ := hE
      cases habs with
      | leaf _ _ _ heq =>
        obtain ⟨θ', hθ', hinst⟩ := U.mostGeneral [(s.enodes[i]!.expr, st.hyps[h]!)] ρ hρ (fun p hp => by
          rw [List.mem_singleton] at hp
          subst hp
          exact heq)
        rw [hθ] at hθ'
        obtain rfl := Option.some.inj hθ'
        exact hinst
    · obtain ⟨hj, hp⟩ := (mem_aChildren s i j).1 hj
      simp only [anodeEntries, List.mem_filterMap] at hE
      obtain ⟨tup, htup, hmk⟩ := hE
      obtain ⟨hlen, hk⟩ := mem_tuples _ tup htup
      split at hmk
      · exact absurd hmk (by simp)
      · rename_i θ hjoin
        split at hmk
        · simp only [Option.some.injEq] at hmk
          subst hmk
          cases habs with
          | node _ _ hab hcs =>
            obtain ⟨A, hinv⟩ := hs.anodes j hj
            simp only [List.length_map] at hlen
            have hmemk : ∀ k, k < tup.length →
                tup[k]! ∈ sptE U st s fuel s.anodes[j]!.children[k]! := by
              intro k hk'
              have := hk k (by simpa [hlen] using hk')
              rwa [getElem!_map _ _ k (by rw [← hlen]; exact hk')] at this
            have hinst : ∀ e ∈ tup, ρ.comp e.sub = ρ := by
              intro e he
              obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 he
              have hck : s.anodes[j]!.children[k]! < s.enodes.size :=
                (hinv.children k (by rw [← hlen]; exact hk')).1
              have hEk := hmemk k hk'
              rw [getElem!_pos tup k hk'] at hEk
              have hinvk := sptE_inv hs fuel _ hck _ hEk
              have habs_k : Absorbs s st ρ tup[k].tree :=
                hcs _ (List.mem_map_of_mem (f := fun x => x.tree) (List.getElem_mem hk'))
              exact Subst.comp_eq_of_instance hinvk.idem (entry_mostGeneral hs fuel _ hck _ hEk ρ hρ habs_k)
            have hidem : ∀ σ ∈ s.anodes[j]!.sub :: tup.map (·.sub), σ.Idem := by
              intro σ hσ
              rcases List.mem_cons.1 hσ with rfl | hσ
              · exact hinv.idem
              · rw [List.mem_map] at hσ
                obtain ⟨e, he, rfl⟩ := hσ
                obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.1 he
                have hck : s.anodes[j]!.children[k]! < s.enodes.size :=
                  (hinv.children k (by rw [← hlen]; exact hk')).1
                have hEk := hmemk k hk'
                rw [getElem!_pos tup k hk'] at hEk
                exact (sptE_inv hs fuel _ hck _ hEk).idem
            have habsall : ∀ σ ∈ s.anodes[j]!.sub :: tup.map (·.sub), ρ.comp σ = ρ := by
              intro σ hσ
              rcases List.mem_cons.1 hσ with rfl | hσ
              · exact hab
              · rw [List.mem_map] at hσ
                obtain ⟨e, he, rfl⟩ := hσ
                exact hinst e he
            obtain ⟨θ', hθ', hρθ⟩ := joinAll_mostGeneral U _ ρ hρ hidem habsall
            rw [hjoin] at hθ'
            obtain rfl := Option.some.inj hθ'
            exact hρθ
        · exact absurd hmk (by simp)

/-! ### Generality -/

theorem generality' {U : Unification} {db : Database} (hwf : db.WF) {st : Statement} (n : ℕ) :
    ∀ E ∈ (run U db st n).rootEntries U st, ∀ (σ : Subst), σ.Typed → ∀ (π : PTree),
      IsProof db (st.subst σ) π → π.Congruent (E.proof db (run U db st n)) →
      π.IsInstance db (E.proof db (run U db st n)) := by
  intro E hE σ hσ π hπ hcong
  have hs := run_inv U db st n
  have hEinv := sptE_inv hs _ 0 hs.root_lt E hE
  have hm : Matches (run U db st n) π E.tree := matches_of_congruent db (run U db st n) E.sub E.tree π hcong
  have hnd : ((assign π E.tree).map Prod.fst).Nodup := by
    rw [assign_keys hm]
    exact anodes_nodup hs hEinv.at_
  have hLtyped : ∀ p ∈ assign π E.tree, p.2.Typed := assign_typed hm hπ.1.1
  have hρ : (build db (run U db st n) σ (assign π E.tree)).Typed := build_typed db (run U db st n) hσ _ hLtyped
  have hρσ : ∀ v : Var, v.id < (run U db st n).freshBase → (build db (run U db st n) σ (assign π E.tree)).f v = σ.f v :=
    fun v hv => build_f_lt db (run U db st n) σ _ v hv
  have hρa : ∀ (j : ℕ) (θπ : Subst), (j, θπ) ∈ assign π E.tree → ∀ x ∈ nodeBinders db (run U db st n) j,
      (build db (run U db st n) σ (assign π E.tree)).f (renamed ((run U db st n).baseOf j) x) = θπ.f x := by
    intro j θπ hL x hx
    have hj : j < (run U db st n).anodes.size :=
      anodes_lt hEinv.at_ j (by rw [← assign_keys hm]; exact List.mem_map_of_mem (f := Prod.fst) hL)
    obtain ⟨A, hinv⟩ := hs.anodes j hj
    have hxA : x ∈ A.vars := by simpa [nodeBinders, getElem!_of_getElem? hinv.assertion] using hx
    exact build_f_renamed db (run U db st n) σ _ hnd hs.stride_pos hL hx
      (hs.stride_gt A (List.mem_of_getElem? hinv.assertion) x hxA)
  have hexpr : π.expr = (build db (run U db st n) σ (assign π E.tree)).apply (run U db st n).enodes[0]!.expr := by
    rw [hs.root_expr, hπ.2.1]
    simp only [Statement.subst]
    symm
    apply apply_congr_vars
    intro v hv
    exact hρσ v (hs.fresh_gt v (Or.inl hv))
  obtain ⟨hπeq, habs⟩ := sim hwf hs (build db (run U db st n) σ (assign π E.tree)) hρ (assign π E.tree) hρσ hρa hEinv.at_ hm hπ.1.1 (fun p hp => hp) hexpr
  obtain ⟨δ, hδ⟩ := entry_mostGeneral hs _ 0 hs.root_lt E hE (build db (run U db st n) σ (assign π E.tree)) hρ habs
  refine ⟨δ, ?_⟩
  rw [Entry.proof, proofOf_subst hs _ _ hEinv.at_, ← hδ]
  exact hπeq

end Theory
