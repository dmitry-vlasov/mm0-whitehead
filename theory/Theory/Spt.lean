/-
The substitution proof trees of the reference engine and what they stand for: the
invariants of a state and of an entry, and the theorem that an entry with them gives a
valid proof (`valid_of_inv`), which is the argument of the 2017 paper's Theorem 1. That
the engine keeps the invariants is `Preserve.lean`.
-/
import Theory.Search

namespace Theory

open State

/-! ### Absorption -/

/-- `θ` solves the equational form of `σ` exactly when `θ` absorbs `σ`: `θ ∘ σ = θ`. -/
theorem Subst.solves_eqs_iff (θ σ : Subst) : Solves θ σ.eqs ↔ θ.comp σ = θ := by
  constructor
  · intro h
    apply Subst.ext
    funext v
    show θ.apply (σ.f v) = θ.f v
    by_cases hv : v ∈ σ.dom
    · have hmem : (Exp.var v, σ.f v) ∈ σ.eqs := by
        simp only [Subst.eqs, List.mem_map, Finset.mem_sort]
        exact ⟨v, hv, rfl⟩
      have := h _ hmem
      simp only [Subst.apply_var] at this
      exact this.symm
    · rw [Subst.f_eq_of_not_mem hv, Subst.apply_var]
  · intro h p hp
    simp only [Subst.eqs, List.mem_map, Finset.mem_sort] at hp
    obtain ⟨v, _, rfl⟩ := hp
    simp only [Subst.apply_var]
    have := congrArg (fun τ => τ.f v) h
    exact this.symm

/-- The join of a list of substitutions absorbs each of them. -/
theorem joinAll_absorbs (U : Unification) :
    ∀ (θs : List Subst) (θ : Subst), U.joinAll θs = some θ → ∀ σ ∈ θs, θ.comp σ = θ
  | [], _, _, σ, hσ => by simp at hσ
  | σ₀ :: θs, θ, h, σ, hσ => by
    simp only [Unification.joinAll, Option.bind_eq_some_iff] at h
    obtain ⟨η, hη, hjoin⟩ := h
    have hsolves := U.solves _ _ hjoin
    have h0 : θ.comp σ₀ = θ :=
      (Subst.solves_eqs_iff θ σ₀).1 fun p hp => hsolves p (List.mem_append_left _ hp)
    have hη' : θ.comp η = θ :=
      (Subst.solves_eqs_iff θ η).1 fun p hp => hsolves p (List.mem_append_right _ hp)
    rcases List.mem_cons.1 hσ with rfl | hσ
    · exact h0
    · have hrec := joinAll_absorbs U θs η hη σ hσ
      calc θ.comp σ = (θ.comp η).comp σ := by rw [hη']
        _ = θ.comp (η.comp σ) := Subst.comp_assoc _ _ _
        _ = θ.comp η := by rw [hrec]
        _ = θ := hη'

theorem joinAll_typed (U : Unification) :
    ∀ (θs : List Subst) (θ : Subst), U.joinAll θs = some θ → θ.Typed
  | [], θ, h => by
    simp only [Unification.joinAll, Option.some.injEq] at h
    subst h
    exact Subst.Typed.id
  | _ :: _, θ, h => by
    simp only [Unification.joinAll, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, hjoin⟩ := h
    exact U.typed _ _ hjoin

/-! ### The invariants -/

/-- The tree of an entry sits at expression node `i` of the state: its nodes are
nodes of the state, at the right places. -/
inductive SptTree.At (s : State) : ℕ → SptTree → Prop
  | leaf (i h : ℕ) (hi : i < s.enodes.size) : SptTree.At s i (.leaf i h)
  | node (i j : ℕ) (cs : List SptTree) (hj : j < s.anodes.size) (hp : s.anodes[j]!.parent = i)
      (hlen : cs.length = s.anodes[j]!.children.length)
      (hcs : ∀ k, k < cs.length → SptTree.At s (s.anodes[j]!.children[k]!) cs[k]!) :
      SptTree.At s i (.node j cs)

/-- The answer `θ` absorbs the tree: it absorbs the unifier of every assertion node on
it, and makes every leaf's expression the hypothesis it is closed by. -/
inductive Absorbs (s : State) (st : Statement) (θ : Subst) : SptTree → Prop
  | leaf (i h : ℕ) (hh : h < st.hyps.length) (heq : θ.apply s.enodes[i]!.expr = θ.apply st.hyps[h]!) :
      Absorbs s st θ (.leaf i h)
  | node (j : ℕ) (cs : List SptTree) (habs : θ.comp s.anodes[j]!.sub = θ)
      (hcs : ∀ c ∈ cs, Absorbs s st θ c) :
      Absorbs s st θ (.node j cs)

/-- An answer that absorbs another's answer absorbs its tree. -/
theorem Absorbs.of_comp {s : State} {st : Statement} {σ : Subst} {T : SptTree} (h : Absorbs s st σ T)
    {θ : Subst} (hθ : θ.comp σ = θ) : Absorbs s st θ T := by
  induction h with
  | leaf i h hh heq =>
    refine Absorbs.leaf i h hh ?_
    calc θ.apply s.enodes[i]!.expr = (θ.comp σ).apply s.enodes[i]!.expr := by rw [hθ]
      _ = θ.apply (σ.apply s.enodes[i]!.expr) := Subst.apply_comp _ _ _
      _ = θ.apply (σ.apply st.hyps[h]!) := by rw [heq]
      _ = (θ.comp σ).apply st.hyps[h]! := (Subst.apply_comp _ _ _).symm
      _ = θ.apply st.hyps[h]! := by rw [hθ]
  | node j cs habs _ ih =>
    refine Absorbs.node j cs ?_ ih
    calc θ.comp s.anodes[j]!.sub = (θ.comp σ).comp s.anodes[j]!.sub := by rw [hθ]
      _ = θ.comp (σ.comp s.anodes[j]!.sub) := Subst.comp_assoc _ _ _
      _ = θ.comp σ := by rw [habs]
      _ = θ := hθ

mutual
/-- The conditions of a tree: of every assertion node on it, under its own unifier. -/
def SptTree.conds (s : State) : SptTree → List Cond
  | .leaf _ _ => []
  | .node j cs => s.anodes[j]!.conds ++ SptTree.condsList s cs
def SptTree.condsList (s : State) : List SptTree → List Cond
  | [] => []
  | t :: ts => SptTree.conds s t ++ SptTree.condsList s ts
end

theorem SptTree.condsList_eq_flatMap (s : State) :
    ∀ cs : List SptTree, SptTree.condsList s cs = cs.flatMap (SptTree.conds s)
  | [] => rfl
  | t :: ts => by simp [SptTree.condsList, condsList_eq_flatMap s ts]

theorem joinAll_idem (U : Unification) :
    ∀ (θs : List Subst) (θ : Subst), U.joinAll θs = some θ → θ.Idem
  | [], θ, h => by
    simp only [Unification.joinAll, Option.some.injEq] at h
    subst h
    exact Subst.comp_id _
  | _ :: _, θ, h => by
    simp only [Unification.joinAll, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, hjoin⟩ := h
    exact U.idem _ _ hjoin

/-- The invariant of an entry at expression node `i`. -/
structure EntryInv (s : State) (st : Statement) (i : ℕ) (E : Entry) : Prop where
  at_ : E.tree.At s i
  absorbs : Absorbs s st E.sub E.tree
  typed : E.sub.Typed
  idem : E.sub.Idem
  conds : E.conds = (E.tree.conds s).map (Cond.apply E.sub)
  holds : ∀ k ∈ E.conds, k.Holds st.consts

/-- The invariant of an assertion node, for its assertion `A`: as `tryAssertion` makes
it. -/
structure ANodeInv (U : Unification) (db : Database) (s : State) (a : ANode) (A : Assertion) : Prop where
  parent_lt : a.parent < s.enodes.size
  assertion : db.asserts[a.assertion]? = some A
  typed : a.sub.Typed
  idem : a.sub.Idem
  /-- The unifier is the one the postulate gives for the node's equation. -/
  is_mgu : U.mgu [(s.enodes[a.parent]!.expr, A.concl.rename a.base)] = some a.sub
  unifies : a.sub.apply s.enodes[a.parent]!.expr = a.sub.apply (A.concl.rename a.base)
  children_len : a.children.length = A.hyps.length
  children : ∀ k, k < a.children.length →
    a.children[k]! < s.enodes.size ∧ s.enodes[a.children[k]!]!.expr = a.sub.apply (A.hyps[k]!.rename a.base)
  /-- The children are a block of expression nodes made after the parent. -/
  children_eq : ∃ n, a.parent < n ∧ a.children = (List.range A.hyps.length).map (n + ·)
  /-- The parent's expression is below the node's variables. -/
  parent_vars_lt : ∀ v ∈ s.enodes[a.parent]!.expr.vars, v.id < a.base
  conds : a.conds = nodeConds A a.base a.sub

/-- The expression node above an expression node, through its parent assertion node. -/
def up (s : State) (e : ℕ) : Option ℕ :=
  s.enodes[e]!.parent.map fun p => s.anodes[p.1]!.parent

/-- The invariant of a state. -/
structure StateInv (U : Unification) (db : Database) (st : Statement) (s : State) : Prop where
  root_lt : 0 < s.enodes.size
  root_expr : s.enodes[0]!.expr = st.concl
  anodes : ∀ j, j < s.anodes.size → ∃ A, ANodeInv U db s s.anodes[j]! A
  /-- The base of an assertion node follows its number. -/
  base_eq : ∀ j, j < s.anodes.size → s.anodes[j]!.base = s.baseOf j
  /-- The stride is positive and above every binder, the base above every variable of
  the statement. -/
  stride_pos : 0 < s.stride
  stride_gt : ∀ A ∈ db.asserts, ∀ x ∈ A.vars, x.id < s.stride
  fresh_gt : ∀ v, (v ∈ st.concl.vars ∨ ∃ h ∈ st.hyps, v ∈ h.vars) → v.id < s.freshBase
  /-- A parent link points at an assertion node of the state. -/
  parent_lt : ∀ e, e < s.enodes.size → ∀ j k, s.enodes[e]!.parent = some (j, k) → j < s.anodes.size
  /-- The node above is earlier, and the children of an assertion node have it above. -/
  up_lt : ∀ e p, up s e = some p → p < e
  up_children : ∀ j, j < s.anodes.size → ∀ k, k < s.anodes[j]!.children.length →
    up s s.anodes[j]!.children[k]! = some s.anodes[j]!.parent
  /-- Every variable of an expression node is below the next base. -/
  vars_lt : ∀ i, i < s.enodes.size → ∀ v ∈ s.enodes[i]!.expr.vars, v.id < s.baseOf s.anodes.size
  /-- An attempt recorded has its node, or no unifier at the base it used; its base is
  above the expression; and an expanded node has tried every assertion. -/
  tried_spec : ∀ i a B, (i, a, B) ∈ s.tried → ∀ A, db.asserts[a]? = some A →
    (∃ j, j < s.anodes.size ∧ s.anodes[j]!.parent = i ∧ s.anodes[j]!.assertion = a) ∨
    U.mgu [(s.enodes[i]!.expr, A.concl.rename B)] = none
  tried_fresh : ∀ i a B, (i, a, B) ∈ s.tried → ∀ v ∈ s.enodes[i]!.expr.vars, v.id < B
  tried_lt : ∀ i a B, (i, a, B) ∈ s.tried → i < s.enodes.size
  expanded_tried : ∀ i, i < s.enodes.size → s.enodes[i]!.expanded = true →
    ∀ a, a < db.asserts.length → ∃ B, (i, a, B) ∈ s.tried
  /-- Nodes are made in order: the children of an assertion node are above the parent
  of every assertion node up to it. -/
  parent_lt_children : ∀ j j', j ≤ j' → j' < s.anodes.size →
    ∀ c ∈ s.anodes[j']!.children, s.anodes[j]!.parent < c

/-! ### An entry's proof is valid -/

theorem getElem!_of_getElem? {A : Assertion} {l : List Assertion} {i : ℕ} (h : l[i]? = some A) : l[i]! = A := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact getElem!_pos l i hi

theorem stepSub_f_of_mem {db : Database} {a : ANode} {θ : Subst} {x : Var} (A : Assertion)
    (hA : db.asserts[a.assertion]! = A) (hx : x ∈ A.vars) :
    (stepSub db a θ).f x = θ.apply (a.sub.apply (.var (renamed a.base x))) := by
  simp [stepSub, Subst.ofFun, hA, hx]

mutual
/-- The substitution of a step applied to an expression over the binders: the answer
after the unifier after the renaming. -/
theorem stepSub_apply {db : Database} {a : ANode} {θ : Subst} (A : Assertion)
    (hA : db.asserts[a.assertion]! = A) :
    ∀ q : Exp, q.vars ⊆ A.vars.toFinset →
      (stepSub db a θ).apply q = θ.apply (a.sub.apply (q.rename a.base))
  | .var x, hq => by
    have hx : x ∈ A.vars := List.mem_toFinset.1 (hq (by simp [Exp.vars]))
    rw [Subst.apply_var, stepSub_f_of_mem A hA hx]
    rfl
  | .const _ _, _ => by simp [Subst.apply, Exp.rename]
  | .app _ _ args, hq => by
    simp only [Subst.apply, Exp.rename]
    congr 1
    exact stepSub_applyList A hA args (by simpa [Exp.vars] using hq)
theorem stepSub_applyList {db : Database} {a : ANode} {θ : Subst} (A : Assertion)
    (hA : db.asserts[a.assertion]! = A) :
    ∀ es : List Exp, Exp.varsList es ⊆ A.vars.toFinset →
      (stepSub db a θ).applyList es = θ.applyList (a.sub.applyList (Exp.renameList a.base es))
  | [], _ => rfl
  | e :: es, hq => by
    simp only [Subst.applyList, Exp.renameList]
    have h1 : e.vars ⊆ A.vars.toFinset := fun v hv => hq (by simp [Exp.varsList, hv])
    have h2 : Exp.varsList es ⊆ A.vars.toFinset := fun v hv => hq (by simp [Exp.varsList, hv])
    rw [stepSub_apply A hA e h1, stepSub_applyList A hA es h2]
end

theorem stepSub_typed {db : Database} {a : ANode} {θ : Subst} (hθ : θ.Typed) (ha : a.sub.Typed) :
    (stepSub db a θ).Typed := by
  intro x
  simp only [stepSub, Subst.ofFun]
  split_ifs with hx
  · rw [Subst.apply_var]
    refine ⟨Ty.fits_trans (ha (renamed a.base x)).1 (Subst.ty_apply hθ _), fun hn => ?_⟩
    exact Subst.apply_isName hθ _ ((ha (renamed a.base x)).2 hn) ((ha (renamed a.base x)).1.2 hn)
  · exact ⟨Ty.fits_refl _, fun _ => trivial⟩

theorem proofsOf_eq_map (db : Database) (s : State) (θ : Subst) :
    ∀ cs : List SptTree, proofsOf db s θ cs = cs.map (proofOf db s θ)
  | [] => rfl
  | t :: ts => by simp [proofsOf, proofsOf_eq_map db s θ ts]

theorem flatMap_congr_mem {α β : Type} (l : List α) (f g : α → List β) (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (List.mem_cons_self), ih fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- The proof of a tree at node `i` that the answer absorbs has the shape of a proof
of the statement under the answer, and proves the node's expression under it. -/
theorem shape_of_inv {U : Unification} {db : Database} (hwf : db.WF) {st : Statement} {s : State}
    (hs : StateInv U db st s)
    {θ : Subst} (hθ : θ.Typed) {i : ℕ} {T : SptTree} (hat : T.At s i) (habs : Absorbs s st θ T) :
    Shape db (st.subst θ) (proofOf db s θ T) ∧ (proofOf db s θ T).expr = θ.apply s.enodes[i]!.expr := by
  induction hat with
  | leaf i h =>
    cases habs with
    | leaf _ _ hh heq =>
      refine ⟨?_, rfl⟩
      simp only [proofOf]
      refine Shape.hyp h _ (by simp [Statement.subst, hh]) ?_
      rw [heq]
      simp only [Statement.subst]
      rw [getElem!_map' _ _ h hh]
  | node i j cs hj hp hlen hcs ih =>
    cases habs with
    | node _ _ hab hcsabs =>
      obtain ⟨A, hinv⟩ := hs.anodes j hj
      have hwfA : A.WF := hwf A (List.mem_of_getElem? hinv.assertion)
      have hA! : db.asserts[s.anodes[j]!.assertion]! = A := getElem!_of_getElem? hinv.assertion
      have hexpr : ∀ k, k < cs.length →
          (proofOf db s θ cs[k]!).expr = θ.apply (s.anodes[j]!.sub.apply (A.hyps[k]!.rename s.anodes[j]!.base)) := by
        intro k hk
        have hmem : cs[k]! ∈ cs := by rw [getElem!_pos cs k hk]; exact List.getElem_mem hk
        rw [(ih k hk (hcsabs _ hmem)).2, (hinv.children k (hlen ▸ hk)).2]
      refine ⟨?_, by simp only [proofOf, PTree.expr, hp]⟩
      simp only [proofOf]
      refine Shape.step _ _ _ _ A hinv.assertion (stepSub_typed hθ hinv.typed) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [stepSub, Subst.ofFun, hA!, Finset.mem_filter] at hx
        exact hx.1
      · rw [stepSub_apply A hA! A.concl hwfA.concl_vars, ← hinv.unifies, ← Subst.apply_comp, hab]
      · rw [proofsOf_eq_map, List.map_map]
        apply List.ext_getElem
        · simp [hlen, hinv.children_len]
        · intro n h1 h2
          simp only [List.getElem_map, Function.comp]
          have hn : n < cs.length := by simpa using h1
          have hnA : n < A.hyps.length := by simpa using h2
          rw [← getElem!_pos cs n hn, hexpr n hn, ← getElem!_pos A.hyps n hnA,
            stepSub_apply A hA! _ (hwfA.hyps_vars _ (by rw [getElem!_pos A.hyps n hnA]; exact List.getElem_mem hnA))]
      · intro c hc
        rw [proofsOf_eq_map, List.mem_map] at hc
        obtain ⟨t, ht, rfl⟩ := hc
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
        have hmem : cs[k]! ∈ cs := by rw [getElem!_pos cs k hk]; exact List.getElem_mem hk
        rw [← getElem!_pos cs k hk]
        exact (ih k hk (hcsabs _ hmem)).1

/-- The conditions of the proof of a tree: the tree's conditions under the answer. -/
theorem conds_proofOf {U : Unification} {db : Database} (hwf : db.WF) {st : Statement} {s : State}
    (hs : StateInv U db st s)
    {θ : Subst} {i : ℕ} {T : SptTree} (hat : T.At s i) :
    (proofOf db s θ T).conds db = (T.conds s).map (Cond.apply θ) := by
  induction hat with
  | leaf i h => simp [proofOf, PTree.conds, SptTree.conds]
  | node i j cs hj hp hlen hcs ih =>
    obtain ⟨A, hinv⟩ := hs.anodes j hj
    have hwfA : A.WF := hwf A (List.mem_of_getElem? hinv.assertion)
    have hA! : db.asserts[s.anodes[j]!.assertion]! = A := getElem!_of_getElem? hinv.assertion
    simp only [proofOf, PTree.conds, SptTree.conds, List.map_append]
    congr 1
    · unfold stepConds
      rw [hinv.assertion, hinv.conds]
      simp only [nodeConds, List.map_map]
      apply List.map_congr_left
      intro p hp
      simp only [Function.comp, Cond.apply]
      rw [stepSub_f_of_mem A hA! (hwfA.pairs_vars p hp).1, stepSub_f_of_mem A hA! (hwfA.pairs_vars p hp).2]
    · rw [PTree.condsList_eq_flatMap, proofsOf_eq_map, List.flatMap_map, SptTree.condsList_eq_flatMap,
        List.map_flatMap]
      apply flatMap_congr_mem
      intro t ht
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 ht
      rw [← getElem!_pos cs k hk]
      exact ih k hk

/-- The theorem of this file: an entry at the root with the invariants gives a valid
proof of the statement under its answer, with the conclusion under the answer at the
root. -/
theorem valid_of_inv {U : Unification} {db : Database} (hwf : db.WF) {st : Statement} {s : State}
    (hs : StateInv U db st s)
    (E : Entry) (hE : EntryInv s st 0 E) :
    Valid db (st.subst E.sub) (E.proof db s) ∧ (E.proof db s).expr = E.sub.apply st.concl := by
  obtain ⟨hshape, hexpr⟩ := shape_of_inv hwf hs hE.typed hE.at_ hE.absorbs
  refine ⟨⟨hshape, ?_⟩, ?_⟩
  · intro k hk
    rw [Entry.proof, conds_proofOf hwf hs hE.at_, ← hE.conds] at hk
    exact hE.holds k hk
  · rw [Entry.proof, hexpr, hs.root_expr]

end Theory
