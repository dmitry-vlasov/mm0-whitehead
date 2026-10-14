/-
The stack invariant (milestone V3, part f). Everything is judged in the world of the
statement's end — its final store, context (binders and all dummies) and hypotheses —
which every intermediate state is a part of. An element of the stack is valid assuming
the obligations above it: `Conv` pushes a proof whose validity rests on the obligation
it pushes above it, and so does `ConvCut` for a conversion.
-/
import Verifier.Disjoint

namespace Verifier

open mm0

structure World where
  E : env
  Γ : ctx
  store : List Node
  hyps : List ℕ

def World.x (W : World) (e : ℕ) : sexpr := toSexpr W.store e

def World.Hs (W : World) : Set sexpr := {x | ∃ h ∈ W.hyps, toSexpr W.store h = x}

/-- An obligation `e1 =?= e2` that holds. -/
def ObTrue (W : World) (e1 e2 : ℕ) : Prop :=
  ∃ s, conv W.E W.Γ (W.x e1) (W.x e2) s ∧ sexpr.ok W.E W.Γ (W.x e1) s ∧ sexpr.ok W.E W.Γ (W.x e2) s

/-- An element valid, its nodes below `n`. -/
def ElOk (W : World) (n : ℕ) : El → Prop
  | .expr e => e < n
  | .proof e => e < n ∧ proof W.E W.Γ W.Hs (W.x e)
  | .conv e1 e2 => e1 < n ∧ e2 < n ∧ ObTrue W e1 e2
  | .coConv e1 e2 => e1 < n ∧ e2 < n

/-- What an element asks of the elements below it. -/
def ObOf (W : World) : El → Prop
  | .coConv e1 e2 => ObTrue W e1 e2
  | _ => True

def SOk (W : World) (n : ℕ) : List El → Prop
  | [] => True
  | el :: l => ElOk W n el ∧ (ObOf W el → SOk W n l)

def HeapOk (W : World) (n : ℕ) (heap : List El) : Prop :=
  ∀ el ∈ heap, ElOk W n el ∧ ∀ a b, el ≠ El.coConv a b

/-! ### Generic facts -/

theorem ElOk.mono {W : World} {n n' : ℕ} (h : n ≤ n') : ∀ {el : El}, ElOk W n el → ElOk W n' el
  | .expr _, he => by simp only [ElOk] at he ⊢; omega
  | .proof _, ⟨he, hp⟩ => ⟨by omega, hp⟩
  | .conv _ _, ⟨h1, h2, h3⟩ => ⟨by omega, by omega, h3⟩
  | .coConv _ _, ⟨h1, h2⟩ => ⟨by omega, by omega⟩

theorem SOk.mono {W : World} {n n' : ℕ} (h : n ≤ n') : ∀ {l : List El}, SOk W n l → SOk W n' l
  | [], _ => trivial
  | _ :: _, ⟨h1, h2⟩ => ⟨h1.mono h, fun ho => SOk.mono h (h2 ho)⟩

theorem HeapOk.mono {W : World} {n n' : ℕ} (h : n ≤ n') {heap : List El} (hh : HeapOk W n heap) : HeapOk W n' heap :=
  fun el hel => ⟨(hh el hel).1.mono h, (hh el hel).2⟩

theorem HeapOk.push {W : World} {n : ℕ} {heap : List El} {el : El} (hh : HeapOk W n heap) (he : ElOk W n el)
    (hnc : ∀ a b, el ≠ El.coConv a b) : HeapOk W n (heap ++ [el]) := by
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hh x hx
  · simp only [List.mem_singleton] at hx
    subst hx
    exact ⟨he, hnc⟩

theorem HeapOk.push_ite {W : World} {n : ℕ} {heap : List El} {el : El} (hh : HeapOk W n heap) (he : ElOk W n el)
    (hnc : ∀ a b, el ≠ El.coConv a b) (b : Bool) : HeapOk W n (if b then heap ++ [el] else heap) := by
  cases b
  · exact hh
  · exact hh.push he hnc

theorem SOk.push {W : World} {n : ℕ} {l : List El} {el : El} (he : ElOk W n el) (hl : SOk W n l) : SOk W n (el :: l) :=
  ⟨he, fun _ => hl⟩

theorem SOk.tail_of_not_ob {W : World} {n : ℕ} {l : List El} {el : El} (h : SOk W n (el :: l))
    (hnc : ∀ a b, el ≠ El.coConv a b) : SOk W n l := by
  apply h.2
  cases el with
  | coConv a b => exact absurd rfl (hnc a b)
  | _ => trivial

theorem SOk.drop_exprs {W : World} {n : ℕ} : ∀ (ps : List ℕ) {l : List El}, SOk W n (ps.map El.expr ++ l) →
    (∀ p ∈ ps, p < n) ∧ SOk W n l
  | [], _, h => ⟨fun _ h => by simp at h, h⟩
  | p :: ps, l, h => by
    have h' := SOk.tail_of_not_ob h (fun a b h => by cases h)
    obtain ⟨hps, hl⟩ := SOk.drop_exprs ps h'
    exact ⟨fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h.1
      · exact hps q hq, hl⟩

theorem SOk.drop_proofs {W : World} {n : ℕ} : ∀ (ps : List ℕ) {l : List El}, SOk W n (ps.map El.proof ++ l) →
    (∀ p ∈ ps, p < n ∧ proof W.E W.Γ W.Hs (W.x p)) ∧ SOk W n l
  | [], _, h => ⟨fun _ h => by simp at h, h⟩
  | p :: ps, l, h => by
    have h' := SOk.tail_of_not_ob h (fun a b h => by cases h)
    obtain ⟨hps, hl⟩ := SOk.drop_proofs ps h'
    exact ⟨fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h.1
      · exact hps q hq, hl⟩

/-- Obligations pushed together: each well-formed, and the rest valid once all hold. -/
theorem SOk.of_obs {W : World} {n : ℕ} : ∀ (obs : List (ℕ × ℕ)) {l : List El},
    (∀ ab ∈ obs, ab.1 < n ∧ ab.2 < n) → ((∀ ab ∈ obs, ObTrue W ab.1 ab.2) → SOk W n l) →
    SOk W n (obs.map (fun ab => El.coConv ab.1 ab.2) ++ l)
  | [], _, _, h => h (fun _ h => by simp at h)
  | ab :: obs, l, hwf, h => by
    refine ⟨hwf ab (List.mem_cons_self ..), fun hob => SOk.of_obs obs (fun x hx => hwf x (List.mem_cons_of_mem _ hx))
      fun hall => h fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hob
    · exact hall x hx

theorem zipWith_coConv_eq (A B : List ℕ) :
    List.zipWith El.coConv A B = (A.zip B).map (fun ab => El.coConv ab.1 ab.2) := by
  induction A generalizing B with
  | nil => simp
  | cons a A ih =>
    cases B with
    | nil => simp
    | cons b B => simp [ih]

/-! ### The world and the states in it -/

/-- The final world of a statement with binders `bs` and dummies `D`. -/
structure WorldOk (W : World) (c : Ctx) (allTerms : List TermDecl) (bs : List Binder) (D : List ℕ) : Prop where
  env : EnvHas W.E c allTerms
  ctx : W.Γ = ctxOf bs D
  store : StoreOk W.E bs D c.isDef W.store

theorem EnvHas.termsUnique {E : env} {c : Ctx} {allTerms : List TermDecl} (h : EnvHas E c allTerms) : TermsUnique E := by
  intro t a r o a' r' o' h1 h2
  obtain ⟨d, hd, rfl, rfl⟩ := h.terms_unique t a r o h1
  obtain ⟨d', hd', rfl, rfl⟩ := h.terms_unique t a' r' o' h2
  rw [hd] at hd'
  cases hd'
  exact ⟨rfl, rfl⟩

/-- A node of the final store is well-typed at its sort in the final context. -/
theorem WorldOk.node {W : World} {c : Ctx} {allTerms : List TermDecl} {bs : List Binder} {D : List ℕ}
    (hW : WorldOk W c allTerms bs D) {p : ℕ} {n : Node} (hp : W.store[p]? = some n) :
    NodeOk W.E bs D c.isDef W.store p n := hW.store.nodes p n hp

theorem WorldOk.ok_node {W : World} {c : Ctx} {allTerms : List TermDecl} {bs : List Binder} {D : List ℕ}
    (hW : WorldOk W c allTerms bs D) {p : ℕ} {n : Node} (hp : W.store[p]? = some n) :
    sexpr.ok W.E W.Γ (W.x p) n.ty.sort := by
  rw [hW.ctx]
  exact (hW.node hp).ok

theorem WorldOk.exists_node {W : World} {c : Ctx} {allTerms : List TermDecl} {bs : List Binder} {D : List ℕ}
    (hW : WorldOk W c allTerms bs D) {p : ℕ} (hp : p < W.store.length) :
    ∃ s, sexpr.ok W.E W.Γ (W.x p) s :=
  ⟨_, hW.ok_node (List.getElem?_eq_getElem hp)⟩

theorem ObTrue.refl {W : World} {c : Ctx} {allTerms : List TermDecl} {bs : List Binder} {D : List ℕ}
    (hW : WorldOk W c allTerms bs D) {e : ℕ} (he : e < W.store.length) : ObTrue W e e := by
  obtain ⟨s, hs⟩ := hW.exists_node he
  exact ⟨s, conv'.refl hs, hs, hs⟩

theorem ObTrue.symm {W : World} {e1 e2 : ℕ} (h : ObTrue W e1 e2) : ObTrue W e2 e1 := by
  obtain ⟨s, hc, h1, h2⟩ := h
  exact ⟨s, conv'.symm hc, h2, h1⟩

end Verifier
