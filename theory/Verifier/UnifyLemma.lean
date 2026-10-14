/-
The unify lemma (milestone V3, part c): a stream the unifier accepts for a node, with
a heap of nodes, decodes to an expression whose instance under the heap's expressions
is the node's. By strong induction on the decoder's fuel; the invariant between the
two heaps allows a saved term still being read to be undecoded, provided it is above
every node of the current segment, which the arguments of a term are.
-/
import Verifier.CtxOk

namespace Verifier

open mm0
open Whitehead.Mmb (UnifyCmd)

/-! ### Substitution -/

theorem subst_app' (σ : List sexpr) : ∀ (es : List sexpr) (f : sexpr),
    sexpr.subst σ (sexpr.app' f es) = sexpr.app' (sexpr.subst σ f) (es.map (sexpr.subst σ))
  | [], _ => rfl
  | x :: xs, f => by
    rw [sexpr.app', subst_app' σ xs, List.map_cons, sexpr.app']
    rfl

theorem subst_app (σ : List sexpr) (t : term_id) (es : List sexpr) :
    sexpr.subst σ (sexpr.app t es) = sexpr.app t (es.map (sexpr.subst σ)) := by
  rw [sexpr.app, subst_app']
  rfl

theorem subst_prefix {σ σ' : List sexpr} (h : σ <+: σ') : ∀ {x : sexpr}, sexpr.VarsLt x σ.length →
    sexpr.subst σ' x = sexpr.subst σ x
  | .var v, hv => by
    obtain ⟨tl, rfl⟩ := h
    simp only [sexpr.subst]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hv]
  | .term _, _ => rfl
  | .app1 f x, h' => by
    simp only [sexpr.subst]
    rw [subst_prefix h h'.1, subst_prefix h h'.2]

theorem varsLt_mono {x : sexpr} : ∀ {n m : ℕ}, n ≤ m → sexpr.VarsLt x n → sexpr.VarsLt x m := by
  induction x with
  | var v => intro n m h hv; exact lt_of_lt_of_le hv h
  | term _ => intro _ _ _ _; trivial
  | app1 f x ihf ihx => intro n m h hv; exact ⟨ihf h hv.1, ihx h hv.2⟩

/-! ### The invariant -/

/-- Every application of the store is of a term of the context with that many
arguments. -/
def StoreTerms (c : Ctx) (store : List Node) : Prop :=
  ∀ (p : ℕ) (ty : Ty) (t : ℕ) (args : List ℕ), store[p]? = some (Node.app ty t args) →
    ∃ d : TermDecl, c.terms[t]? = some d ∧ args.length = d.args.length

/-- The decoder's heap against the unifier's: a decoded entry (`some x`) is the node's
expression under `σ`, with its variables below `σ`'s length; an undecoded one (`none`,
a saved term still being read) is above every node of the current segment `ks`. -/
structure HeapCorr (σ : List sexpr) (store : List Node) (H : UHeap) (heapS : List (Option sexpr)) (ks : List ℕ) :
    Prop where
  len : H.length = heapS.length
  entries : ∀ (i e : ℕ) (b : Bool), H[i]? = some (e, b) → ∃ ox, heapS[i]? = some ox ∧
    (∀ x, ox = some x → toSexpr store e = sexpr.subst σ x ∧ sexpr.VarsLt x σ.length) ∧
    (ox = none → ∀ k ∈ ks, k < e)

/-- The dummies matched so far: the `j`-th is a bound variable of the store of the
stream's sort, at position `nargs + j` of the substitution. -/
def DummiesCorr (store : List Node) (nargs : ℕ) (σ : List sexpr) (ds : List ℕ) : Prop :=
  ∀ (j s : ℕ), ds[j]? = some s →
    ∃ (v : ℕ) (ty : Ty) (p : ℕ), σ[nargs + j]? = some (sexpr.var v) ∧ store[p]? = some (Node.var ty v) ∧
      ty.bound = true ∧ ty.sort = s

theorem dummiesCorr_prefix {store : List Node} {nargs : ℕ} {σ σ' : List sexpr} {ds : List ℕ}
    (hσ : σ <+: σ') (hlen : σ.length = nargs + ds.length) (h : DummiesCorr store nargs σ ds) :
    DummiesCorr store nargs σ' ds := by
  unfold DummiesCorr at h ⊢
  intro j s hs
  obtain ⟨v, ty, p, hv, hp, hb, hsort⟩ := h j s hs
  refine ⟨v, ty, p, ?_, hp, hb, hsort⟩
  obtain ⟨tl, rfl⟩ := hσ
  rw [List.getElem?_append_left (by have := (List.getElem?_eq_some_iff.1 hs).1; omega)]
  exact hv

/-- What a segment of the stream leaves: the substitution and the dummies grown, the
node heap grown, the decoder's heap against it, no new undecoded entry, and the
dummies matched. -/
structure Out (store : List Node) (nargs : ℕ) (σ : List sexpr) (ds : List ℕ) (H : UHeap) (heapS : List (Option sexpr))
    (σ' : List sexpr) (ds' : List ℕ) (H' : UHeap) (heapS' : List (Option sexpr)) : Prop where
  σpre : σ <+: σ'
  σlen : σ'.length = nargs + ds'.length
  dpre : ds <+: ds'
  Hpre : H <+: H'
  corr : HeapCorr σ' store H' heapS' []
  pending : ∀ i : ℕ, heapS'[i]? = some none → heapS[i]? = some none ∧ H'[i]? = H[i]?
  dummies : DummiesCorr store nargs σ' ds'

theorem Out.refl {store : List Node} {nargs : ℕ} {σ : List sexpr} {ds : List ℕ} {H : UHeap} {heapS : List (Option sexpr)}
    {ks : List ℕ} (h : HeapCorr σ store H heapS ks) (hlen : σ.length = nargs + ds.length)
    (hd : DummiesCorr store nargs σ ds) : Out store nargs σ ds H heapS σ ds H heapS :=
  ⟨List.prefix_rfl, hlen, List.prefix_rfl, List.prefix_rfl,
   ⟨h.len, fun i e b hi => by
     obtain ⟨ox, hox, hx, _⟩ := h.entries i e b hi
     exact ⟨ox, hox, hx, fun _ _ h => by simp at h⟩⟩,
   fun i hi => ⟨hi, rfl⟩, hd⟩

theorem Out.trans {store : List Node} {nargs : ℕ} {σ₁ σ₂ σ₃ : List sexpr} {ds₁ ds₂ ds₃ : List ℕ} {H₁ H₂ H₃ : UHeap}
    {heapS₁ heapS₂ heapS₃ : List (Option sexpr)} (h₁ : Out store nargs σ₁ ds₁ H₁ heapS₁ σ₂ ds₂ H₂ heapS₂)
    (h₂ : Out store nargs σ₂ ds₂ H₂ heapS₂ σ₃ ds₃ H₃ heapS₃) : Out store nargs σ₁ ds₁ H₁ heapS₁ σ₃ ds₃ H₃ heapS₃ :=
  ⟨h₁.σpre.trans h₂.σpre, h₂.σlen, h₁.dpre.trans h₂.dpre, h₁.Hpre.trans h₂.Hpre, h₂.corr,
   fun i hi => by
     obtain ⟨h2a, h2b⟩ := h₂.pending i hi
     obtain ⟨h1a, h1b⟩ := h₁.pending i h2a
     exact ⟨h1a, h2b.trans h1b⟩,
   h₂.dummies⟩

/-- After a segment, the decoder's heap against the node heap for the next segment:
an undecoded entry was undecoded before, above the earlier segment. -/
theorem heapCorr_restore {store : List Node} {nargs : ℕ} {σ σ' : List sexpr} {ds ds' : List ℕ} {H H' : UHeap}
    {heapS heapS' : List (Option sexpr)} {ks ks' : List ℕ} (h : HeapCorr σ store H heapS ks)
    (hout : Out store nargs σ ds H heapS σ' ds' H' heapS') (hsub : ∀ k ∈ ks', k ∈ ks) :
    HeapCorr σ' store H' heapS' ks' :=
  ⟨hout.corr.len, fun i e b hi => by
    obtain ⟨ox, hox, hx, _⟩ := hout.corr.entries i e b hi
    refine ⟨ox, hox, hx, fun hnone => ?_⟩
    subst hnone
    obtain ⟨hbefore, hH⟩ := hout.pending i hox
    rw [hH] at hi
    obtain ⟨ox', hox', _, hpend⟩ := h.entries i e b hi
    rw [hbefore] at hox'
    simp only [Option.some.injEq] at hox'
    subst hox'
    exact fun k hk => hpend rfl k (hsub k hk)⟩

theorem heapCorr_mono {store : List Node} {σ : List sexpr} {H : UHeap} {heapS : List (Option sexpr)} {ks ks' : List ℕ}
    (h : HeapCorr σ store H heapS ks) (hsub : ∀ k ∈ ks', k ∈ ks) : HeapCorr σ store H heapS ks' :=
  ⟨h.len, fun i e b hi => by
    obtain ⟨ox, hox, hx, hpend⟩ := h.entries i e b hi
    exact ⟨ox, hox, hx, fun hn k hk => hpend hn k (hsub k hk)⟩⟩

/-! ### The decoder consumes the stream -/

theorem decode_length (terms : List TermDecl) (nargs : ℕ) : ∀ fuel : ℕ,
    (∀ (us : List UnifyCmd) heap ds x rest heapS' ds', decodeExpr terms nargs fuel us heap ds = some (x, rest, heapS', ds') →
      rest.length < us.length) ∧
    (∀ (n : ℕ) (us : List UnifyCmd) heap ds xs rest heapS' ds', decodeN terms nargs fuel n us heap ds = some (xs, rest, heapS', ds') →
      rest.length ≤ us.length)
  | 0 => ⟨fun _ _ _ _ _ _ _ h => by simp [decodeExpr] at h, fun _ _ _ _ _ _ _ _ h => by simp [decodeN] at h⟩
  | fuel + 1 => by
    obtain ⟨ihE, ihN⟩ := decode_length terms nargs fuel
    constructor
    · intro us heap ds x rest heapS' ds' h
      match us with
      | [] => simp [decodeExpr] at h
      | UnifyCmd.ref i :: us' =>
        simp only [decodeExpr] at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl, _, _⟩ := h
          simp
        · simp at h
      | UnifyCmd.term t save :: us' =>
        simp only [decodeExpr] at h
        split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i args rest' heapS'' ds'' hinner
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _, _⟩ := h
            have := ihN _ _ _ _ _ _ _ _ hinner
            simp only [List.length_cons]
            omega
      | UnifyCmd.dummy s :: us' =>
        simp only [decodeExpr, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _, _⟩ := h
        simp
      | UnifyCmd.hyp :: us' => simp [decodeExpr] at h
    · intro n us heap ds xs rest heapS' ds' h
      cases n with
      | zero =>
        simp only [decodeN, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl, _, _⟩ := h
        exact le_refl _
      | succ n =>
        simp only [decodeN] at h
        split at h
        · simp at h
        · rename_i e rest₁ heap₁ ds₁ hE
          split at h
          · simp at h
          · rename_i es rest₂ heap₂ ds₂ hN
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl, _, _⟩ := h
            have h1 := ihE _ _ _ _ _ _ _ hE
            have h2 := ihN _ _ _ _ _ _ _ _ hN
            omega

/-! ### The lemma -/

theorem forall₂_map_eq {α β γ : Type} {f : α → γ} {g : β → γ} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ (fun a b => f a = g b) l₁ l₂ → l₁.map f = l₂.map g
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h hl => by simp [h, forall₂_map_eq hl]

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | [], [], _, _, h => by simp at h
  | _ :: _, _ :: _, List.Forall₂.cons hab hl, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, h⟩ := forall₂_mem_right hl b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

/-- The statement for one expression (fuel `2|us| + 1`) and for `n` in sequence
(`2|us| + 2`). -/
def PExpr (c : Ctx) (st : State) (terms : List TermDecl) (nargs fuel : ℕ) : Prop :=
  ∀ (us : List UnifyCmd), 2 * us.length + 1 ≤ fuel →
    ∀ (mode : UMode) (e : ℕ) (K : List ℕ) (H : UHeap) (heapS : List (Option sexpr)) (ds : List ℕ) (σ : List sexpr)
      (S : List El) (hs : List ℕ) (S' : List El) (hs' : List ℕ),
    Unify c st mode H us (e :: K) S hs S' hs' → HeapCorr σ st.store H heapS [e] →
    σ.length = nargs + ds.length → DummiesCorr st.store nargs σ ds →
    ∃ x rest heapS' ds' σ' H', decodeExpr terms nargs fuel us heapS ds = some (x, rest, heapS', ds') ∧
      Out st.store nargs σ ds H heapS σ' ds' H' heapS' ∧
      toSexpr st.store e = sexpr.subst σ' x ∧ sexpr.VarsLt x σ'.length ∧
      Unify c st mode H' rest K S hs S' hs'

def PN (c : Ctx) (st : State) (terms : List TermDecl) (nargs fuel : ℕ) : Prop :=
  ∀ (us : List UnifyCmd), 2 * us.length + 2 ≤ fuel →
    ∀ (mode : UMode) (n : ℕ) (ks K : List ℕ) (H : UHeap) (heapS : List (Option sexpr)) (ds : List ℕ) (σ : List sexpr)
      (S : List El) (hs : List ℕ) (S' : List El) (hs' : List ℕ),
    ks.length = n → Unify c st mode H us (ks ++ K) S hs S' hs' → HeapCorr σ st.store H heapS ks →
    σ.length = nargs + ds.length → DummiesCorr st.store nargs σ ds →
    ∃ xs rest heapS' ds' σ' H', decodeN terms nargs fuel n us heapS ds = some (xs, rest, heapS', ds') ∧
      Out st.store nargs σ ds H heapS σ' ds' H' heapS' ∧
      List.Forall₂ (fun k x => toSexpr st.store k = sexpr.subst σ' x ∧ sexpr.VarsLt x σ'.length) ks xs ∧
      Unify c st mode H' rest K S hs S' hs'

theorem heapCorr_below {store : List Node} {σ : List sexpr} {H : UHeap} {heapS : List (Option sexpr)} {e : ℕ}
    {ks : List ℕ} (h : HeapCorr σ store H heapS [e]) (hks : ∀ k ∈ ks, k < e) : HeapCorr σ store H heapS ks :=
  ⟨h.len, fun i e' b hi => by
    obtain ⟨ox, hox, hx, hpend⟩ := h.entries i e' b hi
    exact ⟨ox, hox, hx, fun hn k hk => lt_trans (hks k hk) (hpend hn e (List.mem_singleton_self e))⟩⟩

theorem unify_decode {c : Ctx} {st : State} (hwf : StoreWF st.store) (hterms : StoreTerms c st.store)
    {terms : List TermDecl} (hprefix : ∀ (t : ℕ) (d : TermDecl), c.terms[t]? = some d → terms[t]? = some d) (nargs : ℕ) :
    ∀ fuel : ℕ, PExpr c st terms nargs fuel ∧ PN c st terms nargs fuel
  | 0 => ⟨fun _ h => by omega, fun _ h => by omega⟩
  | fuel + 1 => by
    obtain ⟨ihE, ihN⟩ := unify_decode hwf hterms hprefix nargs fuel
    constructor
    · -- one expression
      intro us hfuel mode e K H heapS ds σ S hs S' hs' hu hcorr hlen hd
      cases hu with
      | ref _ _ _ _ _ _ _ _ _ i b hi hrest =>
        obtain ⟨ox, hox, hx, hpend⟩ := hcorr.entries i e b hi
        cases ox with
        | none => exact absurd (hpend rfl e (List.mem_singleton_self e)) (lt_irrefl e)
        | some x =>
          obtain ⟨hsx, hvl⟩ := hx x rfl
          refine ⟨x, _, heapS, ds, σ, H, ?_, Out.refl hcorr hlen hd, hsx, hvl, hrest⟩
          simp [decodeExpr, hox]
      | term _ _ us' _ t save ty args _ _ _ _ _ hnode hrest =>
        obtain ⟨d, hd', hargs⟩ := hterms e ty t args hnode
        have hdecl := hprefix t d hd'
        have hargs_lt : ∀ a ∈ args, a < e := hwf e ty t args hnode
        have hfuel' : 2 * us'.length + 2 ≤ fuel := by simp at hfuel; omega
        -- the arguments, a segment: the saved entry, undecoded, is above them
        have hcorr' : HeapCorr σ st.store (if save then H ++ [(e, true)] else H)
            (if save then heapS ++ [none] else heapS) args := by
          cases save with
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            exact heapCorr_below hcorr hargs_lt
          | true =>
            simp only [ite_true]
            refine ⟨by simp [hcorr.len], ?_⟩
            intro i e' b hi
            by_cases hil : i < H.length
            · rw [List.getElem?_append_left hil] at hi
              obtain ⟨ox, hox, hx, hpend⟩ := hcorr.entries i e' b hi
              refine ⟨ox, ?_, hx, fun hn k hk => lt_trans (hargs_lt k hk) (hpend hn e (List.mem_singleton_self e))⟩
              rw [List.getElem?_append_left (by rw [← hcorr.len]; exact hil)]
              exact hox
            · rw [List.getElem?_append_right (Nat.le_of_not_lt hil)] at hi
              cases hil' : i - H.length with
              | zero =>
                rw [hil'] at hi
                simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
                obtain ⟨rfl, rfl⟩ := hi
                refine ⟨none, ?_, (fun _ h => by cases h), fun _ k hk => hargs_lt k hk⟩
                rw [List.getElem?_append_right (by rw [← hcorr.len]; exact Nat.le_of_not_lt hil), ← hcorr.len, hil']
                rfl
              | succ _ => rw [hil'] at hi; simp at hi
        obtain ⟨xs, rest', heapS₁, ds₁, σ₁, H₁, hdec, hout, hall, hrest'⟩ :=
          ihN us' hfuel' mode args.length args K _ _ ds σ S hs S' hs' rfl hrest hcorr' hlen hd
        have hsx : toSexpr st.store e = sexpr.subst σ₁ (sexpr.app t xs) := by
          rw [toSexpr_app hwf hnode, subst_app]
          congr 1
          exact forall₂_map_eq (hall.imp fun _ _ h => h.1)
        have hvl : sexpr.VarsLt (sexpr.app t xs) σ₁.length := by
          rw [varsLt_app]
          intro x hx
          obtain ⟨k, _, hk⟩ := forall₂_mem_right hall x hx
          exact hk.2
        refine ⟨sexpr.app t xs, rest', if save then heapS₁.set heapS.length (some (sexpr.app t xs)) else heapS₁,
          ds₁, σ₁, H₁, ?_, ?_, hsx, hvl, hrest'⟩
        · rw [hargs] at hdec
          simp [decodeExpr, hdecl, hdec]
        · cases save with
          | false =>
            simp only [Bool.false_eq_true, ite_false] at hout ⊢
            exact hout
          | true =>
            simp only [ite_true] at hout ⊢
            have hHe : H₁[H.length]? = some (e, true) := by
              obtain ⟨tl, htl⟩ := hout.Hpre
              rw [← htl, List.append_assoc, List.getElem?_append_right (le_refl _), Nat.sub_self]
              rfl
            have hlen₁ : heapS.length < heapS₁.length := by
              have hl := hout.corr.len
              obtain ⟨tl, htl⟩ := hout.Hpre
              rw [← htl, List.length_append, List.length_append, List.length_singleton, hcorr.len] at hl
              omega
            refine ⟨hout.σpre, hout.σlen, hout.dpre, (List.prefix_append H [(e, true)]).trans hout.Hpre, ⟨?_, ?_⟩, ?_,
              hout.dummies⟩
            · rw [List.length_set]
              exact hout.corr.len
            · intro i e' b hi
              by_cases hie : i = heapS.length
              · subst hie
                rw [← hcorr.len, hHe] at hi
                simp only [Option.some.injEq, Prod.mk.injEq] at hi
                obtain ⟨rfl, rfl⟩ := hi
                refine ⟨some (sexpr.app t xs), ?_, fun x hx => ?_, (fun h => by cases h)⟩
                · rw [List.getElem?_set_self hlen₁]
                · simp only [Option.some.injEq] at hx
                  subst hx
                  exact ⟨hsx, hvl⟩
              · rw [List.getElem?_set_ne (Ne.symm hie)]
                obtain ⟨ox, hox, hx, _⟩ := hout.corr.entries i e' b hi
                exact ⟨ox, hox, hx, fun _ _ h => by simp at h⟩
            · intro i hi
              by_cases hie : i = heapS.length
              · subst hie
                rw [List.getElem?_set_self hlen₁] at hi
                cases hi
              · rw [List.getElem?_set_ne (Ne.symm hie)] at hi
                obtain ⟨hbefore, hH⟩ := hout.pending i hi
                by_cases hil : i < heapS.length
                · rw [List.getElem?_append_left hil] at hbefore
                  rw [List.getElem?_append_left (by rw [hcorr.len]; exact hil)] at hH
                  exact ⟨hbefore, hH⟩
                · rw [List.getElem?_append_right (Nat.le_of_not_lt hil)] at hbefore
                  cases hil' : i - heapS.length with
                  | zero => exact absurd (by omega) hie
                  | succ _ => rw [hil'] at hbefore; simp at hbefore
      | dummy _ us' _ s ty v _ _ _ _ _ hnode hbound hsort _ hrest =>
        have hsx := toSexpr_var hnode
        refine ⟨sexpr.var (nargs + ds.length), us', heapS ++ [some (sexpr.var (nargs + ds.length))], ds ++ [s],
          σ ++ [sexpr.var v], H ++ [(e, false)], rfl, ?_, ?_, ?_, hrest⟩
        · refine ⟨List.prefix_append _ _, by simp only [List.length_append, List.length_singleton, hlen]; omega,
            List.prefix_append _ _, List.prefix_append _ _,
            ⟨by simp [hcorr.len], ?_⟩, ?_, ?_⟩
          · intro i e' b hi
            by_cases hil : i < H.length
            · rw [List.getElem?_append_left hil] at hi
              obtain ⟨ox, hox, hx, _⟩ := hcorr.entries i e' b hi
              refine ⟨ox, by rw [List.getElem?_append_left (by rw [← hcorr.len]; exact hil)]; exact hox,
                fun x hx' => ?_, fun _ _ h => by simp at h⟩
              obtain ⟨h1, h2⟩ := hx x hx'
              exact ⟨by rw [h1, subst_prefix (List.prefix_append _ _) h2], varsLt_mono (by simp) h2⟩
            · rw [List.getElem?_append_right (Nat.le_of_not_lt hil)] at hi
              cases hil' : i - H.length with
              | zero =>
                rw [hil'] at hi
                simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
                obtain ⟨rfl, rfl⟩ := hi
                refine ⟨some (sexpr.var (nargs + ds.length)), ?_, fun x hx => ?_, (fun h => by cases h)⟩
                · rw [List.getElem?_append_right (by rw [← hcorr.len]; exact Nat.le_of_not_lt hil), ← hcorr.len, hil']
                  rfl
                · simp only [Option.some.injEq] at hx
                  subst hx
                  refine ⟨?_, by simp [sexpr.VarsLt, hlen]⟩
                  rw [hsx]
                  simp only [sexpr.subst]
                  rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_concat_length]
                  rfl
              | succ _ => rw [hil'] at hi; simp at hi
          · intro i hi
            by_cases hil : i < heapS.length
            · rw [List.getElem?_append_left hil] at hi
              exact ⟨hi, by rw [List.getElem?_append_left (by rw [hcorr.len]; exact hil)]⟩
            · rw [List.getElem?_append_right (Nat.le_of_not_lt hil)] at hi
              cases hil' : i - heapS.length with
              | zero => rw [hil'] at hi; simp at hi
              | succ _ => rw [hil'] at hi; simp at hi
          · unfold DummiesCorr
            intro j s' hj
            by_cases hjl : j < ds.length
            · rw [List.getElem?_append_left hjl] at hj
              obtain ⟨v', ty', p, hv, hp, hb, hs'⟩ := hd j s' hj
              exact ⟨v', ty', p, by rw [List.getElem?_append_left (by omega)]; exact hv, hp, hb, hs'⟩
            · rw [List.getElem?_append_right (Nat.le_of_not_lt hjl)] at hj
              cases hjl' : j - ds.length with
              | zero =>
                rw [hjl'] at hj
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
                subst hj
                have hj' : j = ds.length := by omega
                subst hj'
                refine ⟨v, ty, e, ?_, hnode, hbound, hsort⟩
                rw [← hlen, List.getElem?_concat_length]
              | succ _ => rw [hjl'] at hj; simp at hj
        · rw [hsx]
          simp only [sexpr.subst]
          rw [List.getD_eq_getElem?_getD, ← hlen, List.getElem?_concat_length]
          rfl
        · simp [sexpr.VarsLt, hlen]
    · -- a sequence
      intro us hfuel mode n ks K H heapS ds σ S hs S' hs' hn hu hcorr hlen hd
      cases ks with
      | nil =>
        subst hn
        refine ⟨[], us, heapS, ds, σ, H, rfl, Out.refl hcorr hlen hd, List.Forall₂.nil, hu⟩
      | cons k ks' =>
        subst hn
        simp only [List.cons_append] at hu
        obtain ⟨x, rest, heapS₁, ds₁, σ₁, H₁, hdec, hout₁, hsx, hvl, hu₁⟩ :=
          ihE us (by omega) mode k (ks' ++ K) H heapS ds σ S hs S' hs' hu (heapCorr_mono hcorr (by simp)) hlen hd
        have hrestlen := (decode_length terms nargs fuel).1 us heapS ds x rest heapS₁ ds₁ hdec
        obtain ⟨xs, rest', heapS₂, ds₂, σ₂, H₂, hdecN, hout₂, hall, hu₂⟩ :=
          ihN rest (by omega) mode ks'.length ks' K H₁ heapS₁ ds₁ σ₁ S hs S' hs' rfl hu₁
            (heapCorr_restore hcorr hout₁ (fun k' hk' => List.mem_cons_of_mem _ hk')) hout₁.σlen hout₁.dummies
        refine ⟨x :: xs, rest', heapS₂, ds₂, σ₂, H₂, ?_, hout₁.trans hout₂, ?_, hu₂⟩
        · simp [decodeN, hdec, hdecN]
        · refine List.Forall₂.cons ⟨?_, varsLt_mono hout₂.σpre.length_le hvl⟩ hall
          rw [hsx, subst_prefix hout₂.σpre hvl]

end Verifier
