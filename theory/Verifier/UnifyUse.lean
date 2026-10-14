/-
The three uses of the unify lemma (milestone V3, part c): a def's stream against a
node (`Unfold`, the end of a def), a theorem's stream against a node with its
subproofs on the main stack (`Thm`), and a theorem's own stream against its proved
statement and hypotheses (the end of a theorem).
-/
import Verifier.UnifyLemma

namespace Verifier

open mm0
open Whitehead.Mmb (UnifyCmd)

/-! ### The initial heap -/

def argHeap (args : List ℕ) : UHeap := args.map fun p => (p, false)

/-- The decoder's heap has no undecoded entry. -/
def NoneFree (heapS : List (Option sexpr)) : Prop := ∀ i : ℕ, heapS[i]? ≠ some none

theorem noneFree_init (n : ℕ) : NoneFree (initHeap n) := by
  intro i h
  simp [initHeap, List.getElem?_map] at h

theorem heapCorr_init (store : List Node) (args : List ℕ) (ks : List ℕ) :
    HeapCorr (args.map (toSexpr store)) store (argHeap args) (initHeap args.length) ks := by
  refine ⟨by simp [argHeap, initHeap], ?_⟩
  intro i e b hi
  simp only [argHeap, List.getElem?_map, Option.map_eq_some_iff, Prod.mk.injEq] at hi
  obtain ⟨p, hp, rfl, rfl⟩ := hi
  have hil : i < args.length := (List.getElem?_eq_some_iff.1 hp).1
  refine ⟨some (sexpr.var i), by simp [initHeap, hil], fun x hx => ?_, fun h => by cases h⟩
  simp only [Option.some.injEq] at hx
  subst hx
  refine ⟨?_, by simp [sexpr.VarsLt, hil]⟩
  simp only [sexpr.subst]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
  rfl

theorem heapCorr_any {σ : List sexpr} {store : List Node} {H : UHeap} {heapS : List (Option sexpr)} {ks ks' : List ℕ}
    (h : HeapCorr σ store H heapS ks) (hnf : NoneFree heapS) : HeapCorr σ store H heapS ks' :=
  ⟨h.len, fun i e b hi => by
    obtain ⟨ox, hox, hx, _⟩ := h.entries i e b hi
    refine ⟨ox, hox, hx, fun hn => ?_⟩
    subst hn
    exact absurd hox (hnf i)⟩

theorem noneFree_out {store : List Node} {nargs : ℕ} {σ σ' : List sexpr} {ds ds' : List ℕ} {H H' : UHeap}
    {heapS heapS' : List (Option sexpr)} (hout : Out store nargs σ ds H heapS σ' ds' H' heapS') (hnf : NoneFree heapS) :
    NoneFree heapS' := fun i h => hnf i (hout.pending i h).1

theorem prefix_eq_of_length {α : Type} {l l' : List α} (h : l <+: l') (hl : l'.length = l.length) : l' = l := by
  obtain ⟨tl, rfl⟩ := h
  simp only [List.length_append] at hl
  have : tl = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp [this]

/-! ### Definition mode -/

theorem unify_defn_rest {c : Ctx} {st : State} : ∀ {H : UHeap} {us : List UnifyCmd} {S : List El} {hs : List ℕ}
    {S' : List El} {hs' : List ℕ}, Unify c st .defn H us [] S hs S' hs' → us = []
  | _, _, _, _, _, _, Unify.nil _ _ _ _ _ => rfl

/-- A def's stream accepted against node `e` with the arguments `args`: it decodes to the
def's value and dummies, and `e`'s expression is the value under the arguments and the
dummies' variables, which are bound variables of the store of the dummies' sorts. -/
theorem unify_defn {c : Ctx} {st : State} (hwf : StoreWF st.store) (hterms : StoreTerms c st.store)
    {terms : List TermDecl} (hprefix : ∀ (t : ℕ) (d : TermDecl), c.terms[t]? = some d → terms[t]? = some d)
    {args : List ℕ} {us : List UnifyCmd} {e : ℕ} {S : List El} {hs : List ℕ} {S' : List El} {hs' : List ℕ}
    (hu : Unify c st .defn (argHeap args) us [e] S hs S' hs') :
    ∃ v ds σ', decodeDef terms args.length us = some (v, ds) ∧ args.map (toSexpr st.store) <+: σ' ∧
      σ'.length = args.length + ds.length ∧ DummiesCorr st.store args.length σ' ds ∧
      toSexpr st.store e = sexpr.subst σ' v ∧ sexpr.VarsLt v σ'.length ∧
      ∃ H', DummyNodes st args.length σ' ds (argHeap args) H' := by
  obtain ⟨x, rest, heapS', ds', σ', H', hdec, hout, hsx, hvl, hrest, _, hdn⟩ :=
    (unify_decode hwf hterms hprefix args.length (2 * us.length + 2)).1 us (by omega) .defn e [] (argHeap args)
      (initHeap args.length) [] (args.map (toSexpr st.store)) S hs S' hs' hu (heapCorr_init _ _ _) (by simp)
      (fun j s h => by simp at h)
  have := unify_defn_rest hrest
  subst this
  refine ⟨x, ds', σ', ?_, hout.σpre, hout.σlen, hout.dummies, hsx, hvl, H',
    hdn (argHeap args) ⟨List.prefix_rfl, [], rfl, fun j hj => by simp at hj, fun j hj => by simp at hj,
      fun j hj => by simp at hj⟩⟩
  simp [decodeDef, hdec]

/-! ### Theorem mode -/

/-- The hypotheses of a theorem's stream, against the subproofs on the main stack. -/
theorem unify_thm_hyps {c : Ctx} {st : State} (hwf : StoreWF st.store) (hterms : StoreTerms c st.store)
    {terms : List TermDecl} (hprefix : ∀ (t : ℕ) (d : TermDecl), c.terms[t]? = some d → terms[t]? = some d)
    (nargs : ℕ) (σ : List sexpr) (hσ : σ.length = nargs) : ∀ (fuel : ℕ) (rest : List UnifyCmd) (H : UHeap)
      (heapS : List (Option sexpr)) (S : List El) (hs : List ℕ) (S' : List El) (hs' : List ℕ),
      2 * rest.length + 2 ≤ fuel → Unify c st .thm H rest [] S hs S' hs' → HeapCorr σ st.store H heapS [] →
      NoneFree heapS →
      ∃ hl ps, decodeHyps terms nargs fuel rest heapS [] = some hl ∧ S = ps.map El.proof ++ S' ∧
        List.Forall₂ (fun p h => toSexpr st.store p = sexpr.subst σ h) ps hl
  | 0, _, _, _, _, _, _, _, hf, _, _, _ => by omega
  | fuel + 1, rest, H, heapS, S, hs, S', hs', hf, hu, hcorr, hnf => by
    cases hu with
    | nil _ _ _ _ _ => exact ⟨[], [], by simp [decodeHyps], by simp, List.Forall₂.nil⟩
    | hyp_thm _ us' e' S0 _ _ _ hu' =>
      simp only [List.length_cons] at hf
      obtain ⟨x, rest2, heapS2, ds2, σ2, H2, hdec, hout, hsx, _, hu2, hdm, -⟩ :=
        (unify_decode hwf hterms hprefix nargs fuel).1 us' (by omega) .thm e' [] H heapS [] σ S0 hs S' hs' hu'
          (heapCorr_any hcorr hnf) (by simp [hσ]) (fun j s h => by simp at h)
      have hds2 : ds2 = [] := hdm (by decide)
      subst hds2
      have hσ2 : σ2 = σ := prefix_eq_of_length hout.σpre (by rw [hout.σlen, hσ]; simp)
      subst hσ2
      have hlen2 := (decode_length terms nargs fuel).1 us' heapS [] x rest2 heapS2 [] hdec
      obtain ⟨hl, ps, hdecH, hS0, hall⟩ := unify_thm_hyps hwf hterms hprefix nargs σ2 hσ fuel rest2 H2 heapS2 S0 hs S' hs'
        (by omega) hu2 (heapCorr_any hout.corr (noneFree_out hout hnf)) (noneFree_out hout hnf)
      refine ⟨x :: hl, e' :: ps, ?_, by simp [hS0], List.Forall₂.cons hsx hall⟩
      simp [decodeHyps, hdec, hdecH]

/-- A theorem's stream accepted at a `Thm` step: it decodes to the theorem's statement;
the claimed conclusion is the conclusion under the arguments, and the subproofs popped
from the main stack prove the hypotheses under them. -/
theorem unify_thm {c : Ctx} {st : State} (hwf : StoreWF st.store) (hterms : StoreTerms c st.store)
    {terms : List TermDecl} (hprefix : ∀ (t : ℕ) (d : TermDecl), c.terms[t]? = some d → terms[t]? = some d)
    {args : List ℕ} {us : List UnifyCmd} {e : ℕ} {S S' : List El}
    (hu : Unify c st .thm (argHeap args) us [e] S [] S' []) :
    ∃ concl hl ps, decodeThm terms args.length us = some (concl, hl) ∧
      toSexpr st.store e = sexpr.subst (args.map (toSexpr st.store)) concl ∧
      S = ps.map El.proof ++ S' ∧
      List.Forall₂ (fun p h => toSexpr st.store p = sexpr.subst (args.map (toSexpr st.store)) h) ps hl := by
  set σ := args.map (toSexpr st.store) with hσdef
  obtain ⟨x, rest, heapS', ds', σ', H', hdec, hout, hsx, _, hrest, hdm, -⟩ :=
    (unify_decode hwf hterms hprefix args.length (2 * us.length + 2)).1 us (by omega) .thm e [] (argHeap args)
      (initHeap args.length) [] σ S [] S' [] hu (heapCorr_init _ _ _) (by simp [hσdef]) (fun j s h => by simp at h)
  have hds : ds' = [] := hdm (by decide)
  subst hds
  have hσ' : σ' = σ := prefix_eq_of_length hout.σpre (by rw [hout.σlen, hσdef]; simp)
  subst hσ'
  have hlen := (decode_length terms args.length (2 * us.length + 2)).1 us _ [] x rest heapS' [] hdec
  have hnf := noneFree_out hout (noneFree_init _)
  obtain ⟨hl, ps, hdecH, hS, hall⟩ := unify_thm_hyps hwf hterms hprefix args.length σ (by simp [hσdef])
    (2 * rest.length + 2) rest H' heapS' S [] S' [] le_rfl hrest (heapCorr_any hout.corr hnf) hnf
  refine ⟨x, hl, ps, ?_, hsx, hS, hall⟩
  simp [decodeThm, hdec, hdecH]

/-! ### The end of a theorem -/

theorem unify_end_hyps {c : Ctx} {st : State} (hwf : StoreWF st.store) (hterms : StoreTerms c st.store)
    {terms : List TermDecl} (hprefix : ∀ (t : ℕ) (d : TermDecl), c.terms[t]? = some d → terms[t]? = some d)
    (nargs : ℕ) (σ : List sexpr) (hσ : σ.length = nargs) : ∀ (fuel : ℕ) (rest : List UnifyCmd) (H : UHeap)
      (heapS : List (Option sexpr)) (S : List El) (hs : List ℕ) (S' : List El) (hs' : List ℕ),
      2 * rest.length + 2 ≤ fuel → Unify c st .thmEnd H rest [] S hs S' hs' → HeapCorr σ st.store H heapS [] →
      NoneFree heapS →
      ∃ hl, decodeHyps terms nargs fuel rest heapS [] = some hl ∧
        List.Forall₂ (fun p h => toSexpr st.store p = sexpr.subst σ h ∧ sexpr.VarsLt h σ.length) hs.reverse hl
  | 0, _, _, _, _, _, _, _, hf, _, _, _ => by omega
  | fuel + 1, rest, H, heapS, S, hs, S', hs', hf, hu, hcorr, hnf => by
    cases hu with
    | nil _ _ _ _ hnil =>
      have := hnil rfl
      subst this
      exact ⟨[], by simp [decodeHyps], List.Forall₂.nil⟩
    | hyp_end _ us' e' _ hs0 _ _ hu' =>
      simp only [List.length_cons] at hf
      obtain ⟨x, rest2, heapS2, ds2, σ2, H2, hdec, hout, hsx, hvl, hu2, hdm, -⟩ :=
        (unify_decode hwf hterms hprefix nargs fuel).1 us' (by omega) .thmEnd e' [] H heapS [] σ S hs0 S' hs' hu'
          (heapCorr_any hcorr hnf) (by simp [hσ]) (fun j s h => by simp at h)
      have hds2 : ds2 = [] := hdm (by decide)
      subst hds2
      have hσ2 : σ2 = σ := prefix_eq_of_length hout.σpre (by rw [hout.σlen, hσ]; simp)
      subst hσ2
      have hlen2 := (decode_length terms nargs fuel).1 us' heapS [] x rest2 heapS2 [] hdec
      obtain ⟨hl, hdecH, hall⟩ := unify_end_hyps hwf hterms hprefix nargs σ2 hσ fuel rest2 H2 heapS2 S hs0 S' hs'
        (by omega) hu2 (heapCorr_any hout.corr (noneFree_out hout hnf)) (noneFree_out hout hnf)
      refine ⟨x :: hl, ?_, ?_⟩
      · simp [decodeHyps, hdec, hdecH]
      · rw [List.reverse_append]
        exact List.Forall₂.cons ⟨hsx, hvl⟩ hall

theorem unify_end {c : Ctx} {st : State} (hwf : StoreWF st.store) (hterms : StoreTerms c st.store)
    {terms : List TermDecl} (hprefix : ∀ (t : ℕ) (d : TermDecl), c.terms[t]? = some d → terms[t]? = some d)
    {args : List ℕ} {us : List UnifyCmd} {e : ℕ} {hyps : List ℕ}
    (hu : Unify c st .thmEnd (argHeap args) us [e] [] hyps [] []) :
    ∃ concl hl, decodeThm terms args.length us = some (concl, hl) ∧
      toSexpr st.store e = sexpr.subst (args.map (toSexpr st.store)) concl ∧ sexpr.VarsLt concl args.length ∧
      List.Forall₂ (fun p h => toSexpr st.store p = sexpr.subst (args.map (toSexpr st.store)) h ∧
        sexpr.VarsLt h args.length) hyps.reverse hl := by
  set σ := args.map (toSexpr st.store) with hσdef
  obtain ⟨x, rest, heapS', ds', σ', H', hdec, hout, hsx, hvl, hrest, hdm, -⟩ :=
    (unify_decode hwf hterms hprefix args.length (2 * us.length + 2)).1 us (by omega) .thmEnd e [] (argHeap args)
      (initHeap args.length) [] σ [] hyps [] [] hu (heapCorr_init _ _ _) (by simp [hσdef]) (fun j s h => by simp at h)
  have hds : ds' = [] := hdm (by decide)
  subst hds
  have hσ' : σ' = σ := prefix_eq_of_length hout.σpre (by rw [hout.σlen, hσdef]; simp)
  subst hσ'
  have hnf := noneFree_out hout (noneFree_init _)
  obtain ⟨hl, hdecH, hall⟩ := unify_end_hyps hwf hterms hprefix args.length σ (by simp [hσdef])
    (2 * rest.length + 2) rest H' heapS' [] hyps [] [] le_rfl hrest (heapCorr_any hout.corr hnf) hnf
  have hσl : σ.length = args.length := by simp [hσdef]
  refine ⟨x, hl, ?_, hsx, by rw [← hσl]; exact hvl, ?_⟩
  · simp [decodeThm, hdec, hdecH]
  · rw [← hσl]
    exact hall

end Verifier
