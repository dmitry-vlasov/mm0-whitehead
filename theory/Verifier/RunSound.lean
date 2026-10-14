/-
Every command keeps the stack invariant, and so does a run (milestone V3, part f).
-/
import Verifier.StepSound

namespace Verifier

open mm0
open Whitehead.Mmb (ProofCmd)

variable {W : World} {c : Ctx} {allTerms : List TermDecl} {bs : List Binder} {D : List ℕ}

theorem step_sound (hW : WorldOk W c allTerms bs D) {cmd : ProofCmd} {st st' : State} (hstep : Step c cmd st st')
    (hwf : StoreWF st.store) (hT : StoreTerms c st.store) (hext : st'.store <+: W.store) (hhyps : st'.hyps <+: W.hyps)
    (hS : SOk W st.store.length st.stack) (hH : HeapOk W st.store.length st.heap) :
    SOk W st'.store.length st'.stack ∧ HeapOk W st'.store.length st'.heap := by
  have hx := step_ext hstep
  have hpre : st.store <+: W.store := hx.store.trans hext
  have hle : st.store.length ≤ st'.store.length := hx.store.length_le
  have hWlen : st.store.length ≤ W.store.length := hpre.length_le
  cases hstep
  case term t save decl args S' ty hdecl hpop hargs hty =>
    obtain ⟨_, hSeq⟩ := popArgs_spec hpop
    rw [hSeq] at hS
    obtain ⟨_, hS'⟩ := SOk.drop_exprs args.reverse hS
    have hlt : st.store.length < (st.store ++ [Node.app ty t args]).length := by simp
    refine ⟨SOk.push hlt (SOk.mono (le_of_lt hlt) hS'), ?_⟩
    exact (hH.mono (le_of_lt hlt)).push_ite (el := El.expr st.store.length) hlt (fun a b h => by cases h) save
  case ref_el i el hnc hi =>
    have hel := hH el (List.mem_of_getElem? hi)
    exact ⟨SOk.mono hle (SOk.push hel.1 hS), hH.mono hle⟩
  case ref_conv i e1 e2 S hi hstk =>
    rw [hstk] at hS
    obtain ⟨_, _, hob⟩ := (hH _ (List.mem_of_getElem? hi)).1
    exact ⟨SOk.mono hle (hS.2 hob), hH.mono hle⟩
  case dummy s sd _ _ _ _ =>
    have hlt : st.store.length < (st.store ++ [Node.var ⟨s, true, {st.nextBv}⟩ st.nextVar]).length := by simp
    refine ⟨SOk.push hlt (SOk.mono (le_of_lt hlt) hS), ?_⟩
    exact (hH.mono (le_of_lt hlt)).push (el := El.expr st.store.length) hlt (fun a b h => by cases h)
  case thm t save decl e args S₁ S₂ hdef hdecl hpop S₃ hstk hargs hdis hU =>
    obtain ⟨he, hp, hS₃⟩ := thm_sound hW hwf hT hpre hdef hdecl hstk hpop hargs hdis hU hS
    exact ⟨SOk.push (el := El.proof e) ⟨he, hp⟩ hS₃, hH.push_ite (el := El.proof e) ⟨he, hp⟩ (fun a b h => by cases h) save⟩
  case hyp e S ty sd hdef hsd hprov hstk hty =>
    rw [hstk] at hS
    have he : e < st.store.length := hS.1
    have hS' := SOk.tail_of_not_ob hS (fun a b h => by cases h)
    have hmem : e ∈ W.hyps := hhyps.subset (List.mem_append_right _ (List.mem_singleton_self e))
    have hp : proof W.E W.Γ W.Hs (W.x e) := proof.hyp ⟨e, hmem, rfl⟩
    exact ⟨hS', hH.push (el := El.proof e) ⟨he, hp⟩ (fun a b h => by cases h)⟩
  case conv e1 e2 S hstk =>
    rw [hstk] at hS
    obtain ⟨⟨he2, hp2⟩, hrest⟩ := hS
    obtain ⟨he1, hS'⟩ := hrest trivial
    refine ⟨⟨⟨he1, he2⟩, fun hob => ⟨⟨he1, ?_⟩, fun _ => hS' trivial⟩⟩, hH⟩
    obtain ⟨s, hc, _, _⟩ := hob
    exact proof.conv (conv'.symm hc) hp2
  case refl e S hstk =>
    rw [hstk] at hS
    exact ⟨hS.2 (ObTrue.refl hW (lt_of_lt_of_le hS.1.1 hWlen)), hH⟩
  case symm e1 e2 S hstk =>
    rw [hstk] at hS
    exact ⟨⟨⟨hS.1.2, hS.1.1⟩, fun hob => hS.2 hob.symm⟩, hH⟩
  case cong e1 e2 S ty1 ty2 t args1 args2 hlen hstk hn1 hn2 =>
    rw [hstk] at hS
    refine ⟨?_, hH⟩
    rw [zipWith_coConv_eq]
    refine SOk.of_obs _ (fun ab hab => ?_) (fun hall => hS.2 (cong_ob hW hpre hn1 hn2 fun i h1 h2 => ?_))
    · have h1 := List.of_mem_zip hab
      have hl1 := (List.getElem?_eq_some_iff.1 hn1).1
      have hl2 := (List.getElem?_eq_some_iff.1 hn2).1
      exact ⟨lt_trans (hwf e1 ty1 t args1 hn1 _ h1.1) hl1, lt_trans (hwf e2 ty2 t args2 hn2 _ h1.2) hl2⟩
    · have hmem : (args1[i], args2[i]) ∈ args1.zip args2 := by
        have hi : i < (args1.zip args2).length := by simp; omega
        rw [← List.getElem_zip (i := i) (h := hi)]
        exact List.getElem_mem _
      exact hall _ hmem
  case unfold e e' t ty args decl us S e2 hd hus hstk hn hU =>
    rw [hstk] at hS
    obtain ⟨he2, hrest⟩ := hS
    obtain ⟨⟨he, he'⟩, hrest'⟩ := hrest trivial
    exact ⟨⟨⟨he2, he'⟩, fun hob => hrest' (unfold_ob hW hwf hT hpre hn hd hus hU he2 hob)⟩, hH⟩
  case convCut e1 e2 S hstk =>
    rw [hstk] at hS
    obtain ⟨⟨h1, h2⟩, hrest⟩ := hS
    exact ⟨⟨⟨h1, h2⟩, fun hob => ⟨⟨h1, h2, hob⟩, fun _ => hrest hob⟩⟩, hH⟩
  case convSave e1 e2 S hstk =>
    rw [hstk] at hS
    obtain ⟨hcv, hrest⟩ := hS
    exact ⟨hrest trivial, hH.push hcv (fun a b h => by cases h)⟩
  case save el S hnc hstk =>
    rw [hstk] at hS
    have hnc' : ∀ a b, el ≠ El.coConv a b := hnc
    exact ⟨by rw [hstk]; exact hS, hH.push hS.1 hnc'⟩

theorem run_sound (hW : WorldOk W c allTerms bs D) (hbwf : BindersWF bs) :
    ∀ {cmds : List ProofCmd} {st st' : State} {ds : List ℕ}, Run c cmds st st' →
      StateOk W.E bs ds c.isDef st → StoreTerms c st.store → st'.store <+: W.store → st'.hyps <+: W.hyps →
      SOk W st.store.length st.stack → HeapOk W st.store.length st.heap →
      SOk W st'.store.length st'.stack ∧ HeapOk W st'.store.length st'.heap
  | _, _, _, _, Run.nil _, _, _, _, _, hS, hH => ⟨hS, hH⟩
  | _, _, _, ds, Run.cons _ _ _ st₁ _ hstep hrun, hst, hT, hext, hhyps, hS, hH => by
    have hx := run_ext hrun
    obtain ⟨ds₁, _, hst₁⟩ := step_stateOk hW.env hbwf hstep hst
    obtain ⟨hS₁, hH₁⟩ := step_sound hW hstep hst.store.wf hT (hx.store.trans hext) (hx.hyps.trans hhyps) hS hH
    exact run_sound hW hbwf hrun hst₁ (storeTerms_step hstep hT) hext hhyps hS₁ hH₁

end Verifier
