/-
A file the machine accepts proves the environment it declares (milestone V3): the
statements in order, each checked against the environment of those before it.
-/
import Verifier.WF

namespace Verifier

open mm0

def ctxAt (f : File) (ns nt nh : ℕ) (b : Bool) : Ctx := ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, b⟩

theorem EnvHas.withDef {E : env} {f : File} {ns nt nh : ℕ} {b : Bool} (h : EnvHas E (ctxAt f ns nt nh false) f.terms) :
    EnvHas E (ctxAt f ns nt nh b) f.terms :=
  ⟨h.sorts, h.sorts_unique, h.terms, h.terms_unique, h.thms, h.terms_prefix, h.terms_wf, h.defs_ok⟩

/-! ### Lists -/

theorem take_succ_cases {α : Type} {l : List α} {n i : ℕ} {x : α} (h : (l.take (n + 1))[i]? = some x) :
    (l.take n)[i]? = some x ∨ (i = n ∧ l[n]? = some x) := by
  rw [List.getElem?_take] at h
  split at h
  · rename_i hi
    by_cases hin : i < n
    · left
      rw [List.getElem?_take, ite_eq_left hin]
      exact h
    · right
      have : i = n := by omega
      subst this
      exact ⟨rfl, h⟩
  · cases h

theorem take_mono {α : Type} {l : List α} {n i : ℕ} {x : α} (h : (l.take n)[i]? = some x) : (l.take (n + 1))[i]? = some x := by
  rw [List.getElem?_take] at h ⊢
  by_cases hi : i < n
  · rw [if_pos hi] at h
    rw [if_pos (by omega)]
    exact h
  · rw [if_neg hi] at h
    cases h

theorem take_self {α : Type} {l : List α} {n : ℕ} {x : α} (h : l[n]? = some x) : (l.take (n + 1))[n]? = some x := by
  rw [List.getElem?_take, if_pos (by omega)]
  exact h

theorem take_prefix {α : Type} {l : List α} {n i : ℕ} {x : α} (h : (l.take n)[i]? = some x) : l[i]? = some x := by
  rw [List.getElem?_take] at h
  split at h
  · exact h
  · cases h

/-! ### The environment extended -/

theorem sub_append (E : env) (d : decl) : ∀ x ∈ E, x ∈ E ++ [d] := fun _ h => List.mem_append_left _ h

theorem get_term_append {E : env} {d : decl} {t : term_id} {a : ctx} {r : dep_type} {o : Option (List sort_id × sexpr)}
    (h : (E ++ [d]).get_term t a r o) :
    E.get_term t a r o ∨ (d = decl.term t a r ∧ o = none) ∨ d = decl.defn t a r o := by
  cases h with
  | term hm =>
    rcases List.mem_append.1 hm with hm | hm
    · exact Or.inl (env.get_term.term hm)
    · simp only [List.mem_singleton] at hm
      exact Or.inr (Or.inl ⟨hm.symm, rfl⟩)
  | defn hm =>
    rcases List.mem_append.1 hm with hm | hm
    · exact Or.inl (env.get_term.defn hm)
    · simp only [List.mem_singleton] at hm
      exact Or.inr (Or.inr hm.symm)

theorem get_thm_mono {E : env} {d : decl} {a : ctx} {hs : List sexpr} {r : sexpr} (h : E.get_thm a hs r) :
    (E ++ [d]).get_thm a hs r := h.imp (List.mem_append_left _) (List.mem_append_left _)

/-- The invariant of the prefix: the environment of the statements so far, with what the
tables declare, and its proof. -/
structure PInv (f : File) (E : env) (ns nt nh : ℕ) : Prop where
  has : EnvHas E (ctxAt f ns nt nh false) f.terms
  pf : env.proof' E
  wf : env.ok E

/-- A new declaration that is not a term or def keeps the term clauses. -/
theorem envHas_terms_keep {E : env} {f : File} {ns nt nh : ℕ} (h : EnvHas E (ctxAt f ns nt nh false) f.terms) {d : decl}
    (hd : ∀ t a r o, d ≠ decl.term t a r ∧ d ≠ decl.defn t a r o) :
    (∀ (t : ℕ) (dd : TermDecl), (ctxAt f ns nt nh false).terms[t]? = some dd →
      ∃ o, (E ++ [d]).get_term t (dd.args.map (Binder.toMm0 dd.args)) (depTypeOf dd.args dd.ret) o ∧
        ∀ us, dd.defn = some us → ∃ v ds, decodeDef f.terms dd.args.length us = some (v, ds) ∧ o = some (ds, v)) ∧
    (∀ t a r o, (E ++ [d]).get_term t a r o → ∃ dd : TermDecl, (ctxAt f ns nt nh false).terms[t]? = some dd ∧
      a = dd.args.map (Binder.toMm0 dd.args) ∧ r = depTypeOf dd.args dd.ret) := by
  refine ⟨fun t dd hdd => ?_, fun t a r o hg => ?_⟩
  · obtain ⟨o, hg, ho⟩ := h.terms t dd hdd
    exact ⟨o, get_term_mono (sub_append E d) hg, ho⟩
  · rcases get_term_append hg with hg | ⟨rfl, _⟩ | rfl
    · exact h.terms_unique t a r o hg
    · exact absurd rfl (hd t a r o).1
    · exact absurd rfl (hd t a r o).2

theorem inv_sort {f : File} {E : env} {ns nt nh : ℕ} (h : PInv f E ns nt nh) {sd : sort_data} (hsd : f.sorts[ns]? = some sd) :
    PInv f (E ++ [decl.sort ns sd]) (ns + 1) nt nh := by
  have hE := h.has
  obtain ⟨hterms, hunique⟩ := envHas_terms_keep hE (d := decl.sort ns sd) (fun _ _ _ _ => ⟨by simp, by simp⟩)
  refine ⟨⟨fun s sd' hs => ?_, fun s sd' hs => ?_, hterms, hunique, fun h' d' hd' => ?_, hE.terms_prefix,
    hE.terms_wf, fun t d' us v ds h1 h2 h3 => ok'_env_mono (sub_append E _) (hE.defs_ok t d' us v ds h1 h2 h3)⟩,
    env.proof'.sort h.pf, env.ok.cons h.wf trivial⟩
  · rcases take_succ_cases hs with hs | ⟨rfl, hs⟩
    · exact List.mem_append_left _ (hE.sorts s sd' hs)
    · rw [hsd] at hs
      cases hs
      exact List.mem_append_right _ (List.mem_singleton_self _)
  · rcases List.mem_append.1 hs with hs | hs
    · exact take_mono (hE.sorts_unique s sd' hs)
    · simp only [List.mem_singleton, decl.sort.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      exact take_self hsd
  · obtain ⟨concl, hs, hdec, hg⟩ := hE.thms h' d' hd'
    exact ⟨concl, hs, hdec, get_thm_mono hg⟩

theorem inv_thm {f : File} {E : env} {ns nt nh : ℕ} (h : PInv f E ns nt nh) {d : ThmDecl} (hd : f.thms[nh]? = some d)
    {concl : sexpr} {hl : List sexpr} (hdec : decodeThm f.terms d.args.length d.unify = some (concl, hl)) {dd : decl}
    (hdd : dd = decl.ax (d.args.map (Binder.toMm0 d.args)) hl concl ∨ dd = decl.thm (d.args.map (Binder.toMm0 d.args)) hl concl)
    (hproof : env.proof' (E ++ [dd])) (hok : decl.ok E dd) :
    PInv f (E ++ [dd]) ns nt (nh + 1) := by
  have hE := h.has
  obtain ⟨hterms, hunique⟩ := envHas_terms_keep hE (d := dd)
    (fun _ _ _ _ => by rcases hdd with rfl | rfl <;> exact ⟨by simp, by simp⟩)
  refine ⟨⟨fun s sd' hs => List.mem_append_left _ (hE.sorts s sd' hs), fun s sd' hs => ?_, hterms, hunique,
    fun h' d' hd' => ?_, hE.terms_prefix, hE.terms_wf,
    fun t d' us v ds h1 h2 h3 => ok'_env_mono (sub_append E _) (hE.defs_ok t d' us v ds h1 h2 h3)⟩, hproof,
    env.ok.cons h.wf hok⟩
  · rcases List.mem_append.1 hs with hs | hs
    · exact hE.sorts_unique s sd' hs
    · simp only [List.mem_singleton] at hs
      rcases hdd with rfl | rfl <;> cases hs
  · rcases take_succ_cases hd' with hd' | ⟨rfl, hd'⟩
    · obtain ⟨concl', hs, hdec', hg⟩ := hE.thms h' d' hd'
      exact ⟨concl', hs, hdec', get_thm_mono hg⟩
    · rw [hd] at hd'
      cases hd'
      refine ⟨concl, hl, hdec, ?_⟩
      rcases hdd with rfl | rfl
      · exact Or.inl (List.mem_append_right _ (List.mem_singleton_self _))
      · exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))

theorem inv_term {f : File} {E : env} {ns nt nh : ℕ} (h : PInv f E ns nt nh) {d : TermDecl} (hd : f.terms[nt]? = some d)
    {b : Bool} (hfacts : TermFacts E (ctxAt f ns nt nh b) f.terms d) {dd : decl} (hdd : termDeclOf f nt = some dd)
    (hok : decl.ok E dd) :
    PInv f (E ++ [dd]) ns (nt + 1) nh := by
  have hE := h.has
  -- the new declaration
  have hshape : (d.defn = none ∧ dd = decl.term nt (d.args.map (Binder.toMm0 d.args)) (depTypeOf d.args d.ret)) ∨
      ∃ us v ds, d.defn = some us ∧ decodeDef f.terms d.args.length us = some (v, ds) ∧
        dd = decl.defn nt (d.args.map (Binder.toMm0 d.args)) (depTypeOf d.args d.ret) (some (ds, v)) := by
    unfold termDeclOf at hdd
    rw [hd] at hdd
    simp only [Option.bind_some] at hdd
    cases hdef : d.defn with
    | none =>
      rw [hdef] at hdd
      simp only [Option.some.injEq] at hdd
      exact Or.inl ⟨rfl, hdd.symm⟩
    | some us =>
      rw [hdef] at hdd
      simp only [Option.map_eq_some_iff] at hdd
      obtain ⟨⟨v, ds⟩, hdec, rfl⟩ := hdd
      exact Or.inr ⟨us, v, ds, rfl, hdec, rfl⟩
  have hnotsort : ∀ s sd, dd ≠ decl.sort s sd := by
    intro s sd h'
    rcases hshape with ⟨_, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> cases h'
  have hnotthm : ∀ a hs r, dd ≠ decl.ax a hs r ∧ dd ≠ decl.thm a hs r := by
    intro a hs r
    rcases hshape with ⟨_, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> exact ⟨by simp, by simp⟩
  refine ⟨⟨fun s sd' hs => List.mem_append_left _ (hE.sorts s sd' hs), fun s sd' hs => ?_, fun t d' hd' => ?_,
    fun t a r o hg => ?_, fun h' d' hd' => ?_, fun t d' hd' => take_prefix hd', fun t d' hd' => ?_,
    fun t d' us v ds h1 h2 h3 => ?_⟩, ?_, env.ok.cons h.wf hok⟩
  · rcases List.mem_append.1 hs with hs | hs
    · exact hE.sorts_unique s sd' hs
    · simp only [List.mem_singleton] at hs
      exact absurd hs.symm (hnotsort s sd')
  · rcases take_succ_cases hd' with hd' | ⟨rfl, hd'⟩
    · obtain ⟨o, hg, ho⟩ := hE.terms t d' hd'
      exact ⟨o, get_term_mono (sub_append E _) hg, ho⟩
    · rw [hd] at hd'
      cases hd'
      rcases hshape with ⟨hnone, rfl⟩ | ⟨us, v, ds, hsome, hdec, rfl⟩
      · refine ⟨none, env.get_term.term (List.mem_append_right _ (List.mem_singleton_self _)), fun us h' => ?_⟩
        rw [hnone] at h'
        cases h'
      · refine ⟨some (ds, v), env.get_term.defn (List.mem_append_right _ (List.mem_singleton_self _)), fun us' h' => ?_⟩
        rw [hsome] at h'
        cases h'
        exact ⟨v, ds, hdec, rfl⟩
  · rcases get_term_append hg with hg | ⟨heq, _⟩ | heq
    · obtain ⟨d', hd', ha, hr⟩ := hE.terms_unique t a r o hg
      exact ⟨d', take_mono hd', ha, hr⟩
    · rcases hshape with ⟨_, rfl⟩ | ⟨_, _, _, _, _, rfl⟩
      · simp only [decl.term.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact ⟨d, take_self hd, rfl, rfl⟩
      · cases heq
    · rcases hshape with ⟨_, rfl⟩ | ⟨_, _, _, _, _, rfl⟩
      · cases heq
      · simp only [decl.defn.injEq] at heq
        obtain ⟨rfl, rfl, rfl, _⟩ := heq
        exact ⟨d, take_self hd, rfl, rfl⟩
  · obtain ⟨concl, hs, hdec, hg⟩ := hE.thms h' d' hd'
    refine ⟨concl, hs, hdec, ?_⟩
    exact get_thm_mono hg
  · rcases take_succ_cases hd' with hd' | ⟨rfl, hd'⟩
    · exact hE.terms_wf t d' hd'
    · rw [hd] at hd'
      cases hd'
      exact ⟨hfacts.wf, hfacts.ret_deps⟩
  · rcases take_succ_cases h1 with h1 | ⟨rfl, h1⟩
    · exact ok'_env_mono (sub_append E _) (hE.defs_ok t d' us v ds h1 h2 h3)
    · rw [hd] at h1
      cases h1
      obtain ⟨v', ds', hdec', hok⟩ := hfacts.value us h2
      rw [h3] at hdec'
      cases hdec'
      exact ok'_env_mono (sub_append E _) hok
  · rcases hshape with ⟨_, rfl⟩ | ⟨_, v, ds, _, _, rfl⟩
    · exact env.proof'.term h.pf
    · exact env.proof'.defn h.pf

/-! ### The statements -/

/-- `term_ok` of a new term or def: its number is fresh, its binders and return type
well-formed, its result sort not pure. -/
theorem term_ok_of {f : File} {E : env} {ns nt nh : ℕ} (h : PInv f E ns nt nh) {b : Bool} {dc : TermDecl}
    (hctx : ctx.ok E (ctxOf dc.args [])) (hdep : dep_type.ok E (ctxOf dc.args []) (depTypeOf dc.args dc.ret))
    (hfacts : TermFacts E (ctxAt f ns nt nh b) f.terms dc) :
    term_ok E nt (dc.args.map (Binder.toMm0 dc.args)) (depTypeOf dc.args dc.ret) := by
  have hargs : dc.args.map (Binder.toMm0 dc.args) = ctxOf dc.args [] := by simp [ctxOf]
  rw [hargs]
  refine ⟨fun ⟨a, r, o, hg⟩ => ?_, hctx, hdep, ?_⟩
  · obtain ⟨d, hd, _⟩ := h.has.terms_unique nt a r o hg
    simp [ctxAt, List.getElem?_take] at hd
  · obtain ⟨sd, hsd, hpure⟩ := hfacts.ret_sort
    exact ⟨sd, h.has.sorts _ _ hsd, by simp [hpure]⟩

theorem stmts_valid {f : File} : ∀ {ss : List Stmt} {ns nt nh : ℕ}, Stmts f ss ns nt nh → ∀ E, PInv f E ns nt nh →
    ∃ rest, toEnvAux f ss ns nt nh = some rest ∧ env.ok (E ++ rest) ∧ env.proof' (E ++ rest) := by
  intro ss ns nt nh hS
  induction hS with
  | nil => intro E h; exact ⟨[], rfl, by simpa using h.wf, by simpa using h.pf⟩
  | sort ss ns nt nh hns _ ih =>
    intro E h
    have hsd : f.sorts[ns]? = some f.sorts[ns] := List.getElem?_eq_getElem hns
    obtain ⟨rest, hrest, hp⟩ := ih _ (inv_sort h hsd)
    refine ⟨decl.sort ns f.sorts[ns] :: rest, ?_, by simpa [List.append_assoc] using hp.1,
      by simpa [List.append_assoc] using hp.2⟩
    simp [toEnvAux, hsd, hrest]
  | term ss ns nt nh dc hd hnone hok _ ih =>
    intro E h
    have hfacts := term_stmt_sound h.has (fun h' => by rw [hnone] at h'; cases h') hok
    have hwf := term_stmt_wf h.has (fun h' => by rw [hnone] at h'; cases h') hok
    have hdd : termDeclOf f nt = some (decl.term nt (dc.args.map (Binder.toMm0 dc.args)) (depTypeOf dc.args dc.ret)) := by
      unfold termDeclOf
      rw [hd]
      simp [hnone]
    obtain ⟨rest, hrest, hp⟩ := ih _ (inv_term h hd hfacts hdd (term_ok_of h hwf.1 hwf.2.1 hfacts))
    refine ⟨_ :: rest, ?_, by simpa [List.append_assoc] using hp.1,
      by simpa [List.append_assoc] using hp.2⟩
    simp [toEnvAux, hdd, hrest]
  | defn ss ns nt nh dc isLocal body hd hsome hok _ ih =>
    intro E h
    have hfacts := term_stmt_sound (h.has.withDef (b := true)) (fun _ => rfl) hok
    obtain ⟨us, hus⟩ := Option.isSome_iff_exists.1 hsome
    obtain ⟨v, ds, hdec, _⟩ := hfacts.value us hus
    have hdd : termDeclOf f nt = some (decl.defn nt (dc.args.map (Binder.toMm0 dc.args))
        (depTypeOf dc.args dc.ret) (some (ds, v))) := by
      unfold termDeclOf
      rw [hd]
      simp [hus, hdec]
    have hwf := term_stmt_wf (h.has.withDef (b := true)) (fun _ => rfl) hok
    obtain ⟨hctxv, hfree⟩ := hwf.2.2 us hus v ds hdec
    obtain ⟨v', ds', hdec', hvok⟩ := hfacts.value us hus
    rw [hdec] at hdec'
    simp only [Option.some.injEq, Prod.mk.injEq] at hdec'
    obtain ⟨rfl, rfl⟩ := hdec'
    have hdok : decl.ok E (decl.defn nt (dc.args.map (Binder.toMm0 dc.args)) (depTypeOf dc.args dc.ret) (some (ds, v))) := by
      refine ⟨term_ok_of h hwf.1 hwf.2.1 hfacts, ?_, ?_, fun x hx => Or.inl (hfree x ?_)⟩
      · simpa [append_dummies, ctxOf] using hctxv
      · simpa [append_dummies, ctxOf, depTypeOf] using hvok
      · simpa [append_dummies, ctxOf] using hx
    obtain ⟨rest, hrest, hp⟩ := ih _ (inv_term h hd hfacts hdd hdok)
    refine ⟨_ :: rest, ?_, by simpa [List.append_assoc] using hp.1,
      by simpa [List.append_assoc] using hp.2⟩
    simp [toEnvAux, hdd, hrest]
  | ax ss ns nt nh dc body hd hok _ ih =>
    intro E h
    obtain ⟨concl, hl, hdec, _⟩ := thm_stmt_sound h.has rfl hok
    have hdd : thmDeclOf f true nh = some (decl.ax (dc.args.map (Binder.toMm0 dc.args)) hl concl) := by
      unfold thmDeclOf
      rw [hd]
      simp [hdec]
    obtain ⟨rest, hrest, hp⟩ := ih _ (inv_thm h hd hdec (Or.inl rfl) (env.proof'.ax h.pf) (thm_stmt_wf h.has rfl hok hdec))
    refine ⟨_ :: rest, ?_, by simpa [List.append_assoc] using hp.1,
      by simpa [List.append_assoc] using hp.2⟩
    simp [toEnvAux, hdd, hrest]
  | thm ss ns nt nh dc isLocal body hd hok _ ih =>
    intro E h
    obtain ⟨concl, hl, hdec, hpr⟩ := thm_stmt_sound h.has rfl hok
    obtain ⟨D, hctx, hproof⟩ := hpr rfl
    have hdd : thmDeclOf f false nh = some (decl.thm (dc.args.map (Binder.toMm0 dc.args)) hl concl) := by
      unfold thmDeclOf
      rw [hd]
      simp [hdec]
    obtain ⟨rest, hrest, hp⟩ := ih _ (inv_thm h hd hdec (Or.inr rfl) (env.proof'.thm hctx hproof h.pf)
      (thm_stmt_wf h.has rfl hok hdec))
    refine ⟨_ :: rest, ?_, by simpa [List.append_assoc] using hp.1,
      by simpa [List.append_assoc] using hp.2⟩
    simp [toEnvAux, hdd, hrest]

/-- **Soundness of the machine** (milestone V3): a proof file the machine accepts
declares an environment, and every theorem of it is proved in the environment of the
statements before it — `env.proof'` of the formal semantics. -/
theorem file_valid {f : File} (h : FileOk f) : ∃ E, toEnv f = some E ∧ env.ok E ∧ env.proof' E := by
  have hinv : PInv f [] 0 0 0 :=
    ⟨⟨fun s sd h => by simp [ctxAt] at h, fun s sd h => by simp [env.get_sd] at h,
      fun t d h => by simp [ctxAt] at h, fun t a r o h => by cases h <;> simp_all,
      fun h' d h => by simp [ctxAt] at h, fun t d h => by simp [ctxAt] at h,
      fun t d h => by simp [ctxAt] at h, fun t d us v ds h => by simp [ctxAt] at h⟩, env.proof'.nil, env.ok.nil⟩
  obtain ⟨rest, hrest, hok, hp⟩ := stmts_valid h [] hinv
  exact ⟨rest, hrest, by simpa using hok, by simpa using hp⟩

theorem file_sound {f : File} (h : FileOk f) : ∃ E, toEnv f = some E ∧ env.proof' E := by
  obtain ⟨E, hE, _, hp⟩ := file_valid h
  exact ⟨E, hE, hp⟩

end Verifier
