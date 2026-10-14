/-
The context of a loaded declaration is well-formed (`ctx.ok`), and its return type's
dependencies are among its bound binders (`dep_type.ok`) — milestone V3, part b.
-/
import Verifier.Load

namespace Verifier

open mm0

theorem boundNumbers_split' {bs : List Binder} {j : ℕ} (hj : j ≤ bs.length) :
    boundNumbers bs = ((List.range j).filter fun i => decide (isBoundAt bs i)) ++
      ((List.range' j (bs.length - j)).filter fun i => decide (isBoundAt bs i)) := by
  rw [boundNumbers_eq, List.range_eq_range']
  have hsplit : List.range' 0 j ++ List.range' j (bs.length - j) = List.range' 0 bs.length := by
    have := @List.range'_append 0 j (bs.length - j) 1
    simp only [Nat.zero_add, Nat.one_mul] at this
    rw [this]
    congr 1
    omega
  rw [← hsplit, List.filter_append, ← List.range_eq_range']

/-- A bound-variable number below the count before `j` is a binder before `j`. -/
theorem bvVar_lt_of_countBefore {bs : List Binder} {j k : ℕ} (hj : j ≤ bs.length) (hk : k < countBefore bs j) :
    bvVar bs k < j := by
  have hlen : k < (boundNumbers bs).length := lt_of_lt_of_le hk (countBefore_le_nb bs hj)
  rw [bvVar_of_lt hlen]
  have hsplit := boundNumbers_split' hj
  have hk' : k < ((List.range j).filter fun i => decide (isBoundAt bs i)).length := hk
  have hget : (boundNumbers bs)[k] = ((List.range j).filter fun i => decide (isBoundAt bs i))[k] := by
    rw [List.getElem_of_eq hsplit, List.getElem_append_left hk']
  rw [hget]
  have hmem := List.getElem_mem hk'
  exact List.mem_range.1 (List.mem_of_mem_filter hmem)

theorem take_map_getElem? {bs : List Binder} {j x : ℕ} (hx : x < j) :
    ((bs.take j).map (Binder.toMm0 bs))[x]? = (bs[x]?).map (Binder.toMm0 bs) := by
  rw [List.getElem?_map, List.getElem?_take_of_lt hx]

/-- The prefixes of the context are well-formed. -/
theorem ctxOk_prefix {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms) {bs : List Binder}
    {st : State} (h : Loading c bs bs.length st) : ∀ j, j ≤ bs.length → ctx.ok E ((bs.take j).map (Binder.toMm0 bs))
  | 0, _ => by simp [ctx.ok.nil]
  | j + 1, hj => by
    have hjl : j < bs.length := hj
    have hb : bs[j]? = some bs[j] := List.getElem?_eq_getElem hjl
    rw [List.take_succ, hb]
    simp only [Option.toList, List.map_append, List.map_cons, List.map_nil]
    have ih := ctxOk_prefix hE h j (le_of_lt hjl)
    obtain ⟨h1, h2⟩ := h.wf j bs[j] hjl hb
    cases hbb : bs[j].bound with
    | true =>
      obtain ⟨_, sd, hsd, hstrict⟩ := h1 hbb
      rw [toMm0_bound hbb]
      exact ctx.ok.bound (hE.sorts _ _ hsd) (by simp [hstrict]) ih
    | false =>
      obtain ⟨hsort, hdeps⟩ := h2 hbb
      rw [toMm0_reg hbb]
      refine ctx.ok.reg ⟨?_, ?_⟩ ih
      · obtain ⟨sd, hsd⟩ : ∃ sd, c.sorts[bs[j].sort]? = some sd := ⟨_, List.getElem?_eq_getElem hsort⟩
        exact ⟨sd, hE.sorts _ _ hsd⟩
      · intro x hx
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
        have hlt := bvVar_lt_of_countBefore (le_of_lt hjl) (hdeps k hk)
        have hkn : k < (boundNumbers bs).length :=
          lt_of_lt_of_le (hdeps k hk) (countBefore_le_nb bs (le_of_lt hjl))
        obtain ⟨b', hb', hbb'⟩ := isBoundAt_iff.1 (boundNumbers_bound hkn)
        refine ⟨b'.sort, ?_⟩
        rw [take_map_getElem? hlt, bvVar_of_lt hkn, hb']
        simp [toMm0_bound hbb']

theorem ctxOk_loaded {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms) {bs : List Binder}
    {st : State} (h : Loading c bs bs.length st) : ctx.ok E (ctxOf bs []) := by
  have := ctxOk_prefix hE h bs.length (le_refl _)
  rw [List.take_length] at this
  simpa [ctxOf] using this

/-- A return type whose dependencies are among the bound binders is well-formed. -/
theorem depTypeOk_of {E : env} {c : Ctx} {allTerms : List TermDecl} (hE : EnvHas E c allTerms) {bs : List Binder}
    {ret : Binder} {sd : sort_data} (hsd : c.sorts[ret.sort]? = some sd)
    (hdeps : ∀ k ∈ ret.deps, k < (boundNumbers bs).length) :
    dep_type.ok E (ctxOf bs []) (depTypeOf bs ret) := by
  refine ⟨⟨sd, hE.sorts _ _ hsd⟩, ?_⟩
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
  have hkn := hdeps k hk
  obtain ⟨b', hb', hbb'⟩ := isBoundAt_iff.1 (boundNumbers_bound hkn)
  refine ⟨b'.sort, ?_⟩
  rw [bvVar_of_lt hkn, ctxOf_getElem_binder [] hb', toMm0_bound hbb']

end Verifier
