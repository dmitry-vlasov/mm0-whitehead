/-
The numbering of bound variables (milestone V3, part b): the positions of the bound
binders, the map from a bound-variable number to its variable, the context of a
declaration, and the number `LoadArgs` gives a bound binder — the count of bound
binders before it.
-/
import Verifier.Translate

namespace Verifier

open mm0

/-- Whether the binder at position `i` is bound. -/
def isBoundAt (bs : List Binder) (i : ℕ) : Prop := (bs[i]?.map fun b : Binder => b.bound) = some true

instance (bs : List Binder) (i : ℕ) : Decidable (isBoundAt bs i) := by unfold isBoundAt; infer_instance

theorem isBoundAt_iff {bs : List Binder} {i : ℕ} : isBoundAt bs i ↔ ∃ b, bs[i]? = some b ∧ b.bound = true := by
  unfold isBoundAt
  constructor
  · intro h
    cases hb : bs[i]? with
    | none => rw [hb] at h; simp at h
    | some b =>
      rw [hb] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨b, rfl, h⟩
  · rintro ⟨b, hb, hbb⟩
    simp [hb, hbb]

theorem boundNumbers_eq (bs : List Binder) : boundNumbers bs = (List.range bs.length).filter fun i => decide (isBoundAt bs i) := by
  unfold boundNumbers isBoundAt
  rfl

theorem mem_boundNumbers {bs : List Binder} {i : ℕ} : i ∈ boundNumbers bs ↔ i < bs.length ∧ isBoundAt bs i := by
  rw [boundNumbers_eq]
  simp [List.mem_filter, List.mem_range]

theorem boundNumbers_sorted (bs : List Binder) : (boundNumbers bs).Pairwise (· < ·) := by
  rw [boundNumbers_eq]
  exact (List.pairwise_lt_range).filter _

theorem boundNumbers_nodup (bs : List Binder) : (boundNumbers bs).Nodup :=
  (boundNumbers_sorted bs).imp fun h => Nat.ne_of_lt h

theorem boundNumbers_lt {bs : List Binder} {k : ℕ} (hk : k < (boundNumbers bs).length) :
    (boundNumbers bs)[k] < bs.length :=
  (mem_boundNumbers.1 (List.getElem_mem hk)).1

theorem boundNumbers_bound {bs : List Binder} {k : ℕ} (hk : k < (boundNumbers bs).length) :
    isBoundAt bs (boundNumbers bs)[k] :=
  (mem_boundNumbers.1 (List.getElem_mem hk)).2

/-! ### The variable of a number -/

theorem bvVar_of_lt {bs : List Binder} {k : ℕ} (hk : k < (boundNumbers bs).length) :
    bvVar bs k = (boundNumbers bs)[k] := by
  unfold bvVar
  rw [dite_eq_left hk]

theorem bvVar_of_ge {bs : List Binder} {k : ℕ} (hk : ¬ k < (boundNumbers bs).length) :
    bvVar bs k = bs.length + (k - (boundNumbers bs).length) := by
  unfold bvVar
  rw [dite_eq_right hk]

theorem bvVar_lt_of_lt {bs : List Binder} {k : ℕ} (hk : k < (boundNumbers bs).length) : bvVar bs k < bs.length := by
  rw [bvVar_of_lt hk]
  exact boundNumbers_lt hk

theorem bvVar_injective (bs : List Binder) {k k' : ℕ} (h : bvVar bs k = bvVar bs k') : k = k' := by
  by_cases hk : k < (boundNumbers bs).length <;> by_cases hk' : k' < (boundNumbers bs).length
  · rw [bvVar_of_lt hk, bvVar_of_lt hk'] at h
    exact ((boundNumbers_nodup bs).getElem_inj_iff).1 h
  · rw [bvVar_of_lt hk, bvVar_of_ge hk'] at h
    have := boundNumbers_lt hk
    omega
  · rw [bvVar_of_ge hk, bvVar_of_lt hk'] at h
    have := boundNumbers_lt hk'
    omega
  · rw [bvVar_of_ge hk, bvVar_of_ge hk'] at h
    omega

theorem bvVar_lt {bs : List Binder} {ds : List ℕ} {k : ℕ} (hk : k < (boundNumbers bs).length + ds.length) :
    bvVar bs k < bs.length + ds.length := by
  by_cases h : k < (boundNumbers bs).length
  · have := bvVar_lt_of_lt h
    omega
  · rw [bvVar_of_ge h]
    omega

/-! ### The context of a declaration -/

theorem ctxOf_length (bs : List Binder) (ds : List ℕ) : (ctxOf bs ds).length = bs.length + ds.length := by
  simp [ctxOf]

theorem ctxOf_append (bs : List Binder) (ds : List ℕ) (s : ℕ) :
    ctxOf bs (ds ++ [s]) = ctxOf bs ds ++ [binder.bound s] := by
  simp [ctxOf]

theorem ctxOf_getElem_binder {bs : List Binder} (ds : List ℕ) {i : ℕ} {b : Binder} (hb : bs[i]? = some b) :
    (ctxOf bs ds)[i]? = some (Binder.toMm0 bs b) := by
  unfold ctxOf
  rw [List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.1 hb).1), List.getElem?_map, hb]
  rfl

theorem ctxOf_getElem_dummy (bs : List Binder) {ds : List ℕ} {d : ℕ} {s : ℕ} (hd : ds[d]? = some s) :
    (ctxOf bs ds)[bs.length + d]? = some (binder.bound s) := by
  unfold ctxOf
  rw [List.getElem?_append_right (by simp), List.getElem?_map]
  simp [hd]

theorem toMm0_bound {bs : List Binder} {b : Binder} (hb : b.bound = true) : Binder.toMm0 bs b = binder.bound b.sort := by
  simp [Binder.toMm0, hb]

theorem toMm0_reg {bs : List Binder} {b : Binder} (hb : b.bound = false) :
    Binder.toMm0 bs b = binder.reg b.sort (b.deps.image (bvVar bs)) := by
  simp [Binder.toMm0, hb]

/-- The sort of bound-variable number `k`. -/
def bvSort (bs : List Binder) (ds : List ℕ) (k : ℕ) : ℕ :=
  if h : k < (boundNumbers bs).length then ((bs[(boundNumbers bs)[k]]?).map fun b : Binder => b.sort).getD 0
  else ds.getD (k - (boundNumbers bs).length) 0

theorem ctxOf_bvVar {bs : List Binder} {ds : List ℕ} {k : ℕ} (hk : k < (boundNumbers bs).length + ds.length) :
    (ctxOf bs ds)[bvVar bs k]? = some (binder.bound (bvSort bs ds k)) := by
  by_cases h : k < (boundNumbers bs).length
  · rw [bvVar_of_lt h]
    obtain ⟨b, hb, hbb⟩ := isBoundAt_iff.1 (boundNumbers_bound h)
    rw [ctxOf_getElem_binder ds hb, toMm0_bound hbb]
    unfold bvSort
    rw [dite_eq_left h, hb]
    rfl
  · rw [bvVar_of_ge h]
    have hd : k - (boundNumbers bs).length < ds.length := by omega
    rw [ctxOf_getElem_dummy bs (List.getElem?_eq_getElem hd)]
    unfold bvSort
    rw [dite_eq_right h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd]
    rfl

/-- A variable of the context that is bound is the variable of a number. -/
theorem bvVar_of_bound {bs : List Binder} {ds : List ℕ} {v : ℕ} {s : ℕ} (hv : (ctxOf bs ds)[v]? = some (binder.bound s)) :
    ∃ k, k < (boundNumbers bs).length + ds.length ∧ bvVar bs k = v := by
  have hlen : v < bs.length + ds.length := by
    have := (List.getElem?_eq_some_iff.1 hv).1
    rwa [ctxOf_length] at this
  by_cases hb : v < bs.length
  · -- a binder, bound
    obtain ⟨b, hb'⟩ : ∃ b, bs[v]? = some b := ⟨bs[v], List.getElem?_eq_getElem hb⟩
    rw [ctxOf_getElem_binder ds hb'] at hv
    have hbb : b.bound = true := by
      by_contra h
      rw [toMm0_reg (Bool.eq_false_iff.2 h)] at hv
      simp at hv
    have hmem : v ∈ boundNumbers bs := mem_boundNumbers.2 ⟨hb, isBoundAt_iff.2 ⟨b, hb', hbb⟩⟩
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hmem
    exact ⟨k, by omega, by rw [bvVar_of_lt hk]; exact hkv⟩
  · refine ⟨(boundNumbers bs).length + (v - bs.length), by omega, ?_⟩
    rw [bvVar_of_ge (by omega)]
    omega

/-! ### The count before a position -/

/-- The number of bound binders before position `i`: the number `LoadArgs` gives the
binder there if it is bound. -/
def countBefore (bs : List Binder) (i : ℕ) : ℕ :=
  ((List.range i).filter fun j => decide (isBoundAt bs j)).length

theorem boundNumbers_split {bs : List Binder} {i : ℕ} (hi : i < bs.length) (hb : isBoundAt bs i) :
    boundNumbers bs = ((List.range i).filter fun j => decide (isBoundAt bs j)) ++
      i :: ((List.range' (i + 1) (bs.length - i - 1)).filter fun j => decide (isBoundAt bs j)) := by
  rw [boundNumbers_eq, List.range_eq_range']
  have hsplit : List.range' 0 i ++ List.range' i (bs.length - i) = List.range' 0 bs.length := by
    have := @List.range'_append 0 i (bs.length - i) 1
    simp only [Nat.zero_add, Nat.one_mul] at this
    rw [this]
    congr 1
    omega
  rw [← hsplit, List.filter_append, ← List.range_eq_range']
  congr 1
  have hlen : bs.length - i = (bs.length - i - 1) + 1 := by omega
  rw [hlen, List.range'_succ, List.filter_cons_of_pos (by simpa using hb)]
  simp

theorem countBefore_lt {bs : List Binder} {i : ℕ} (hi : i < bs.length) (hb : isBoundAt bs i) :
    countBefore bs i < (boundNumbers bs).length := by
  rw [boundNumbers_split hi hb, List.length_append, List.length_cons]
  unfold countBefore
  omega

theorem boundNumbers_countBefore {bs : List Binder} {i : ℕ} (hi : i < bs.length) (hb : isBoundAt bs i) :
    (boundNumbers bs)[countBefore bs i]'(countBefore_lt hi hb) = i := by
  have h := boundNumbers_split hi hb
  simp only [countBefore]
  rw [List.getElem_of_eq h, List.getElem_append_right (le_refl _)]
  simp

theorem bvVar_countBefore {bs : List Binder} {i : ℕ} (hi : i < bs.length) (hb : isBoundAt bs i) :
    bvVar bs (countBefore bs i) = i := by
  rw [bvVar_of_lt (countBefore_lt hi hb), boundNumbers_countBefore hi hb]

theorem countBefore_succ_of_bound {bs : List Binder} {i : ℕ} (hb : isBoundAt bs i) :
    countBefore bs (i + 1) = countBefore bs i + 1 := by
  unfold countBefore
  rw [List.range_succ, List.filter_append, List.length_append]
  simp [hb]

theorem countBefore_succ_of_reg {bs : List Binder} {i : ℕ} (hb : ¬ isBoundAt bs i) :
    countBefore bs (i + 1) = countBefore bs i := by
  unfold countBefore
  rw [List.range_succ, List.filter_append, List.length_append]
  simp [hb]

theorem countBefore_length (bs : List Binder) : countBefore bs bs.length = (boundNumbers bs).length := by
  unfold countBefore
  rw [boundNumbers_eq]

end Verifier
