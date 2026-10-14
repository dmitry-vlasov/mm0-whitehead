/-
The reference verifier (milestone V4): the machine's relations made executable, each
function proved sound for its relation. With `file_sound`, `checkFile f = true` gives
`env.proof'` of the environment `f` declares.

The representation is the machine's — lists and finite sets — chosen for the proofs,
not for speed; the fast verifier (`Whitehead/Verify`) is tested against this one
(milestone V5).
-/
import Verifier.FileSound

namespace Verifier

open mm0
open Whitehead.Mmb (ProofCmd UnifyCmd)

/-! ### Popping arguments -/

def popArgsF : ℕ → List El → Option (List ℕ × List El)
  | 0, S => some ([], S)
  | n + 1, El.expr p :: S => (popArgsF n S).map fun r => (r.1 ++ [p], r.2)
  | _ + 1, _ => none

theorem popArgsF_sound : ∀ {n : ℕ} {S : List El} {ps : List ℕ} {S' : List El},
    popArgsF n S = some (ps, S') → popArgs n S ps S'
  | 0, S, ps, S', h => by
    simp only [popArgsF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact popArgs.zero S
  | n + 1, El.expr p :: S, ps, S', h => by
    simp only [popArgsF, Option.map_eq_some_iff] at h
    obtain ⟨⟨ps₀, S₀⟩, h₀, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact popArgs.succ n S p ps₀ S₀ (popArgsF_sound h₀)
  | n + 1, [], _, _, h => by simp [popArgsF] at h
  | n + 1, El.proof _ :: _, _, _, h => by simp [popArgsF] at h
  | n + 1, El.conv _ _ :: _, _, _, h => by simp [popArgsF] at h
  | n + 1, El.coConv _ _ :: _, _, _, h => by simp [popArgsF] at h

/-! ### The arguments and the disjointness conditions -/

def argsOkB (st : State) : List Binder → List ℕ → Bool
  | [], [] => true
  | b :: bs, p :: ps =>
    (match st.ty p with
     | some ty => decide (ty.sort = b.sort) && (!b.bound || ty.bound)
     | none => false) && argsOkB st bs ps
  | _, _ => false

theorem argsOkB_sound {st : State} : ∀ {bs : List Binder} {ps : List ℕ}, argsOkB st bs ps = true → argsOk st bs ps
  | [], [], _ => trivial
  | b :: bs, p :: ps, h => by
    simp only [argsOkB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, argsOkB_sound h2⟩
    cases hty : st.ty p with
    | none => rw [hty] at h1; cases h1
    | some ty =>
      rw [hty] at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h1
      refine ⟨ty, rfl, h1.1, fun hb => ?_⟩
      rcases h1.2 with h | h
      · rw [hb] at h; cases h
      · exact h
  | [], _ :: _, h => by simp [argsOkB] at h
  | _ :: _, [], h => by simp [argsOkB] at h

def thmDisjointB (st : State) : List Binder → List ℕ → List (ℕ × Finset ℕ) → List (Finset ℕ) → Bool
  | [], [], _, _ => true
  | b :: bs, p :: ps, seen, earlier =>
    match st.ty p with
    | none => false
    | some ty =>
      if b.bound then
        earlier.all (fun d => decide (Disjoint ty.deps d)) &&
          thmDisjointB st bs ps (seen ++ [(seen.length, ty.deps)]) (earlier ++ [ty.deps])
      else
        seen.all (fun jd => decide (jd.1 ∉ b.deps → Disjoint ty.deps jd.2)) &&
          thmDisjointB st bs ps seen (earlier ++ [ty.deps])
  | _, _, _, _ => false

theorem thmDisjointB_sound {st : State} : ∀ {bs : List Binder} {ps : List ℕ} {seen : List (ℕ × Finset ℕ)}
    {earlier : List (Finset ℕ)}, thmDisjointB st bs ps seen earlier = true → thmDisjoint st bs ps seen earlier
  | [], [], _, _, _ => trivial
  | b :: bs, p :: ps, seen, earlier, h => by
    simp only [thmDisjointB] at h
    cases hty : st.ty p with
    | none => rw [hty] at h; cases h
    | some ty =>
      rw [hty] at h
      refine ⟨ty, hty, ?_⟩
      cases hb : b.bound
      · simp only [hb, Bool.false_eq_true, ite_false, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
        exact ⟨h.1, thmDisjointB_sound h.2⟩
      · simp only [hb, ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
        exact ⟨h.1, thmDisjointB_sound h.2⟩
  | [], _ :: _, _, _, h => by simp [thmDisjointB] at h
  | _ :: _, [], _, _, h => by simp [thmDisjointB] at h

/-! ### The unifier -/

def dummyFresh (st : State) (ty : Ty) (H : UHeap) : Bool :=
  H.all fun h => h.2 || match st.ty h.1 with
    | some ty' => decide (Disjoint ty.deps ty'.deps)
    | none => true

def unifyF (c : Ctx) (st : State) (mode : UMode) :
    UHeap → List UnifyCmd → List ℕ → List El → List ℕ → Option (List El × List ℕ)
  | _, [], K, S, hs => if K = [] ∧ (mode = .thmEnd → hs = []) then some (S, hs) else none
  | H, UnifyCmd.ref i :: us, e :: K, S, hs =>
    match H[i]? with
    | some (e', _) => if e' = e then unifyF c st mode H us K S hs else none
    | none => none
  | H, UnifyCmd.term t save :: us, e :: K, S, hs =>
    match st.store[e]? with
    | some (Node.app _ t' args) =>
      if t' = t then unifyF c st mode (if save then H ++ [(e, true)] else H) us (args ++ K) S hs else none
    | _ => none
  | H, UnifyCmd.dummy s :: us, e :: K, S, hs =>
    if mode = .defn then
      match st.store[e]? with
      | some (Node.var ty _) =>
        if ty.bound = true ∧ ty.sort = s ∧ dummyFresh st ty H = true then
          unifyF c st mode (H ++ [(e, false)]) us K S hs
        else none
      | _ => none
    else none
  | H, UnifyCmd.hyp :: us, [], S, hs =>
    match mode with
    | .thm =>
      match S with
      | El.proof e :: S' => unifyF c st mode H us [e] S' hs
      | _ => none
    | .thmEnd =>
      match hs.getLast? with
      | some e => unifyF c st mode H us [e] S hs.dropLast
      | none => none
    | .defn => none
  | _, _, _, _, _ => none

theorem dummyFresh_sound {st : State} {ty : Ty} {H : UHeap} (h : dummyFresh st ty H = true) :
    ∀ x ∈ H, x.2 = false → ∀ ty', st.ty x.1 = some ty' → Disjoint ty.deps ty'.deps := by
  intro x hx hb ty' hty'
  have := List.all_eq_true.1 h x hx
  rw [hb, hty'] at this
  simpa using this

theorem unifyF_sound {c : Ctx} {st : State} {mode : UMode} : ∀ {H : UHeap} {us : List UnifyCmd} {K : List ℕ}
    {S : List El} {hs : List ℕ} {S' : List El} {hs' : List ℕ},
    unifyF c st mode H us K S hs = some (S', hs') → Unify c st mode H us K S hs S' hs'
  | H, [], K, S, hs, S', hs', h => by
    simp only [unifyF] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, h2⟩ := hc
      exact Unify.nil mode H S hs h2
    · cases h
  | H, UnifyCmd.ref i :: us, [], S, hs, S', hs', h => by simp [unifyF] at h
  | H, UnifyCmd.ref i :: us, e :: K, S, hs, S', hs', h => by
    simp only [unifyF] at h
    split at h
    · rename_i e' b hi
      split at h
      · rename_i he
        subst he
        exact Unify.ref mode H us e' K S hs S' hs' i b hi (unifyF_sound h)
      · cases h
    · cases h
  | H, UnifyCmd.term t save :: us, [], S, hs, S', hs', h => by simp [unifyF] at h
  | H, UnifyCmd.term t save :: us, e :: K, S, hs, S', hs', h => by
    simp only [unifyF] at h
    split at h
    · rename_i ty t' args hn
      split at h
      · rename_i ht
        subst ht
        exact Unify.term mode H us e t' save ty args K S hs S' hs' hn (unifyF_sound h)
      · cases h
    · cases h
  | H, UnifyCmd.dummy s :: us, [], S, hs, S', hs', h => by simp [unifyF] at h
  | H, UnifyCmd.dummy s :: us, e :: K, S, hs, S', hs', h => by
    simp only [unifyF] at h
    split at h
    · rename_i hmode
      subst hmode
      split at h
      · rename_i ty v hn
        split at h
        · rename_i hc
          obtain ⟨hb, hs0, hfresh⟩ := hc
          exact Unify.dummy H us e s ty v K S hs S' hs' hn hb hs0 (dummyFresh_sound hfresh) (unifyF_sound h)
        · cases h
      · cases h
    · cases h
  | H, UnifyCmd.hyp :: us, e :: K, S, hs, S', hs', h => by simp [unifyF] at h
  | H, UnifyCmd.hyp :: us, [], S, hs, S', hs', h => by
    simp only [unifyF] at h
    cases mode with
    | thm =>
      simp only at h
      split at h
      · rename_i e S₀
        exact Unify.hyp_thm H us e S₀ hs S' hs' (unifyF_sound h)
      · cases h
    | thmEnd =>
      simp only at h
      split at h
      · rename_i e hlast
        have hdl : hs = hs.dropLast ++ [e] := (List.dropLast_append_getLast? (l := hs) (a := e) hlast).symm
        rw [hdl]
        exact Unify.hyp_end H us e S hs.dropLast S' hs' (unifyF_sound h)
      · cases h
    | defn => cases h

/-! ### The commands -/

def tyOrZero (st : State) (p : ℕ) : Ty := (st.ty p).getD ⟨0, false, ∅⟩

def isCoConv : El → Bool
  | .coConv _ _ => true
  | _ => false

def isConvEl : El → Bool
  | .conv _ _ => true
  | _ => false

def stepF (c : Ctx) (st : State) : ProofCmd → Option State
  | .term t save =>
    match c.terms[t]? with
    | none => none
    | some decl =>
      match popArgsF decl.args.length st.stack with
      | none => none
      | some (args, S') =>
        if argsOkB st decl.args args then
          some { st with stack := El.expr st.store.length :: S',
                         heap := if save then st.heap ++ [El.expr st.store.length] else st.heap,
                         store := st.store ++ [Node.app ⟨decl.ret.sort, false,
                           appDeps c.isDef decl.args decl.ret (args.map fun p => (st.ty p).getD ⟨0, false, ∅⟩)⟩ t args] }
        else none
  | .ref i =>
    match st.heap[i]? with
    | none => none
    | some el =>
      if isConvEl el then
        match el, st.stack with
        | El.conv e1 e2, El.coConv a b :: S => if a = e1 ∧ b = e2 then some { st with stack := S } else none
        | _, _ => none
      else some { st with stack := el :: st.stack }
  | .dummy s =>
    match c.sorts[s]? with
    | none => none
    | some sd =>
      if sd.strict = false ∧ sd.free = false ∧ st.nextBv < maxBound then
        some { st with stack := El.expr st.store.length :: st.stack,
                       heap := st.heap ++ [El.expr st.store.length],
                       store := st.store ++ [Node.var ⟨s, true, {st.nextBv}⟩ st.nextVar],
                       nextBv := st.nextBv + 1, nextVar := st.nextVar + 1 }
      else none
  | .thm t save =>
    if c.isDef = false then
      match c.thms[t]?, st.stack with
      | some decl, El.expr e :: S₁ =>
        match popArgsF decl.args.length S₁ with
        | none => none
        | some (args, S₂) =>
          if argsOkB st decl.args args ∧ thmDisjointB st decl.args args [] [] then
            match unifyF c st .thm (args.map fun p => (p, false)) decl.unify [e] S₂ [] with
            | some (S₃, []) =>
              some { st with stack := El.proof e :: S₃,
                             heap := if save then st.heap ++ [El.proof e] else st.heap }
            | _ => none
          else none
      | _, _ => none
    else none
  | .hyp =>
    if c.isDef = false then
      match st.stack with
      | El.expr e :: S =>
        match st.ty e with
        | some ty =>
          match c.sorts[ty.sort]? with
          | some sd =>
            if sd.provable = true then
              some { st with stack := El.proof e :: S, heap := st.heap ++ [El.proof e], hyps := st.hyps ++ [e] }
            else none
          | none => none
        | none => none
      | _ => none
    else none
  | .conv =>
    match st.stack with
    | El.proof e2 :: El.expr e1 :: S => some { st with stack := El.coConv e1 e2 :: El.proof e1 :: S }
    | _ => none
  | .refl =>
    match st.stack with
    | El.coConv a b :: S => if a = b then some { st with stack := S } else none
    | _ => none
  | .symm =>
    match st.stack with
    | El.coConv a b :: S => some { st with stack := El.coConv b a :: S }
    | _ => none
  | .cong =>
    match st.stack with
    | El.coConv e1 e2 :: S =>
      match st.store[e1]?, st.store[e2]? with
      | some (Node.app _ t1 args1), some (Node.app _ t2 args2) =>
        if t1 = t2 ∧ args1.length = args2.length then
          some { st with stack := List.zipWith El.coConv args1 args2 ++ S }
        else none
      | _, _ => none
    | _ => none
  | .unfold =>
    match st.stack with
    | El.expr e2 :: El.coConv e e' :: S =>
      match st.store[e]? with
      | some (Node.app _ t args) =>
        match c.terms[t]? with
        | some decl =>
          match decl.defn with
          | some us =>
            if unifyF c st .defn (args.map fun p => (p, false)) us [e2] S [] = some (S, []) then
              some { st with stack := El.coConv e2 e' :: S }
            else none
          | none => none
        | none => none
      | _ => none
    | _ => none
  | .convCut =>
    match st.stack with
    | El.coConv a b :: S => some { st with stack := El.coConv a b :: El.conv a b :: S }
    | _ => none
  | .convSave =>
    match st.stack with
    | El.conv a b :: S => some { st with stack := S, heap := st.heap ++ [El.conv a b] }
    | _ => none
  | .save =>
    match st.stack with
    | el :: _ => if isCoConv el then none else some { st with heap := st.heap ++ [el] }
    | [] => none
  | .sorry => none

theorem stepF_sound {c : Ctx} {st st' : State} : ∀ {cmd : ProofCmd}, stepF c st cmd = some st' → Step c cmd st st'
  | .term t save, h => by
    simp only [stepF] at h
    split at h
    · cases h
    · rename_i decl hd
      split at h
      · cases h
      · rename_i args S' hpop
        split at h
        · rename_i hok
          simp only [Option.some.injEq] at h
          subst h
          exact Step.term st t save decl args S' _ hd (popArgsF_sound hpop) (argsOkB_sound hok) rfl
        · cases h
  | .ref i, h => by
    simp only [stepF] at h
    split at h
    · cases h
    · rename_i el hi
      split at h
      · split at h
        · split at h
          · rename_i e1 e2 a b S hstk _ hab
            obtain ⟨rfl, rfl⟩ := hab
            simp only [Option.some.injEq] at h
            subst h
            exact Step.ref_conv st i a b S hi hstk
          · cases h
        · cases h
      · rename_i hnc
        simp only [Option.some.injEq] at h
        subst h
        refine Step.ref_el st i el hi (fun e1 e2 he => ?_)
        subst he
        exact hnc rfl
  | .dummy s, h => by
    simp only [stepF] at h
    split at h
    · cases h
    · rename_i sd hsd
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        exact Step.dummy st s sd hsd hc.1 hc.2.1 hc.2.2
      · cases h
  | .thm t save, h => by
    simp only [stepF] at h
    split at h
    · rename_i hdef
      split at h
      · rename_i decl e S₁ hd hstk
        split at h
        · cases h
        · rename_i args S₂ hpop
          split at h
          · rename_i hok
            split at h
            · rename_i S₃ hU
              simp only [Option.some.injEq] at h
              subst h
              exact Step.thm st t save decl e args S₁ S₂ hdef hd hstk (popArgsF_sound hpop)
                (argsOkB_sound hok.1) (thmDisjointB_sound hok.2) S₃ (unifyF_sound hU)
            · cases h
          · cases h
      · cases h
    · cases h
  | .hyp, h => by
    simp only [stepF] at h
    split at h
    · rename_i hdef
      split at h
      · rename_i e S hstk
        split at h
        · rename_i ty hty
          split at h
          · rename_i sd hsd
            split at h
            · rename_i hprov
              simp only [Option.some.injEq] at h
              subst h
              exact Step.hyp st e S ty sd hdef hstk hty hsd hprov
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  | .conv, h => by
    simp only [stepF] at h
    split at h
    · rename_i e2 e1 S hstk
      simp only [Option.some.injEq] at h
      subst h
      exact Step.conv st e1 e2 S hstk
    · cases h
  | .refl, h => by
    simp only [stepF] at h
    split at h
    · rename_i a b S hstk
      split at h
      · rename_i hab
        subst hab
        simp only [Option.some.injEq] at h
        subst h
        exact Step.refl st a S hstk
      · cases h
    · cases h
  | .symm, h => by
    simp only [stepF] at h
    split at h
    · rename_i a b S hstk
      simp only [Option.some.injEq] at h
      subst h
      exact Step.symm st a b S hstk
    · cases h
  | .cong, h => by
    simp only [stepF] at h
    split at h
    · rename_i e1 e2 S hstk
      split at h
      · rename_i ty1 t1 args1 ty2 t2 args2 hn1 hn2
        split at h
        · rename_i hc
          obtain ⟨rfl, hlen⟩ := hc
          simp only [Option.some.injEq] at h
          subst h
          exact Step.cong st e1 e2 S ty1 ty2 t1 args1 args2 hstk hn1 hn2 hlen
        · cases h
      · cases h
    · cases h
  | .unfold, h => by
    simp only [stepF] at h
    split at h
    · rename_i e2 e e' S hstk
      split at h
      · rename_i ty t args hn
        split at h
        · rename_i decl hd
          split at h
          · rename_i us hus
            split at h
            · rename_i hU
              simp only [Option.some.injEq] at h
              subst h
              exact Step.unfold st e e' t ty args decl us S e2 hstk hn hd hus (unifyF_sound hU)
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  | .convCut, h => by
    simp only [stepF] at h
    split at h
    · rename_i a b S hstk
      simp only [Option.some.injEq] at h
      subst h
      exact Step.convCut st a b S hstk
    · cases h
  | .convSave, h => by
    simp only [stepF] at h
    split at h
    · rename_i a b S hstk
      simp only [Option.some.injEq] at h
      subst h
      exact Step.convSave st a b S hstk
    · cases h
  | .save, h => by
    simp only [stepF] at h
    split at h
    · rename_i el S hstk
      split at h
      · cases h
      · rename_i hnc
        simp only [Option.some.injEq] at h
        subst h
        refine Step.save st el S hstk (fun e1 e2 he => ?_)
        subst he
        exact hnc rfl
    · cases h
  | .sorry, h => by simp [stepF] at h

/-! ### Runs and binders -/

def runF (c : Ctx) : List ProofCmd → State → Option State
  | [], st => some st
  | cmd :: cmds, st =>
    match stepF c st cmd with
    | some st' => runF c cmds st'
    | none => none

theorem runF_sound {c : Ctx} : ∀ {cmds : List ProofCmd} {st st' : State}, runF c cmds st = some st' → Run c cmds st st'
  | [], st, st', h => by
    simp only [runF, Option.some.injEq] at h
    subst h
    exact Run.nil st
  | cmd :: cmds, st, st', h => by
    simp only [runF] at h
    split at h
    · rename_i st₁ hs
      exact Run.cons cmd cmds st st₁ st' (stepF_sound hs) (runF_sound h)
    · cases h

def loadF (c : Ctx) : List Binder → State → Option State
  | [], st => some st
  | b :: bs, st =>
    if b.bound then
      match c.sorts[b.sort]? with
      | some sd =>
        if sd.strict = false ∧ st.nextBv < maxBound ∧ b.deps = {st.nextBv} then
          loadF c bs { st with store := st.store ++ [Node.var (Ty.ofBinder b) st.nextVar],
                               heap := st.heap ++ [El.expr st.store.length],
                               nextBv := st.nextBv + 1, nextVar := st.nextVar + 1 }
        else none
      | none => none
    else
      if b.sort < c.sorts.length ∧ ∀ j ∈ b.deps, j < st.nextBv then
        loadF c bs { st with store := st.store ++ [Node.var (Ty.ofBinder b) st.nextVar],
                             heap := st.heap ++ [El.expr st.store.length], nextVar := st.nextVar + 1 }
      else none

theorem loadF_sound {c : Ctx} : ∀ {bs : List Binder} {st st' : State}, loadF c bs st = some st' → LoadArgs c bs st st'
  | [], st, st', h => by
    simp only [loadF, Option.some.injEq] at h
    subst h
    exact LoadArgs.nil st
  | b :: bs, st, st', h => by
    simp only [loadF] at h
    split at h
    · rename_i hb
      split at h
      · rename_i sd hsd
        split at h
        · rename_i hc
          exact LoadArgs.bound b bs st st' sd hb hsd hc.1 hc.2.1 hc.2.2 (loadF_sound h)
        · cases h
      · cases h
    · rename_i hb
      split at h
      · rename_i hc
        exact LoadArgs.reg b bs st st' (by simpa using hb) hc.1 hc.2 (loadF_sound h)
      · cases h

/-! ### Statements -/

def termOkB (c : Ctx) (decl : TermDecl) (isLocal : Bool) (body : List ProofCmd) : Bool :=
  (!isLocal || decl.defn.isSome) &&
  match loadF c decl.args State.empty with
  | none => false
  | some st =>
    decide (decl.ret.bound = false) &&
    (match c.sorts[decl.ret.sort]? with
     | some sd => decide (sd.pure = false)
     | none => false) &&
    decide (∀ j ∈ decl.ret.deps, j < st.nextBv) &&
    match decl.defn with
    | none => decide (body = [])
    | some us =>
      match runF { c with isDef := true } body st with
      | some st' =>
        match st'.stack with
        | [El.expr e] =>
          match st'.ty e with
          | some ty =>
            decide (ty.sort = decl.ret.sort) && decide (ty.deps ⊆ decl.ret.deps) &&
              decide (unifyF { c with isDef := true } st' .defn (argsUheap st' decl.args.length) us [e] [] [] = some ([], []))
          | none => false
        | _ => false
      | none => false

theorem termOkB_sound {c : Ctx} {decl : TermDecl} {isLocal : Bool} {body : List ProofCmd}
    (h : termOkB c decl isLocal body = true) : TermOk c decl isLocal body := by
  simp only [termOkB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hloc, h⟩ := h
  refine ⟨fun hl => ?_, ?_⟩
  · rcases hloc with hloc | hloc
    · rw [hl] at hloc; cases hloc
    · exact hloc
  split at h
  · cases h
  · rename_i st hload
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hrb, hrs⟩, hrd⟩, hmatch⟩ := h
    refine ⟨st, loadF_sound hload, hrb, ?_, hrd, ?_⟩
    · split at hrs
      · rename_i sd hsd
        exact ⟨sd, hsd, by simpa using hrs⟩
      · cases hrs
    · split
      · rename_i hnone
        rw [hnone] at hmatch
        simpa using hmatch
      · rename_i us hus
        rw [hus] at hmatch
        simp only at hmatch
        split at hmatch
        · rename_i st' hrun
          split at hmatch
          · rename_i e hstk
            split at hmatch
            · rename_i ty hty
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hmatch
              obtain ⟨⟨hsort, hdeps⟩, hU⟩ := hmatch
              exact ⟨st', e, ty, runF_sound hrun, hstk, hty, hsort, hdeps, unifyF_sound hU⟩
            · cases hmatch
          · cases hmatch
        · cases hmatch

def thmOkB (c : Ctx) (decl : ThmDecl) (isAxiom : Bool) (body : List ProofCmd) : Bool :=
  match loadF c decl.args State.empty with
  | none => false
  | some st =>
    match runF { c with isDef := false } body st with
    | none => false
    | some st' =>
      match st'.stack with
      | [el] =>
        match (if isAxiom then (match el with | El.expr e => some e | _ => none)
               else (match el with | El.proof e => some e | _ => none)) with
        | some e =>
          match st'.ty e with
          | some ty =>
            match c.sorts[ty.sort]? with
            | some sd =>
              decide (sd.provable = true) &&
                decide (unifyF { c with isDef := false } st' .thmEnd (argsUheap st' decl.args.length) decl.unify [e] []
                  st'.hyps = some ([], []))
            | none => false
          | none => false
        | none => false
      | _ => false

theorem thmOkB_sound {c : Ctx} {decl : ThmDecl} {isAxiom : Bool} {body : List ProofCmd}
    (h : thmOkB c decl isAxiom body = true) : ThmOk c decl isAxiom body := by
  simp only [thmOkB] at h
  split at h
  · cases h
  · rename_i st hload
    split at h
    · cases h
    · rename_i st' hrun
      split at h
      · rename_i el hstk
        split at h
        · rename_i e hel
          split at h
          · rename_i ty hty
            split at h
            · rename_i sd hsd
              simp only [Bool.and_eq_true, decide_eq_true_eq] at h
              obtain ⟨hprov, hU⟩ := h
              have hel' : el = (if isAxiom then El.expr e else El.proof e) := by
                cases isAxiom <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hel ⊢ <;>
                  (cases el <;> simp_all)
              exact ⟨st, st', e, ty, sd, loadF_sound hload, runF_sound hrun, by rw [hstk, hel'], hty, hsd, hprov,
                unifyF_sound hU⟩
            · cases h
          · cases h
        · cases h
      · cases h

/-! ### The file -/

def stmtsB (f : File) : List Stmt → ℕ → ℕ → ℕ → Bool
  | [], ns, nt, nh => decide (ns = f.sorts.length ∧ nt = f.terms.length ∧ nh = f.thms.length)
  | s :: ss, ns, nt, nh =>
    match s.kind with
    | .sort => decide (s.body = []) && decide (ns < f.sorts.length) && stmtsB f ss (ns + 1) nt nh
    | .term =>
      decide (s.body = []) &&
      match f.terms[nt]? with
      | some decl => decide (decl.defn = none) &&
          termOkB ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, false⟩ decl false [] && stmtsB f ss ns (nt + 1) nh
      | none => false
    | .defn isLocal =>
      match f.terms[nt]? with
      | some decl => decl.defn.isSome &&
          termOkB ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, true⟩ decl isLocal s.body &&
          stmtsB f ss ns (nt + 1) nh
      | none => false
    | .ax =>
      match f.thms[nh]? with
      | some decl => thmOkB ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, false⟩ decl true s.body &&
          stmtsB f ss ns nt (nh + 1)
      | none => false
    | .thm _ =>
      match f.thms[nh]? with
      | some decl => thmOkB ⟨f.sorts.take ns, f.terms.take nt, f.thms.take nh, false⟩ decl false s.body &&
          stmtsB f ss ns nt (nh + 1)
      | none => false

theorem stmtsB_sound {f : File} : ∀ {ss : List Stmt} {ns nt nh : ℕ}, stmtsB f ss ns nt nh = true → Stmts f ss ns nt nh
  | [], ns, nt, nh, h => by
    simp only [stmtsB, decide_eq_true_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Stmts.nil
  | s :: ss, ns, nt, nh, h => by
    obtain ⟨kind, body⟩ := s
    cases kind <;> simp only [stmtsB] at h
    case sort =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hns⟩, hr⟩ := h
      exact Stmts.sort ss ns nt nh hns (stmtsB_sound hr)
    case term =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, h⟩ := h
      split at h
      · rename_i decl hd
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hnone, hok⟩, hr⟩ := h
        exact Stmts.term ss ns nt nh decl hd hnone (termOkB_sound hok) (stmtsB_sound hr)
      · cases h
    case defn isLocal =>
      split at h
      · rename_i decl hd
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨hsome, hok⟩, hr⟩ := h
        exact Stmts.defn ss ns nt nh decl isLocal body hd hsome (termOkB_sound hok) (stmtsB_sound hr)
      · cases h
    case ax =>
      split at h
      · rename_i decl hd
        simp only [Bool.and_eq_true] at h
        exact Stmts.ax ss ns nt nh decl body hd (thmOkB_sound h.1) (stmtsB_sound h.2)
      · cases h
    case thm isLocal =>
      split at h
      · rename_i decl hd
        simp only [Bool.and_eq_true] at h
        exact Stmts.thm ss ns nt nh decl isLocal body hd (thmOkB_sound h.1) (stmtsB_sound h.2)
      · cases h

/-- The reference verifier. -/
def checkFile (f : File) : Bool := stmtsB f f.stmts 0 0 0

theorem checkFile_sound {f : File} (h : checkFile f = true) : FileOk f := stmtsB_sound h

/-- **The verified checker** (milestone V4): a decoded proof file that the reference
verifier accepts declares an environment whose every theorem is proved, `env.proof'`
of the formal semantics. -/
theorem checkFile_correct {f : File} (h : checkFile f = true) : ∃ E, toEnv f = some E ∧ env.proof' E :=
  file_sound (checkFile_sound h)

end Verifier
