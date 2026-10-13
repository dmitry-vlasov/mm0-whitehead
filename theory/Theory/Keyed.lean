/-
The keyed engine (`docs/THEORY.md`, "The production engine", milestone 12): the
reference engine's SPT sets with the production engine's three ideas — a proof goes up
with its substitution restricted to the visible variables of its node (`restrict`,
`DESIGN.md` change 5); a condition is judged as soon as it can be, violated (the proof
dropped), settled (the condition dropped) or pending (`judge`, `openConds`); and one
entry is kept per key, the key being the restricted substitution with the pending
conditions (`proofKey`, `addProof`). The state, its rounds and its nodes are the
reference engine's (`State.run`): the keyed engine differs in what it reads off the
state, as the production engine's tree differs from the reference engine's in its
proofs, not in its nodes.
-/
import Theory.Engine

namespace Theory

open State

/-- An entry of the keyed engine: its tree, its substitution restricted to the visible
variables of its node, and its pending conditions, under that substitution. -/
structure KEntry where
  tree : SptTree
  sub : Subst
  conds : List Cond
  deriving Inhabited

/-- Whether two substitutions are the same: the same domain, and the same image on it. -/
def Subst.beq (θ η : Subst) : Bool :=
  θ.dom = η.dom && (θ.dom.sort (· ≤ ·)).all fun v => θ.f v = η.f v

theorem Subst.beq_iff {θ η : Subst} : Subst.beq θ η = true ↔ θ = η := by
  constructor
  · intro h
    simp only [Subst.beq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨hd, hf⟩ := h
    apply Subst.ext
    funext v
    by_cases hv : v ∈ θ.dom
    · exact hf v (by rw [Finset.mem_sort]; exact hv)
    · rw [Subst.f_eq_of_not_mem hv, Subst.f_eq_of_not_mem (by rwa [← hd])]
  · rintro rfl
    simp [Subst.beq]

/-- The same key: the same restricted substitution and the same pending conditions. -/
def KEntry.sameKey (K K' : KEntry) : Bool := Subst.beq K.sub K'.sub && K.conds == K'.conds

/-- What can be said of a condition under the join `J` at a node whose expression is
`e`, as `judge` of the production engine says it: `none`, violated — the name occurs;
`some false`, settled — the name is a variable that no node above can replace, since
it is not among the variables of the expression under `J` nor of the statement, or a
constant and the expression has no variable left; `some true`, pending. -/
def judgeK (c : Consts) (st : Statement) (e : Exp) (J : Subst) (k : Cond) : Option Bool :=
  let k' := Cond.apply J k
  if ¬ k'.Holds c then none
  else match k'.1 with
    | .var y => if y ∈ (J.apply e).vars ∪ st.vars then some true else some false
    | _ => if k'.2.vars = ∅ then some false else some true

/-- The conditions of a new entry: `none` if one is violated; otherwise the pending
ones, under `J`. -/
def judgeAll (c : Consts) (st : Statement) (e : Exp) (J : Subst) : List Cond → Option (List Cond)
  | [] => some []
  | k :: ks =>
    match judgeK c st e J k with
    | none => none
    | some false => judgeAll c st e J ks
    | some true => (judgeAll c st e J ks).map (Cond.apply J k :: ·)

/-- Every choice of one entry from each list. -/
def tuplesK : List (List KEntry) → List (List KEntry)
  | [] => [[]]
  | l :: ls => l.flatMap fun x => (tuplesK ls).map (x :: ·)

/-- One entry per key, the first found. -/
def dedupKeys (es : List KEntry) : List KEntry :=
  es.foldl (init := []) fun acc K => if acc.any (·.sameKey K) then acc else acc ++ [K]

/-- The leaf entries of an expression node, restricted to its visible variables. -/
def leafK (U : Unification) (st : Statement) (s : State) (i : ℕ) : List KEntry :=
  (leafEntries U st i s.enodes[i]!.expr).map fun E =>
    { tree := E.tree, sub := E.sub.restrict (visible st s i), conds := [] }

/-- The entries of assertion node `j` under expression node `i`: for every tuple of
entries of its children, the join of `θ_a` with their restricted substitutions; the
node's pairs and the tuple's pending conditions judged under the join; the
substitution restricted to the visible variables of `i`; one entry per key. -/
def anodeK (U : Unification) (st : Statement) (s : State) (i j : ℕ) (childEntries : List (List KEntry)) :
    List KEntry :=
  let a := s.anodes[j]!
  let e := s.enodes[i]!.expr
  dedupKeys ((tuplesK childEntries).filterMap fun tup =>
    match U.joinAll (a.sub :: tup.map (·.sub)) with
    | none => none
    | some J =>
      (judgeAll st.consts st e J (a.conds ++ tup.flatMap (·.conds))).map fun pending =>
        { tree := .node j (tup.map (·.tree)), sub := J.restrict (visible st s i), conds := pending })

/-- The keyed entries of an expression node, down to a depth: the leaf entries, and the
entries of its assertion nodes from the keyed entries of their children. -/
def keyedE (U : Unification) (st : Statement) (s : State) : ℕ → ℕ → List KEntry
  | 0, _ => []
  | fuel + 1, i =>
    leafK U st s i ++ (aChildren s i).flatMap fun j =>
      anodeK U st s i j (s.anodes[j]!.children.map fun c => keyedE U st s fuel c)

/-- The keyed entries at the root: the answers, one per key. -/
def keyedRoot (U : Unification) (st : Statement) (s : State) : List KEntry :=
  keyedE U st s s.enodes.size 0

end Theory
