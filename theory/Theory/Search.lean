/-
The reference engine (`docs/THEORY.md`, "The reference engine"): the proof variant tree
and the substitution proof trees of the draft's Definitions 4.1 and 4.2, computed round
by round, breadth first, every entry kept. Pure, and it runs; written as folds and
recursions, so that the invariants (`Spt.lean`) can be proved about it.

One departure from the draft's wording of Definition 4.2: the entry of an assertion
node joins the children's answers *with the node's own unifier* `θ_a`; without it the
metavariables of the parent that `θ_a` binds would be lost from the answer. The 2017
paper's correctness proof has the witness `θ_0 ∘ η`, and Russell composes
`prop.sub` with the join (`ruAddProof`).
-/
import Theory.Unification
import Theory.Deduction

namespace Theory

/-- An expression node of the proof variant tree. -/
structure ENode where
  expr : Exp
  /-- The assertion node it is a hypothesis of, and its position; `none` at the root. -/
  parent : Option (ℕ × ℕ)
  expanded : Bool
  deriving Inhabited

/-- An assertion node: its expression node, the assertion, the base its variables were
renamed to, the unifier `θ_a` of the renamed conclusion with the expression, its
children, and its pairs under `θ_a`. -/
structure ANode where
  parent : ℕ
  assertion : ℕ
  base : ℕ
  sub : Subst
  children : List ℕ
  conds : List Cond
  deriving Inhabited

/-- A substitution proof tree: at each expression node one assertion node, or the
hypothesis of the statement that closes it. -/
inductive SptTree where
  | leaf (enode : ℕ) (hyp : ℕ)
  | node (anode : ℕ) (children : List SptTree)
  deriving Inhabited

/-- An entry of an SPT set: the tree, its answer substitution, and the conditions it
carries, every one of which holds under the answer so far. -/
structure Entry where
  tree : SptTree
  sub : Subst
  conds : List Cond
  deriving Inhabited

/-- The proof variant tree: its nodes, and how its fresh variables are numbered. The
assertion node `j` renames the binders of its assertion to `freshBase + j * stride + x`:
`freshBase` is above every variable of the statement and `stride` above every binder,
so the variables of distinct nodes never meet. -/
structure State where
  enodes : Array ENode
  anodes : Array ANode
  freshBase : ℕ
  stride : ℕ

namespace State

/-- A stride above every binder of the database. -/
def strideOf (db : Database) : ℕ :=
  (db.asserts.map fun A => (A.vars.map (·.id)).foldl max 0).foldl max 0 + 1

/-- The tree with the statement's conclusion at the root. -/
def init (db : Database) (st : Statement) : State where
  enodes := #[{ expr := st.concl, parent := none, expanded := false }]
  anodes := #[]
  freshBase := (st.concl.vars ∪ (st.hyps.map Exp.vars).foldr (· ∪ ·) ∅).sup Var.id + 1
  stride := strideOf db

/-- The base of the variables of assertion node `j`. -/
def baseOf (s : State) (j : ℕ) : ℕ := s.freshBase + j * s.stride

/-- The renamed variable of an assertion node. -/
def renamed (base : ℕ) (x : Var) : Var := ⟨base + x.id, x.ty⟩

/-- The conditions of an assertion node: the pairs of its assertion, renamed, under
its unifier. -/
def nodeConds (A : Assertion) (b : ℕ) (θ : Subst) : List Cond :=
  A.pairs.map fun p => (θ.apply (.var (renamed b p.1)), θ.apply (.var (renamed b p.2)))

/-- The new expression nodes of an assertion node: the hypotheses of its assertion,
renamed, under the unifier. -/
def newENodes (s : State) (A : Assertion) (θ : Subst) : List ENode :=
  (List.range A.hyps.length).map fun k =>
    { expr := θ.apply (A.hyps[k]!.rename (s.baseOf s.anodes.size)), parent := some (s.anodes.size, k),
      expanded := false }

/-- Adds an assertion node at expression node `i` for assertion `a` (which is `A`) with
unifier `θ`, and its children. -/
def addNode (i a : ℕ) (s : State) (A : Assertion) (θ : Subst) : State where
  enodes := s.enodes ++ (newENodes s A θ).toArray
  anodes := s.anodes.push
    { parent := i, assertion := a, base := s.baseOf s.anodes.size, sub := θ,
      children := (List.range A.hyps.length).map (s.enodes.size + ·),
      conds := nodeConds A (s.baseOf s.anodes.size) θ }
  freshBase := s.freshBase
  stride := s.stride

/-- Tries one assertion at an expression node: an assertion node if the renamed
conclusion unifies with the expression, with the hypotheses under the unifier as new
expression nodes. -/
def tryAssertion (U : Unification) (db : Database) (i a : ℕ) (s : State) : State :=
  match db.asserts[a]? with
  | none => s
  | some A =>
    match U.mgu [(s.enodes[i]!.expr, A.concl.rename (s.baseOf s.anodes.size))] with
    | none => s
    | some θ => addNode i a s A θ

/-- Expands one expression node against every assertion of the database. -/
def expandNode (U : Unification) (db : Database) (i : ℕ) (s : State) : State :=
  let s := { s with enodes := s.enodes.modify i fun n => { n with expanded := true } }
  (List.range db.asserts.length).foldl (fun s a => tryAssertion U db i a s) s

/-- One round of expansion: every expression node not yet expanded. The nodes made in
the round wait for the next one, which is breadth first. -/
def expandAll (U : Unification) (db : Database) (s : State) : State :=
  ((List.range s.enodes.size).filter fun i => !s.enodes[i]!.expanded).foldl
    (fun s i => expandNode U db i s) s

/-- The state after `n` rounds. -/
def run (U : Unification) (db : Database) (st : Statement) : ℕ → State
  | 0 => init db st
  | n + 1 => expandAll U db (run U db st n)

/-- The leaf entries of an expression node: the hypotheses of the statement that it
unifies with (Definition 4.2, a hypothesis used as a fact). -/
def leafEntries (U : Unification) (st : Statement) (i : ℕ) (e : Exp) : List Entry :=
  (List.range st.hyps.length).filterMap fun h =>
    (U.mgu [(e, st.hyps[h]!)]).map fun θ => { tree := .leaf i h, sub := θ, conds := [] }

/-- Every choice of one element from each list. -/
def tuples : List (List Entry) → List (List Entry)
  | [] => [[]]
  | l :: ls => l.flatMap fun x => (tuples ls).map (x :: ·)

/-- The entries of an assertion node: for every tuple of entries of its children, the
join of their answers with `θ_a`, when it exists and no condition fails under it. -/
def anodeEntries (U : Unification) (c : Consts) (j : ℕ) (a : ANode) (childEntries : List (List Entry)) :
    List Entry :=
  (tuples childEntries).filterMap fun tup =>
    match U.joinAll (a.sub :: tup.map (·.sub)) with
    | none => none
    | some θ =>
      let conds := (a.conds ++ tup.flatMap (·.conds)).map (Cond.apply θ)
      if conds.all (fun k => decide (k.Holds c)) then
        some { tree := .node j (tup.map (·.tree)), sub := θ, conds }
      else none

/-- The assertion nodes whose expression node is `i`. -/
def aChildren (s : State) (i : ℕ) : List ℕ :=
  (List.range s.anodes.size).filter fun j => s.anodes[j]!.parent == i

/-- The SPT set of an expression node, down to a depth: its leaf entries, and the
entries of its assertion nodes, each from the SPT sets of the node's children. The
depth of the tree is below the number of its expression nodes, so `enodes.size` is
depth enough (`rootEntries`). -/
def sptE (U : Unification) (st : Statement) (s : State) : ℕ → ℕ → List Entry
  | 0, _ => []
  | fuel + 1, i =>
    leafEntries U st i s.enodes[i]!.expr ++ (aChildren s i).flatMap fun j =>
      anodeEntries U st.consts j s.anodes[j]! (s.anodes[j]!.children.map fun c => sptE U st s fuel c)

/-- The SPT set of an assertion node. -/
def sptA (U : Unification) (st : Statement) (s : State) (fuel j : ℕ) : List Entry :=
  anodeEntries U st.consts j s.anodes[j]! (s.anodes[j]!.children.map fun c => sptE U st s fuel c)

/-- The entries at the root: the answers. -/
def rootEntries (U : Unification) (st : Statement) (s : State) : List Entry :=
  sptE U st s s.enodes.size 0

/-- The substitution of a step for the binders of its assertion: what the renamed
binder gets under `θ_a` and then the answer `θ`. -/
def stepSub (db : Database) (a : ANode) (θ : Subst) : Subst :=
  let A := db.asserts[a.assertion]!
  Subst.ofFun A.vars.toFinset
    (fun x => if x ∈ A.vars then θ.apply (a.sub.apply (.var (renamed a.base x))) else .var x)
    (fun x hx => by simp [List.mem_toFinset.not.1 hx])

mutual
/-- The proof that an entry stands for: its tree with every expression under the
answer (the draft's `v(T)[θ]`). -/
def proofOf (db : Database) (s : State) (θ : Subst) : SptTree → PTree
  | .leaf i h => .hyp h (θ.apply s.enodes[i]!.expr)
  | .node j cs =>
    let a := s.anodes[j]!
    .step (θ.apply s.enodes[a.parent]!.expr) a.assertion (stepSub db a θ) (proofsOf db s θ cs)
def proofsOf (db : Database) (s : State) (θ : Subst) : List SptTree → List PTree
  | [] => []
  | t :: ts => proofOf db s θ t :: proofsOf db s θ ts
end

end State

/-- The proof of an entry. -/
def Entry.proof (db : Database) (s : State) (E : Entry) : PTree :=
  State.proofOf db s E.sub E.tree

end Theory
