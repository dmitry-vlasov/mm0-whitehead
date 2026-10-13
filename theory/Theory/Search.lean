/-
The reference engine (`docs/THEORY.md`, "The reference engine"): the proof variant tree
and the substitution proof trees of the draft's Definitions 4.1 and 4.2, computed round
by round, breadth first, every entry kept. Pure, and it runs.

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

structure State where
  enodes : Array ENode
  anodes : Array ANode
  /-- The SPT entries of each expression node and of each assertion node. -/
  spt : Array (List Entry)
  sptA : Array (List Entry)
  /-- The number of the next fresh variable. -/
  fresh : ℕ

namespace State

/-- The tree with the statement's conclusion at the root. The fresh variables start
above every variable of the statement. -/
def init (st : Statement) : State where
  enodes := #[{ expr := st.concl, parent := none, expanded := false }]
  anodes := #[]
  spt := #[[]]
  sptA := #[]
  fresh := (st.concl.vars ∪ (st.hyps.map Exp.vars).foldr (· ∪ ·) ∅).sup Var.id + 1

/-- The renamed variable of an assertion node. -/
def renamed (base : ℕ) (x : Var) : Var := ⟨base + x.id, x.ty⟩

/-- Expands one expression node against every assertion of the database: an assertion
node for each whose renamed conclusion unifies with the expression, with the
hypotheses under the unifier as new expression nodes. -/
def expandNode (U : Unification) (db : Database) (i : ℕ) (s : State) : State := Id.run do
  let mut s := { s with enodes := s.enodes.modify i fun n => { n with expanded := true } }
  let e := s.enodes[i]!.expr
  for a in [0:db.asserts.length] do
    let A := db.asserts[a]!
    let b := s.fresh
    match U.mgu [(e, A.concl.rename b)] with
    | none => pure ()
    | some θ =>
      let ai := s.anodes.size
      let mut children : List ℕ := []
      let mut enodes := s.enodes
      for j in [0:A.hyps.length] do
        children := children ++ [enodes.size]
        enodes := enodes.push { expr := θ.apply (A.hyps[j]!.rename b), parent := some (ai, j), expanded := false }
      let conds := A.pairs.map fun p => (θ.apply (.var (renamed b p.1)), θ.apply (.var (renamed b p.2)))
      s := { s with enodes,
                    anodes := s.anodes.push { parent := i, assertion := a, base := b, sub := θ, children, conds },
                    spt := s.spt ++ Array.replicate A.hyps.length [],
                    sptA := s.sptA.push [],
                    fresh := b + (A.vars.map (·.id)).foldl max 0 + 1 }
  return s

/-- One round of expansion: every expression node not yet expanded. The nodes made in
the round wait for the next one, which is breadth first. -/
def expandAll (U : Unification) (db : Database) (s : State) : State := Id.run do
  let todo := (List.range s.enodes.size).filter fun i => !s.enodes[i]!.expanded
  let mut s := s
  for i in todo do
    s := expandNode U db i s
  return s

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

/-- The SPT sets of every node, computed from scratch: expression nodes from the last
made to the root, since the children of an assertion node were made after the node's
own expression node. -/
def propagate (U : Unification) (st : Statement) (s : State) : State := Id.run do
  let mut s := { s with spt := Array.replicate s.enodes.size [], sptA := Array.replicate s.anodes.size [] }
  for k in [0:s.enodes.size] do
    let i := s.enodes.size - 1 - k
    let aChildren := (List.range s.anodes.size).filter fun j => s.anodes[j]!.parent == i
    for j in aChildren do
      let a := s.anodes[j]!
      s := { s with sptA := s.sptA.set! j (anodeEntries U st.consts j a (a.children.map fun c => s.spt[c]!)) }
    s := { s with spt := s.spt.set! i (leafEntries U st i s.enodes[i]!.expr ++ aChildren.flatMap fun j => s.sptA[j]!) }
  return s

/-- A round: expand, then propagate. -/
def step (U : Unification) (db : Database) (st : Statement) (s : State) : State :=
  propagate U st (expandAll U db s)

/-- The state after `n` rounds. -/
def run (U : Unification) (db : Database) (st : Statement) : ℕ → State
  | 0 => init st
  | n + 1 => step U db st (run U db st n)

/-- The entries at the root: the answers. -/
def rootEntries (s : State) : List Entry := s.spt[0]!

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
  | .leaf i _ => .hyp (θ.apply s.enodes[i]!.expr)
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
