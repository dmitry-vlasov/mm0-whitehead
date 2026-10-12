/-
The proof variant tree: a port of `russell-flow/src/ru/prover/core/tree.flow`.

Expression nodes (`RuProverRoot`, `RuProverExp`) and assertion nodes (`RuProverProp`)
alternate. The nodes are kept in two arrays and refer to each other by their numbers;
Russell has mutable vectors inside the nodes and pointers both ways. The proofs on the
nodes (`RuProverProof`, the substitution proof trees of the paper) are immutable trees,
as in Russell.
-/
import Whitehead.Prove.Db

namespace Whitehead.Prove

/-- A condition on a bound variable that a proof still depends on: the name `name` (a
node: the constant for a bound variable of the task, or a variable) must not occur in
`expr`. It is open as long as a variable in it can still be replaced. -/
structure Cond where
  name : Nat
  expr : Exp
  deriving BEq, Inhabited

/-- `RuProofTree`: a proof read off the tree. Where Russell keeps the statement of each
step, this keeps what the proof format of MM0 needs: the expression for every binder of
the assertion; for an unfolding, the def, where in the statement it is unfolded, and
the expressions for its arguments and dummies. -/
inductive ProofTree where
  | hyp (ind : Nat)
  | step (assertion : Nat) (args : Array Exp) (children : Array ProofTree)
  /-- The statement is `child`'s statement with, at `path`, the def `term` applied to
  `args` where the child has its value (`unfold`), or the value where the child has the
  def (fold). `dummies` are the names given to the dummies of the def. -/
  | conv (term : Nat) (path : Array Nat) (unfold : Bool) (args dummies : Array Exp) (child : ProofTree)
  deriving Inhabited

namespace ProofTree

/-- `ruApplySubst2ProofNode` -/
partial def subst (s : Subst) : ProofTree → ProofTree
  | .hyp i => .hyp i
  | .step a args children => .step a (args.map s.apply) (children.map (subst s))
  | .conv t path unfold args dummies child =>
    .conv t path unfold (args.map s.apply) (dummies.map s.apply) (subst s child)

/-- The number of steps; an unfolding is one. -/
partial def size : ProofTree → Nat
  | .hyp _ => 0
  | .step _ _ children => children.foldl (init := 1) (· + ·.size)
  | .conv _ _ _ _ _ child => 1 + child.size

/-- The proof as text, a step per line, for traces. -/
partial def render (db : Db) (t : ProofTree) (indent : String := "") : String :=
  match t with
  | .hyp i => s!"{indent}hypothesis {i}\n"
  | .step a args children =>
    let head := s!"{indent}{db.asserts[a]!.name} [{", ".intercalate (args.map (db.showExp ·)).toList}]\n"
    children.foldl (init := head) fun acc c => acc ++ c.render db (indent ++ "  ")
  | .conv t path unfold args dummies child =>
    let head := s!"{indent}{if unfold then "unfold" else "fold"} {db.terms[t]!.name} at {path} \
      [{", ".intercalate ((args ++ dummies).map (db.showExp ·)).toList}]\n"
    head ++ child.render db (indent ++ "  ")

/-- The variables that are left in the proof, each once, in the order of their first
occurrence, after those of `acc`. -/
partial def vars (t : ProofTree) (acc : Array Nat := #[]) : Array Nat :=
  (go t (acc, acc.foldl (init := {}) fun s v => s.insert v)).1
where
  go (t : ProofTree) (acc : Array Nat × Std.HashSet Nat) : Array Nat × Std.HashSet Nat :=
    match t with
    | .hyp _ => acc
    | .step _ args children => children.foldl (init := exps args acc) fun acc c => go c acc
    | .conv _ _ _ args dummies child => go child (exps (args ++ dummies) acc)
  exps (es : Array Exp) (acc : Array Nat × Std.HashSet Nat) : Array Nat × Std.HashSet Nat :=
    es.foldl (init := acc) fun acc e =>
      e.nodes.foldl (init := acc) fun (list, seen) n =>
        if Node.isVar n && !seen.contains n then (list.push n, seen.insert n) else (list, seen)

end ProofTree

/-- `RuProverProof`: a substitution proof tree. -/
inductive Proof where
  /-- `RuProverProofTop`: the expression node `node` is premise `premise` under `sub`;
  `expr` is the expression of the node under `sub`. -/
  | top (node : Nat) (expr : Exp) (premise : Nat) (sub : Subst)
  /-- `RuProverProofStmt`: the expression node `node` is proved by the proof `child` of
  one of its assertion nodes. -/
  | stmt (node : Nat) (expr : Exp) (sub : Subst) (child : Proof)
  /-- `RuProverProofProp`: the assertion node `node` with a proof for each premise.
  `conds` are the conditions on bound variables, of this step and of those below it,
  that are still open under `sub`. -/
  | prop (node : Nat) (sub : Subst) (children : Array Proof) (conds : Array Cond)
  /-- `RuProverProofForward`: the expression node `node` is an instance of a fact of the
  forward front, the fact with the node `fact`; `tree` is the proof of the fact, already
  under `sub`, and `conds` are the conditions that it left open. -/
  | forward (node : Nat) (expr : Exp) (sub : Subst) (tree : ProofTree) (conds : Array Cond) (fact : Nat)
  deriving Inhabited

namespace Proof

def sub : Proof → Subst
  | .top _ _ _ s => s
  | .stmt _ _ s _ => s
  | .prop _ s _ _ => s
  | .forward _ _ s _ _ _ => s

def node : Proof → Nat
  | .top n _ _ _ => n
  | .stmt n _ _ _ => n
  | .prop n _ _ _ => n
  | .forward n _ _ _ _ _ => n

/-- The expression that a proof on an expression node proves. -/
def expr : Proof → Exp
  | .top _ e _ _ => e
  | .stmt _ e _ _ => e
  | .prop _ _ _ _ => default
  | .forward _ e _ _ _ _ => e

/-- The conditions on bound variables that are still open in a proof. -/
def conds : Proof → Array Cond
  | .top _ _ _ _ => #[]
  | .stmt _ _ _ child => child.conds
  | .prop _ _ _ c => c
  | .forward _ _ _ _ c _ => c

end Proof

/-- What an assertion node applies: an assertion of the file, or an unfolding — the
def `term` unfolded (`unfold`) or folded at node `pos` of the parent's expression. -/
inductive Step where
  | assertion (id : Nat)
  | conv (term : Nat) (pos : Nat) (unfold : Bool)
  deriving BEq, Inhabited

/-- `RuProverProp`: an assertion applied to the expression node `parent`. -/
structure PropNode where
  step : Step
  /-- The rule applied: the assertion of the file, or for an unfolding the rule made for
  it (`convRule` in `Expand.lean`): "the parent's expression with the def here" from
  "the same with the value here", or the converse, over fresh variables. -/
  rule : Assertion
  /-- The part of the unifier on the variables of the goal. -/
  sub : Subst := {}
  /-- The part of the unifier on the variables of the assertion: every one of them, the
  ones that the unification left free being renamed to fresh variables. -/
  outer : Subst := {}
  /-- For a candidate that is not expanded yet: the bindings that unify its conclusion
  with the parent's expression, as the walk of the index made them. `sub` and `outer`,
  and the fresh variables, are made from them when the node is expanded (`splitProp`),
  as in Russell since `ba2dd6a7`: a goal unifies with thousands of conclusions and few
  of them are ever expanded. -/
  unif : Option Binds := none
  parent : Nat
  children : Array Nat := #[]
  /-- The proofs of the node: one for each substitution of the parent's variables with
  its open conditions on bound variables (`proofKey` in `Proofs.lean`). -/
  proofs : Array Proof := #[]
  /-- The keys of `proofs`. -/
  keys : Std.HashSet (Array Nat) := {}
  expanded : Bool := false
  /-- For the joins (`catchUp` and `addProof` in `Proofs.lean`): for each child, the
  variables of its expression that the expression of another child has too; an index of
  the proofs of the child by what they put for those variables; and how many of its
  proofs are in the index. Empty until the first join. -/
  joinShared : Array (Array Nat) := #[]
  joinIndex : Array (Index Nat) := #[]
  joinCount : Array Nat := #[]
  deriving Inhabited

/-- `RuProverExp`, and `RuProverRoot` for node 0. A fact of the forward front is such a
node too, without a parent (Russell gives it the sentinel `ruNoProverProp`). -/
structure HypNode where
  /-- Which premise of the parent's assertion this is. -/
  ind : Nat
  expr : Exp
  parent : Option Nat
  children : Array Nat := #[]
  proofs : Array Proof := #[]
  /-- For a fact of the forward front: its proof, read off once (`ruMakeProofTree`,
  which Russell calls at every use). A fact has one proof: another derivation of the
  same statement is another fact. -/
  factProof : Option ProofTree := none
  deriving Inhabited

/-- The canonical form of a substitution, as a key (`ruProofSubKey`). -/
def Subst.key (s : Subst) : Array Nat :=
  let ids := (s.map.fold (init := #[]) fun acc v _ => acc.push v).qsort (· < ·)
  ids.foldl (init := #[]) fun acc v =>
    let e := s.map[v]!.exp
    (acc.push v).push e.size ++ e.nodes

end Whitehead.Prove
