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

/-- `RuProverProof`: a substitution proof tree. -/
inductive Proof where
  /-- `RuProverProofTop`: the expression node `node` is premise `premise` under `sub`;
  `expr` is the expression of the node under `sub`. -/
  | top (node : Nat) (expr : Exp) (premise : Nat) (sub : Subst)
  /-- `RuProverProofStmt`: the expression node `node` is proved by the proof `child` of
  one of its assertion nodes. -/
  | stmt (node : Nat) (expr : Exp) (sub : Subst) (child : Proof)
  /-- `RuProverProofProp`: the assertion node `node` with a proof for each premise.
  `conds` says that this step or one below it applies an assertion that has conditions
  on bound variables. -/
  | prop (node : Nat) (sub : Subst) (children : Array Proof) (conds : Bool)
  deriving Inhabited

namespace Proof

def sub : Proof → Subst
  | .top _ _ _ s => s
  | .stmt _ _ s _ => s
  | .prop _ s _ _ => s

def node : Proof → Nat
  | .top n _ _ _ => n
  | .stmt n _ _ _ => n
  | .prop n _ _ _ => n

/-- The expression that a proof on an expression node proves. -/
def expr : Proof → Exp
  | .top _ e _ _ => e
  | .stmt _ e _ _ => e
  | .prop _ _ _ _ => default

/-- Does the proof apply an assertion with conditions on bound variables? -/
def conds : Proof → Bool
  | .top _ _ _ _ => false
  | .stmt _ _ _ child => child.conds
  | .prop _ _ _ c => c

end Proof

/-- `RuProverProp`: an assertion applied to the expression node `parent`. -/
structure PropNode where
  assertion : Nat
  /-- The part of the unifier on the variables of the goal. -/
  sub : Subst
  /-- The part of the unifier on the variables of the assertion: every one of them, the
  ones that the unification left free being renamed to fresh variables. -/
  outer : Subst
  parent : Nat
  children : Array Nat := #[]
  proofs : Array Proof := #[]
  /-- The substitutions of `proofs`, to keep one proof for each (`ruProofSubKey`). -/
  keys : Std.HashSet (Array Nat) := {}
  expanded : Bool := false
  deriving Inhabited

/-- `RuProverExp`, and `RuProverRoot` for the node without a parent. -/
structure HypNode where
  /-- Which premise of the parent's assertion this is. -/
  ind : Nat
  expr : Exp
  parent : Option Nat
  children : Array Nat := #[]
  proofs : Array Proof := #[]
  deriving Inhabited

/-- `RuProofTree`: a proof read off the tree. Where Russell keeps the statement of each
step, this keeps what the proof format of MM0 needs: the expression for every binder of
the assertion. -/
inductive ProofTree where
  | hyp (ind : Nat)
  | step (assertion : Nat) (args : Array Exp) (children : Array ProofTree)
  deriving Inhabited

namespace ProofTree

/-- `ruApplySubst2ProofNode` -/
partial def subst (s : Subst) : ProofTree → ProofTree
  | .hyp i => .hyp i
  | .step a args children => .step a (args.map s.apply) (children.map (subst s))

/-- The number of steps. -/
partial def size : ProofTree → Nat
  | .hyp _ => 0
  | .step _ _ children => children.foldl (init := 1) (· + ·.size)

/-- The proof as text, a step per line, for traces. -/
partial def render (db : Db) (t : ProofTree) (indent : String := "") : String :=
  match t with
  | .hyp i => s!"{indent}hypothesis {i}\n"
  | .step a args children =>
    let head := s!"{indent}{db.asserts[a]!.name} [{", ".intercalate (args.map (db.showExp ·)).toList}]\n"
    children.foldl (init := head) fun acc c => acc ++ c.render db (indent ++ "  ")

/-- The variables that are left in the proof, each once. -/
partial def vars (t : ProofTree) (acc : Array Nat := #[]) : Array Nat :=
  match t with
  | .hyp _ => acc
  | .step _ args children =>
    let acc := args.foldl (init := acc) fun acc e =>
      e.nodes.foldl (init := acc) fun acc n => if Node.isVar n && !acc.contains n then acc.push n else acc
    children.foldl (init := acc) fun acc c => c.vars acc

end ProofTree

/-- The canonical form of a substitution, as a key (`ruProofSubKey`). -/
def Subst.key (s : Subst) : Array Nat :=
  let ids := (s.map.fold (init := #[]) fun acc v _ => acc.push v).qsort (· < ·)
  ids.foldl (init := #[]) fun acc v =>
    let e := s.map[v]!.exp
    (acc.push v).push e.size ++ e.nodes

end Whitehead.Prove
