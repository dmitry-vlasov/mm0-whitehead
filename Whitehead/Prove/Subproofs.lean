/-
The subproofs of a file, each with its most general lemma (`docs/DESIGN.md`, "Phase 4",
"Proof rails"): the measurements that decide between a lemma index and the replay of
fragments.

A subproof here is what is below a node of a proof: the node's assertion and the
subproofs of its children, down to the hypotheses of the theorem. Subproofs are
hash-consed across the whole file, so that the same assertions in the same positions are
one subproof wherever they occur; a hypothesis of the theorem is one generic leaf.

The most general lemma of a subproof is the statement it proves with every hypothesis
leaf open: the assertion at its top, with each premise unified with the conclusion of the
lemma below it, its variables renamed apart, and the hypothesis leaves becoming the
lemma's hypotheses. It is computed from the lemmas of the children, once per distinct
subproof. Conditions on bound variables are not kept: the lemmas are for measuring, not
for proofs.
-/
import Whitehead.Prove.Prove

namespace Whitehead.Prove

/-- A lemma: hypotheses and a conclusion, over the variables `0, 1, ...` in the order
of their first occurrence (in the conclusion, then in the hypotheses). -/
structure Lemma where
  hyps : Array Exp
  concl : Exp
  deriving Inhabited

structure Subproofs where
  /-- For each distinct subproof, from 1, its assertion and the subproofs of its children;
  0 is the hypothesis leaf. -/
  nodes : Array (Nat × Array Nat) := #[(0, #[])]
  /-- Its number of steps. -/
  sizes : Array Nat := #[0]
  /-- The theorem in whose proof it first occurs. -/
  first : Array Nat := #[0]
  table : Std.HashMap (Array Nat) Nat := {}
  /-- For each theorem whose proof is read: its number and the subproof of its proof. -/
  roots : Array (Nat × Nat) := #[]
  /-- In how many proofs it occurs, and the theorem in whose proof it occurs the second
  time (`noRank` if it occurs once): the lemmas known to recur before a theorem. -/
  proofs : Array Nat := #[0]
  second : Array Nat := #[0]
  deriving Inhabited

namespace Subproofs

/-- The subproof of `sk`, made distinct, in the proof of theorem `thm`. -/
partial def intern (sp : Subproofs) (thm : Nat) (sk : Skeleton) : Nat × Subproofs :=
  match sk with
  | .hyp _ => (0, sp)
  | .step t cs => Id.run do
    let mut sp := sp
    let mut kids := #[]
    let mut size := 1
    for c in cs do
      let (k, sp') := sp.intern thm c
      sp := sp'
      kids := kids.push k
      size := size + sp.sizes[k]!
    let key := kids.push t
    match sp.table[key]? with
    | some k => return (k, sp)
    | none =>
      let k := sp.nodes.size
      return (k, { sp with nodes := sp.nodes.push (t, kids), sizes := sp.sizes.push size,
                           first := sp.first.push thm, table := sp.table.insert key k,
                           proofs := sp.proofs.push 0, second := sp.second.push noRank })

/-- The subproofs of every proof of the file that `db.skeleton` reads. -/
def ofDb (db : Db) : Subproofs := Id.run do
  let mut sp : Subproofs := {}
  for s in db.file.stmts do
    let .thm _ := s.kind | continue
    let .ok (some sk) := db.skeleton s | continue
    let (k, sp') := sp.intern s.index sk
    sp := { sp' with roots := sp'.roots.push (s.index, k) }
    -- each subproof of this proof once: one more proof that has it
    let mut seen : Std.HashSet Nat := {}
    let mut stack := #[k]
    while h : 0 < stack.size do
      let j := stack[stack.size - 1]
      stack := stack.pop
      if j == 0 || seen.contains j then continue
      seen := seen.insert j
      if sp.proofs[j]! == 1 then sp := { sp with second := sp.second.set! j s.index }
      sp := { sp with proofs := sp.proofs.modify j (· + 1) }
      stack := stack ++ sp.nodes[j]!.2
  return sp

end Subproofs

/-- The variables of `e` moved up by `base`. -/
def Exp.shiftVars (e : Exp) (base : Nat) : Exp :=
  ⟨e.nodes.map fun n => if Node.isVar n then Node.var (base + Node.varId n) (Node.ty n) else n⟩

/-- `s` applied until nothing changes, at most a few times. -/
def Subst.applyAll (s : Subst) (e : Exp) (fuel : Nat := 8) : Exp := Id.run do
  let mut e := e
  for _ in [0:fuel] do
    if !s.affects e then break
    e := s.apply e
  return e

/-- The lemma with its variables numbered `0, 1, ...` by their first occurrence. -/
def Lemma.canonical (l : Lemma) : Lemma := Id.run do
  let mut map : Std.HashMap Nat Nat := {}
  for e in #[l.concl] ++ l.hyps do
    for n in e.nodes do
      if Node.isVar n && !map.contains n then map := map.insert n (Node.var map.size (Node.ty n))
  let rename (e : Exp) : Exp := ⟨e.nodes.map fun n => if Node.isVar n then map[n]?.getD n else n⟩
  return { hyps := l.hyps.map rename, concl := rename l.concl }

/-- The most general lemma of assertion `a` over the subproofs `kids`, whose lemmas are
in `lemmas` (`none` for one that could not be made). `none` if a premise does not unify
with the lemma below it. -/
def composeLemma (db : Db) (lemmas : Array (Option Lemma)) (a : Nat) (kids : Array Nat) : Option Lemma := do
  let rule := db.asserts[a]!
  -- the rule's variables first, then each child's, apart
  let mut base := rule.vars.size
  let mut sub : Subst := {}
  let mut hyps : Array Exp := #[]
  for i in [0:kids.size] do
    let premise := rule.hyps[i]!
    if kids[i]! == 0 then
      hyps := hyps.push premise
    else
      let l ← lemmas[kids[i]!]!
      let width := l.concl.vars.size + (l.hyps.foldl (init := 0) fun m h => m + h.vars.size)
      let concl := l.concl.shiftVars base
      sub ← unifyExps #[premise, concl] sub
      hyps := hyps ++ l.hyps.map (·.shiftVars base)
      base := base + width + 1
  return (Lemma.canonical { hyps := hyps.map (sub.applyAll ·), concl := sub.applyAll rule.concl })

/-- The lemma of every distinct subproof, in order: a subproof comes after those below it. -/
def Subproofs.lemmas (sp : Subproofs) (db : Db) : Array (Option Lemma) := Id.run do
  let mut out : Array (Option Lemma) := #[some { hyps := #[], concl := default }]
  for k in [1:sp.nodes.size] do
    let (a, kids) := sp.nodes[k]!
    out := out.push (composeLemma db out a kids)
  return out

/-! ### The measurements -/

/-- What the subproofs of a file are, and what their lemmas would do. -/
structure SubproofReport where
  distinct : Nat
  /-- Lemmas that could not be made: a premise that did not unify. -/
  failed : Nat
  /-- Lemmas whose conclusion is a bare variable, which every goal fits. -/
  bare : Nat
  /-- Distinct lemma statements, the hypotheses included. -/
  statements : Nat
  /-- Over the proofs: their nodes, each subproof once per proof, of 2 steps or more; and
  those whose subproof occurs in the proof of an earlier theorem. -/
  nodes : Nat
  coveredNodes : Nat
  /-- Their steps, a shared subproof counted each time it is used; and those inside a
  subproof that an earlier theorem's proof has. -/
  steps : Nat
  coveredSteps : Nat
  proofs : Nat
  /-- Proofs that are, whole, a subproof of an earlier theorem's proof. -/
  wholeCovered : Nat
  /-- The steps again, each subproof once per proof: the distinct subproofs of each proof,
  and those inside a subproof that an earlier theorem's proof has. -/
  distinctSteps : Nat := 0
  coveredDistinct : Nat := 0
  /-- The steps inside a subproof that occurs in two proofs before the theorem. -/
  coveredRecurring : Nat := 0
  /-- The same, each subproof once per proof. -/
  coveredRecurringDistinct : Nat := 0
  /-- Distinct subproofs in 2 proofs or more, and in 10 or more. -/
  recurring : Nat := 0
  recurring10 : Nat := 0

/-- The steps below subproof `k`, in the proof of theorem `thm`, that lie inside a
subproof occurring in an earlier theorem's proof: all of them if `k` is one, else those
of its children. `memo` keeps what is known. -/
partial def Subproofs.coveredBelow (sp : Subproofs) (known : Array Nat) (thm k : Nat) (memo : Std.HashMap Nat Nat) :
    Nat × Std.HashMap Nat Nat :=
  if k == 0 then (0, memo)
  else if let some c := memo[k]? then (c, memo)
  else if known[k]! < thm then (sp.sizes[k]!, memo.insert k sp.sizes[k]!)
  else
    let (c, memo) := sp.nodes[k]!.2.foldl (init := (0, memo)) fun (acc, memo) kid =>
      let (c, memo) := sp.coveredBelow known thm kid memo
      (acc + c, memo)
    (c, memo.insert k c)

/-- In the proof of theorem `thm`, whose subproof is `root`: its distinct subproofs, and
how many of them are inside a subproof that `known` says was known before `thm` (a
subproof is known before `thm` if `known` of it is below `thm`). -/
def Subproofs.distinctCovered (sp : Subproofs) (known : Array Nat) (thm root : Nat) : Nat × Nat := Id.run do
  -- a node may be reached first outside a known subproof and then inside one
  let mut seen : Std.HashMap Nat Bool := {}
  let mut stack : Array (Nat × Bool) := #[(root, false)]
  let mut total := 0
  let mut covered := 0
  while h : 0 < stack.size do
    let (k, inside) := stack[stack.size - 1]
    stack := stack.pop
    if k == 0 then continue
    let inside := inside || known[k]! < thm
    match seen[k]? with
    | some true => continue
    | some false => if !inside then continue
    | none => total := total + 1
    if inside then covered := covered + 1
    seen := seen.insert k inside
    stack := stack ++ sp.nodes[k]!.2.map (·, inside)
  return (total, covered)

def Subproofs.report (sp : Subproofs) (lemmas : Array (Option Lemma)) : SubproofReport := Id.run do
  let mut failed := 0
  let mut bare := 0
  let mut stmts : Std.HashSet (Array Nat) := {}
  for k in [1:sp.nodes.size] do
    match lemmas[k]! with
    | none => failed := failed + 1
    | some l =>
      if l.concl.isVar then bare := bare + 1
      stmts := stmts.insert (l.hyps.foldl (init := l.concl.nodes.push 0) fun acc h => (acc ++ h.nodes).push 0)
  let mut nodes := 0
  let mut coveredNodes := 0
  let mut steps := 0
  let mut coveredSteps := 0
  let mut wholeCovered := 0
  let mut distinctSteps := 0
  let mut coveredDistinct := 0
  let mut coveredRecurring := 0
  let mut coveredRecurringDistinct := 0
  for (thm, root) in sp.roots do
    -- the distinct subproofs of this proof, each with whether it is inside a subproof
    -- of an earlier proof (`inside`): a node is reached first from above, so a node
    -- inside is marked when its covered ancestor is popped
    let mut seen : Std.HashMap Nat Bool := {}
    let mut stack : Array (Nat × Bool) := #[(root, false)]
    while h : 0 < stack.size do
      let (k, inside) := stack[stack.size - 1]
      stack := stack.pop
      if k == 0 then continue
      let inside := inside || sp.first[k]! < thm
      match seen[k]? with
      | some true => continue
      | some false => if !inside then continue
      | none =>
        distinctSteps := distinctSteps + 1
        if sp.sizes[k]! ≥ 2 then
          nodes := nodes + 1
          if sp.first[k]! < thm then coveredNodes := coveredNodes + 1
      if inside then coveredDistinct := coveredDistinct + 1
      seen := seen.insert k inside
      stack := stack ++ sp.nodes[k]!.2.map (·, inside)
    -- the steps inside the topmost subproofs that an earlier proof has
    steps := steps + sp.sizes[root]!
    coveredSteps := coveredSteps + (sp.coveredBelow sp.first thm root {}).1
    coveredRecurring := coveredRecurring + (sp.coveredBelow sp.second thm root {}).1
    coveredRecurringDistinct := coveredRecurringDistinct + (sp.distinctCovered sp.second thm root).2
    if root != 0 && sp.first[root]! < thm then wholeCovered := wholeCovered + 1
  return { distinct := sp.nodes.size - 1, failed, bare, statements := stmts.size, nodes, coveredNodes,
           steps, coveredSteps, proofs := sp.roots.size, wholeCovered, distinctSteps, coveredDistinct,
           coveredRecurring, coveredRecurringDistinct, recurring := (sp.proofs.filter (· ≥ 2)).size,
           recurring10 := (sp.proofs.filter (· ≥ 10)).size }

/-- The index of the lemmas' conclusions, those that are not a bare variable, each ranked
so that a theorem finds only the lemmas of the proofs before it. -/
def Subproofs.lemmaIndex (sp : Subproofs) (lemmas : Array (Option Lemma)) (recurring : Bool := false) :
    Index Nat := Id.run do
  let known := if recurring then sp.second else sp.first
  let mut ix : Index Nat := {}
  for k in [1:sp.nodes.size] do
    if let some l := lemmas[k]! then
      if !l.concl.isVar && known[k]! != noRank then ix := ix.insert l.concl k (2 * known[k]! + 2)
  return ix

/-- At the goal nodes on the path of the known proof of statement `i`, a theorem: how many
assertions unify with the goal, and how many lemmas of earlier proofs (`lemmaIndex`). -/
def lemmaCounts (db : Db) (index : Index Nat) (lemmaIx recurringIx : Index Nat) (limits : Limits) (i : Nat) :
    IO (Option (Array (Nat × Nat × Nat))) := do
  let s := db.file.stmts[i]!
  match db.skeleton s with
  | .error _ | .ok none => return none
  | .ok (some skel) =>
    let env := Env.init db index (db.task s.index)
    let r ← searchWith acceptAny env (oracleAll skel (some 0)) limits
    let env := r.env
    let mut seen : Std.HashSet Nat := {}
    let mut out := #[]
    for p in [0:env.props.size] do
      let prop := env.props[p]!
      if prop.expanded && !seen.contains prop.parent then
        seen := seen.insert prop.parent
        let goal := env.hyps[prop.parent]!.expr
        out := out.push (env.hyps[prop.parent]!.children.size, (lemmaIx.unifyRaw goal (rankLimit s.index)).size,
          (recurringIx.unifyRaw goal (rankLimit s.index)).size)
    return some out

end Whitehead.Prove
