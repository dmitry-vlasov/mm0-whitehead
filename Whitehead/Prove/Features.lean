/-
The features of a variant, for the learned ranking layer (`docs/DESIGN.md`, "The learned
ranking layer"). One function serves the export of the data and the search, so that a
model is given in the search what it was trained on.

A variant is an assertion node at a goal node, expanded or not; its features read the
node, its rule, the unifier's bindings (its new goals, without expanding it) and what
the proofs before the theorem say (`Uses`). Every feature that counts proofs counts only
those before the theorem, so that a model trained on early theorems and tested on later
ones is tested out of sample. They are relative quantities, so that they mean the same in
every file: a symbol is weighted by how rare it is in its own file.
-/
import Whitehead.Prove.Filter
import Whitehead.Prove.Combinators

namespace Whitehead.Prove

/-- What the features read of a rule: the terms of its statement, the nodes of its
conclusion that are not variables, whether that conclusion is a bare variable, and the
weight of its terms. It depends on the rule alone, so it is found once. -/
structure RuleInfo where
  terms : Array Nat := #[]
  conclNonvar : Nat := 0
  conclIsVar : Bool := false
  weight : Float := 0
  deriving Inhabited

/-- How rare each term is in a file: in how many statements of assertions it occurs; and
what the features read of each assertion of the file, by its number. -/
structure SymbolStats where
  df : Array Nat := #[]
  statements : Nat := 0
  rules : Array RuleInfo := #[]
  deriving Inhabited

/-- The terms that occur in `e`, each once. -/
def Exp.terms (e : Exp) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for n in e.nodes do
    if !Node.isVar n && !Node.isConst n then
      let t := Node.appId n
      if !out.contains t then out := out.push t
  return out

/-- The terms of a rule's statement: of its conclusion and its hypotheses. -/
def Assertion.terms (a : Assertion) : Array Nat :=
  (a.hyps.push a.concl).foldl (init := #[]) fun acc e =>
    e.terms.foldl (init := acc) fun acc t => if acc.contains t then acc else acc.push t

/-- The weight of term `t`: the logarithm of how rare it is. -/
def SymbolStats.idf (s : SymbolStats) (t : Nat) : Float :=
  Float.log ((s.statements.toFloat + 1) / ((s.df[t]?.getD 0).toFloat + 1))

def SymbolStats.ruleInfo (s : SymbolStats) (a : Assertion) : RuleInfo :=
  let terms := a.terms
  { terms, conclNonvar := (a.concl.nodes.filter fun n => !Node.isVar n).size, conclIsVar := a.concl.isVar,
    weight := terms.foldl (init := 0) fun acc t => acc + s.idf t }

def SymbolStats.ofDb (db : Db) : SymbolStats := Id.run do
  let mut df := Array.replicate db.terms.size 0
  let mut n := 0
  for a in db.asserts do
    if a.pseudo.isSome then continue
    n := n + 1
    for t in a.terms do
      if t < df.size then df := df.modify t (· + 1)
  let s : SymbolStats := { df, statements := n }
  return { s with rules := db.asserts.map s.ruleInfo }

/-- What the features read of a goal node: its terms and variables, its size, whether it
has a variable, the depth of its variants, and how many it has. It is the same for all its
variants, so it is found once for them. -/
structure GoalInfo where
  terms : Std.HashSet Nat := {}
  vars : Std.HashSet Nat := {}
  size : Nat := 0
  hasVar : Bool := false
  depth : Nat := 1
  variants : Nat := 0
  deriving Inhabited

def Env.goalInfo (env : Env) (h : Nat) : GoalInfo := Id.run do
  let goalNode := env.hyps[h]!
  let goal := goalNode.expr
  -- the assertion nodes from the root to a variant of the goal, it counted
  let mut depth := 1
  let mut g := h
  for _ in [0:env.hyps.size] do
    match env.hyps[g]!.parent with
    | some q =>
      depth := depth + 1
      g := env.props[q]!.parent
    | none => break
  return { terms := goal.terms.foldl (init := {}) (·.insert ·),
           vars := (goal.nodes.filter Node.isVar).foldl (init := {}) fun acc n => acc.insert (Node.varId n),
           size := goal.size, hasVar := goal.nodes.any Node.isVar, depth, variants := goalNode.children.size }

/-- The names of the features, in the order of `Env.features`. -/
def featureNames : Array String := #[
  "is_assertion",   -- 1 for an assertion of the file
  "is_conversion",  -- 1 for a conversion rule (`Pseudo`) or an unfolding, which the file does not state
  "uses_log",       -- log(1 + the proofs before the theorem that use the assertion)
  "never_used",     -- 1 if none does
  "recency_log",    -- log(1 + how many theorems ago the latest such proof is), 0 if none
  "premises",       -- the new goals
  "goals_bare",     -- new goals that are a bare variable
  "goals_ground",   -- new goals without a variable
  "goals_closable", -- new goals, not bare, that a premise of the theorem unifies with
  "goals_size",     -- the nodes of the new goals, together
  "goals_size_max", -- of the largest
  "new_vars",       -- variables of the new goals that the goal does not have
  "concl_nonvar",   -- the nodes of the rule's conclusion that are not variables
  "concl_is_var",   -- 1 if the rule's conclusion is a bare variable
  "goal_size",      -- the nodes of the goal
  "spec_ratio",     -- concl_nonvar / goal_size
  "goal_meta",      -- 1 if the goal has a variable (a metavariable)
  "depth",          -- the assertion nodes from the root to the variant, it counted
  "rule_terms",     -- the terms of the rule's statement
  "shared_terms",   -- of them, those the goal has
  "shared_idf",     -- the share of the rule's weight that the goal has
  "extra_idf",      -- the weight of the terms the rule brings that the goal lacks
  "siblings_log"    -- log(1 + the variants of the goal)
]

/-- `f` to four significant digits: what the data keeps, and so what a model is given in
the search too. -/
def round4 (f : Float) : Float :=
  if f == 0 || f == f.round then f
  else
    let scale := Float.pow 10 (3 - (Float.log10 f.abs).floor)
    (f * scale).round / scale

/-- A feature as text: an integer as one, any other number as `round4` leaves it, so that
the data stays small. -/
def featureText (f : Float) : String :=
  if f == f.round && f.abs < 1e9 then toString f.toInt64.toInt
  else
    let r := round4 f
    let cs := (toString r).toList
    -- without the trailing zeros of the decimal part
    if !cs.contains '.' then String.ofList cs
    else
      let t := (cs.reverse.dropWhile (· == '0')).reverse
      String.ofList (if t.getLast? == some '.' then t.dropLast else t)

/-- The features of variant `p`, in the order of `featureNames`; `gi` is its goal's
(`Env.goalInfo`). -/
def Env.variantFeatures (env : Env) (stats : SymbolStats) (gi : GoalInfo) (p : Nat) : Array Float := Id.run do
  let prop := env.props[p]!
  let v := env.propView p
  let thm := env.task.limit
  let isAssertion := match prop.step with
    | .assertion a => (env.db.asserts[a]?.bind (·.pseudo)).isNone
    | _ => false
  let uses := v.uses
  let latest := match prop.step with
    | .assertion a => env.uses.latest a thm
    | _ => 0
  let goals := v.goals.get
  let isVar (e : Exp) : Bool := e.nodes.any Node.isVar
  let newVars := goals.foldl (init := (#[] : Array Nat)) fun acc g =>
    g.nodes.foldl (init := acc) fun acc n =>
      if !Node.isVar n then acc
      else
        let x := Node.varId n
        if gi.vars.contains x || acc.contains x then acc else acc.push x
  -- the rule's own part: from the file's table, or for an unfolding's rule, found here
  let ri := match prop.step with
    | .assertion a => stats.rules[a]?.getD (stats.ruleInfo prop.rule)
    | _ => stats.ruleInfo prop.rule
  let conclNonvar := ri.conclNonvar
  let ruleTerms := ri.terms
  let shared := ruleTerms.filter gi.terms.contains
  let w (ts : Array Nat) : Float := ts.foldl (init := 0) fun acc t => acc + stats.idf t
  let ruleW := ri.weight
  let b (x : Bool) : Float := if x then 1 else 0
  let n (x : Nat) : Float := x.toFloat
  return Array.map round4 #[
    b isAssertion,
    b (!isAssertion),
    Float.log (1 + n uses),
    b (isAssertion && uses == 0),
    if latest == 0 then 0 else Float.log (1 + n (thm + 1 - latest)),
    n goals.size,
    n (goals.filter (·.isVar)).size,
    n (goals.filter (!isVar ·)).size,
    n v.closable.get,
    n (goals.foldl (init := 0) (· + ·.size)),
    n (goals.foldl (init := 0) fun m g => max m g.size),
    n newVars.size,
    n conclNonvar,
    b ri.conclIsVar,
    n gi.size,
    n conclNonvar / n (max 1 gi.size),
    b gi.hasVar,
    n gi.depth,
    n ruleTerms.size,
    n shared.size,
    if ruleW == 0 then 0 else w shared / ruleW,
    ruleW - w shared,
    Float.log (1 + n gi.variants)
  ]

/-- The features of variant `p`, in the order of `featureNames`. -/
def Env.features (env : Env) (stats : SymbolStats) (p : Nat) : Array Float :=
  env.variantFeatures stats (env.goalInfo env.props[p]!.parent) p

end Whitehead.Prove
