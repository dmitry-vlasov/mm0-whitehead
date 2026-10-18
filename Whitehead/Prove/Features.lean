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

/-- How rare each term is in a file: in how many statements of assertions it occurs. -/
structure SymbolStats where
  df : Array Nat := #[]
  statements : Nat := 0
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

def SymbolStats.ofDb (db : Db) : SymbolStats := Id.run do
  let mut df := Array.replicate db.terms.size 0
  let mut n := 0
  for a in db.asserts do
    if a.pseudo.isSome then continue
    n := n + 1
    for t in a.terms do
      if t < df.size then df := df.modify t (· + 1)
  return { df, statements := n }

/-- The weight of term `t`: the logarithm of how rare it is. -/
def SymbolStats.idf (s : SymbolStats) (t : Nat) : Float :=
  Float.log ((s.statements.toFloat + 1) / ((s.df[t]?.getD 0).toFloat + 1))

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

/-- The features of variant `p`, in the order of `featureNames`. -/
def Env.features (env : Env) (stats : SymbolStats) (p : Nat) : Array Float := Id.run do
  let prop := env.props[p]!
  let v := env.propView p
  let thm := env.task.limit
  let goalNode := env.hyps[prop.parent]!
  let goal := goalNode.expr
  let isAssertion := match prop.step with
    | .assertion a => (env.db.asserts[a]?.bind (·.pseudo)).isNone
    | _ => false
  let uses := v.uses
  let latest := match prop.step with
    | .assertion a => env.uses.latest a thm
    | _ => 0
  let goals := v.goals.get
  let isVar (e : Exp) : Bool := e.nodes.any Node.isVar
  let varsOf (e : Exp) : Array Nat := (e.nodes.filter Node.isVar).map Node.varId
  let goalVars := varsOf goal
  let newVars := goals.foldl (init := (#[] : Array Nat)) fun acc g =>
    (varsOf g).foldl (init := acc) fun acc x => if goalVars.contains x || acc.contains x then acc else acc.push x
  let concl := prop.rule.concl
  let conclNonvar := (concl.nodes.filter fun n => !Node.isVar n).size
  let ruleTerms := prop.rule.terms
  let goalTerms := goal.terms
  let shared := ruleTerms.filter goalTerms.contains
  let w (ts : Array Nat) : Float := ts.foldl (init := 0) fun acc t => acc + stats.idf t
  let ruleW := w ruleTerms
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
    b concl.isVar,
    n goal.size,
    n conclNonvar / n (max 1 goal.size),
    b (isVar goal),
    n (env.propDepth p),
    n ruleTerms.size,
    n shared.size,
    if ruleW == 0 then 0 else w shared / ruleW,
    ruleW - w shared,
    Float.log (1 + n goalNode.children.size)
  ]

end Whitehead.Prove
