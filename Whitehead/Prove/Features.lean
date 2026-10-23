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

/-- How rare each term is in a file: in how many statements of assertions it occurs; what
the features read of each assertion of the file, by its number; and, for the value of
goals, how many assertions conclude with an application of each term. -/
structure SymbolStats where
  df : Array Nat := #[]
  statements : Nat := 0
  rules : Array RuleInfo := #[]
  heads : Array Nat := #[]
  deriving Inhabited

/-- The terms of a rule's statement: of its conclusion and its hypotheses (`Exp.terms`,
`Exp.lean`). -/
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
  let mut heads := Array.replicate db.terms.size 0
  let mut n := 0
  for a in db.asserts do
    if a.pseudo.isSome then continue
    n := n + 1
    for t in a.terms do
      if t < df.size then df := df.modify t (· + 1)
    if let some h := a.concl.nodes[0]? then
      if !Node.isVar h && !Node.isConst h && Node.appId h < heads.size then
        heads := heads.modify (Node.appId h) (· + 1)
  let s : SymbolStats := { df, statements := n, heads }
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
  /-- The goal as a vector, for the contexts of use (`Contexts.lean`), when there are any. -/
  vec : Std.HashMap Nat Float := {}
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
           size := goal.size, hasVar := goal.nodes.any Node.isVar, depth, variants := goalNode.children.size,
           vec := match env.contexts with
             | some c => Contexts.lookup (c.vectorOf goal)
             | none => {} }

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
  "siblings_log",   -- log(1 + the variants of the goal)
  -- the metavariables, where the rank is weakest (2026-10-21): a step whose new goals
  -- share variables is constrained by them; one whose new variables each stand alone is not
  "meta_goals",     -- new goals with a variable
  "shared_vars",    -- variables in two or more of the new goals
  "goal_vars",      -- the distinct variables of the goal
  "closable_meta",  -- new goals, not bare, with a variable, that a premise unifies with
  "max_goal_vars",  -- the most distinct variables in one new goal
  -- the theorem's prior (`Prior.lean`): the earlier theorems like this one, by their
  -- statements, and what their proofs use
  "prior_knn",      -- the sum of the similarities of the near theorems whose proofs use the assertion
  "prior_hit",      -- 1 if one does
  -- the contexts of use (`Contexts.lean`, 2026-10-23): the goals of earlier proofs where
  -- the assertion was used, and a sample of those it unified with where it was not
  "ctx_pos",        -- the goal's best similarity to the goals where the assertion was used
  "ctx_neg",        -- its best similarity to the goals where it unified and was not used
  "ctx_rival"       -- (ctx_pos − ctx_neg) / (ctx_pos + ctx_neg), 0 with neither
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
(`Env.goalInfo`). With `cheap`, the features that need the variant's new goals
instantiated (`goals_*`, `new_vars`, `meta_goals`, `shared_vars`, `closable_meta`,
`max_goal_vars`) and the contexts of use (`ctx_*`) are 0, as a model trained with them
zeroed expects (`train.py --zero`): the first stage of a two-stage rank (`docs/DESIGN.md`,
"Where the time goes"). -/
def Env.variantFeatures (env : Env) (stats : SymbolStats) (gi : GoalInfo) (p : Nat) (cheap : Bool := false) :
    Array Float := Id.run do
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
  let prior := match prop.step with
    | .assertion a => env.prior.getD a 0
    | _ => 0
  -- the contexts of use: the full features only (a search of the contexts a variant)
  let (ctxPos, ctxNeg) := match env.contexts, prop.step with
    | some c, .assertion a => if cheap then (0, 0) else c.best a thm gi.vec
    | _, _ => ((0 : Float), (0 : Float))
  -- the new goals: not instantiated for the cheap features, which are 0 where they would read them
  let goals := if cheap then #[] else v.goals.get
  let isVar (e : Exp) : Bool := e.nodes.any Node.isVar
  let newVars := goals.foldl (init := (#[] : Array Nat)) fun acc g =>
    g.nodes.foldl (init := acc) fun acc n =>
      if !Node.isVar n then acc
      else
        let x := Node.varId n
        if gi.vars.contains x || acc.contains x then acc else acc.push x
  -- the variables of each new goal, distinct
  let goalVars : Array (Array Nat) := goals.map fun g =>
    g.nodes.foldl (init := (#[] : Array Nat)) fun acc n =>
      if Node.isVar n && !acc.contains (Node.varId n) then acc.push (Node.varId n) else acc
  let allVars := goalVars.foldl (init := (#[] : Array Nat)) fun acc vs => vs.foldl (init := acc) fun acc v => if acc.contains v then acc else acc.push v
  let sharedVars := (allVars.filter fun v => (goalVars.filter (·.contains v)).size ≥ 2).size
  -- the goals, not bare, that a premise unifies with: asked of the index once a goal, for
  -- `closable` (all of them, as `VariantView.closable` counts) and `closable_meta` (those
  -- with variables)
  let closable := (Array.range goals.size).filter fun i =>
    let g := goals[i]!
    !g.isVar && !(env.premises.unify g).isEmpty
  let closableMeta := closable.filter fun i => !goalVars[i]!.isEmpty
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
    n prop.rule.hyps.size,
    n (goals.filter (·.isVar)).size,
    n (goals.filter (!isVar ·)).size,
    n closable.size,
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
    Float.log (1 + n gi.variants),
    n (goalVars.filter (!·.isEmpty)).size,
    n sharedVars,
    n gi.vars.size,
    n closableMeta.size,
    n (goalVars.foldl (init := 0) fun m vs => max m vs.size),
    prior,
    b (prior > 0),
    ctxPos,
    ctxNeg,
    Contexts.rival ctxPos ctxNeg
  ]

/-- The features of variant `p`, in the order of `featureNames`. -/
def Env.features (env : Env) (stats : SymbolStats) (p : Nat) : Array Float :=
  env.variantFeatures stats (env.goalInfo env.props[p]!.parent) p

/-! ### The value of goals

How likely a goal is to be proved by the search (`docs/DESIGN.md`, "The learned ranking
layer", step 4). Its features read the goal's expression alone, and the theorem: so they
are the same for a new goal of a variant not yet expanded, whose variables are still the
rule's, and for the goal node that its expansion makes, with fresh ones. -/

/-- What the goal features read of the theorem: the terms of its statement (the goal and
the premises) and their weight, the size of its goal, and its number of premises. Found
once for a theorem. -/
structure TaskInfo where
  terms : Std.HashSet Nat := {}
  weight : Float := 0
  size : Nat := 0
  premises : Nat := 0
  /-- Of the theorem's prior (`Env.prior`), the share on the assertions whose conclusions
  have each term, and the share on those whose conclusions have each term as the head: do
  the lemmas the theorems like this one use conclude about what a goal is made of. -/
  priorTerms : Std.HashMap Nat Float := {}
  priorHeads : Std.HashMap Nat Float := {}
  deriving Inhabited

def Env.taskInfo (env : Env) (stats : SymbolStats) : TaskInfo := Id.run do
  let terms := (env.task.premises.push env.task.goal).foldl (init := ({} : Std.HashSet Nat)) fun acc e =>
    e.terms.foldl (·.insert ·) acc
  let mut total : Float := 0
  let mut priorTerms : Std.HashMap Nat Float := {}
  let mut priorHeads : Std.HashMap Nat Float := {}
  for (a, v) in env.prior do
    let some r := env.db.asserts[a]? | continue
    total := total + v
    for t in r.concl.terms do
      priorTerms := priorTerms.alter t fun x => some (x.getD 0 + v)
    let h := r.concl.nodes[0]!
    if !Node.isVar h && !Node.isConst h then
      priorHeads := priorHeads.alter (Node.appId h) fun x => some (x.getD 0 + v)
  if total > 0 then
    priorTerms := priorTerms.map fun _ x => x / total
    priorHeads := priorHeads.map fun _ x => x / total
  return { terms, weight := terms.fold (init := 0) fun acc t => acc + stats.idf t, size := env.task.goal.size,
           premises := env.task.premises.size, priorTerms, priorHeads }

/-- The names of the goal features, in the order of `Env.goalFeatures`. -/
def goalFeatureNames : Array String := #[
  "size",           -- the nodes of the goal
  "height",         -- the nesting of its applications: 1 for a variable or a constant
  "metas",          -- its distinct variables (metavariables)
  "meta_share",     -- the share of its nodes that are variables
  "bare",           -- 1 if it is a bare variable
  "consts",         -- the distinct variables of the theorem in it
  "terms",          -- its distinct terms
  "idf_sum",        -- their weight
  "idf_max",        -- the weight of the rarest
  "head_idf",       -- the weight of its head term, 0 for a variable or a constant
  "head_rules_log", -- log(1 + the assertions that conclude with its head term)
  "closable",       -- 1 if it has no variable and a premise of the theorem unifies with it
  "closable_meta",  -- 1 if it has variables, is not bare, and a premise unifies with it
  "shared_idf",     -- the share of its weight in terms of the theorem's statement
  "extra_idf",      -- the weight of its terms that the theorem's statement lacks
  "size_ratio",     -- size / the size of the theorem's goal
  "depth",          -- the assertion nodes from the root to it
  "task_premises",  -- the premises of the theorem
  "task_size",      -- the nodes of the theorem's goal
  -- the step's other goals (2026-10-21): a goal with metavariables is proved only as its
  -- siblings allow, by binding them
  "siblings",       -- the step's other goals
  "siblings_ground",-- of them, without a variable
  "shared_sibling_vars", -- the goal's variables that a sibling has too
  "sibling_closable",    -- siblings, not bare, that a premise of the theorem unifies with
  -- the theorem's prior (2026-10-22): do the lemmas that the proofs of the theorems like
  -- this one use conclude about what the goal is made of (`TaskInfo.priorTerms`)
  "prior_head",     -- the share of the prior on assertions concluding with the goal's head term
  "prior_terms",    -- the mean, by weight, over the goal's terms of the share on assertions concluding with the term
  "prior_min"       -- the least of those shares: the goal's term the lemmas least conclude about
]

/-- The features of goal `e`, at `depth` assertion nodes from the root, among the step's
other goals `siblings`, in the order of `goalFeatureNames`. -/
def Env.goalFeatures (env : Env) (stats : SymbolStats) (ti : TaskInfo) (e : Exp) (depth : Nat)
    (siblings : Array Exp := #[]) : Array Float := Id.run do
  -- the nesting: the ends of the applications the walk is inside
  let mut ends : Array Nat := #[]
  let mut height := 0
  let mut varNodes := 0
  let mut vars : Std.HashSet Nat := {}
  let mut consts : Std.HashSet Nat := {}
  for i in [0:e.nodes.size] do
    let n := e.nodes[i]!
    while ends.back?.any (· ≤ i) do ends := ends.pop
    height := max height (ends.size + 1)
    if Node.isVar n then
      varNodes := varNodes + 1
      vars := vars.insert (Node.varId n)
    else if Node.isConst n then consts := consts.insert (Node.appId n)
    else if Node.len n > 0 then ends := ends.push (i + Node.len n + 1)
  let terms := e.terms
  let w := terms.foldl (init := 0) fun acc t => acc + stats.idf t
  let shared := terms.foldl (init := 0) fun acc t => if ti.terms.contains t then acc + stats.idf t else acc
  let head := e.nodes[0]!
  let headTerm := !Node.isVar head && !Node.isConst head
  let sharedSibling := (vars.toArray.filter fun v => siblings.any (·.hasVar v)).size
  let shareOf (t : Nat) : Float := ti.priorTerms.getD t 0
  let priorTerms := if w == 0 then 0 else (terms.foldl (init := 0) fun acc t => acc + stats.idf t * shareOf t) / w
  let priorMin := if terms.isEmpty then 0 else terms.foldl (init := (1 : Float)) fun acc t => min acc (shareOf t)
  let b (x : Bool) : Float := if x then 1 else 0
  let n (x : Nat) : Float := x.toFloat
  return Array.map round4 #[
    n e.size,
    n height,
    n vars.size,
    n varNodes / n (max 1 e.size),
    b e.isVar,
    n consts.size,
    n terms.size,
    w,
    terms.foldl (init := 0) fun m t => max m (stats.idf t),
    if headTerm then stats.idf (Node.appId head) else 0,
    Float.log (1 + n (if headTerm then stats.heads[Node.appId head]?.getD 0 else 0)),
    b (vars.isEmpty && !(env.premises.unify e).isEmpty),
    b (!vars.isEmpty && !e.isVar && !(env.premises.unify e).isEmpty),
    if w == 0 then 0 else shared / w,
    w - shared,
    n e.size / n (max 1 ti.size),
    n depth,
    n ti.premises,
    n ti.size,
    n siblings.size,
    n (siblings.filter (!·.hasVars)).size,
    n sharedSibling,
    n (siblings.filter fun s => !s.isVar && !(env.premises.unify s).isEmpty).size,
    if headTerm then ti.priorHeads.getD (Node.appId head) 0 else 0,
    priorTerms,
    priorMin
  ]

/-- The assertion nodes from the root to goal node `h`. -/
def Env.goalDepth (env : Env) (h : Nat) : Nat := Id.run do
  let mut depth := 0
  let mut g := h
  for _ in [0:env.hyps.size] do
    match env.hyps[g]!.parent with
    | some q =>
      depth := depth + 1
      g := env.props[q]!.parent
    | none => break
  return depth

end Whitehead.Prove
