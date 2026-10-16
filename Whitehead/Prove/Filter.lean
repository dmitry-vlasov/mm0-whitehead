/-
Filters over the variants of the proof variant tree (`docs/DESIGN.md`, "Phase 4",
"Filters").

A filter is a predicate over what an agent chooses among. Backward, that is the variants
of a goal node, its assertion nodes (`RuProverProp`). Forward, it is the deductions,
the facts that `Session.deduce` made. Both are seen through a `View`: the step, its
name, the number of its premises, the new goals it makes, and what it proves. An agent
narrows the variants by tightening a filter or loosening it, and then chooses among the
few that are left. A filter reads the tree and never changes it.

Ranks and mined chains are later atoms (`DESIGN.md`, "Mining and ranking").
-/
import Whitehead.Prove.Pattern
import Whitehead.Prove.Env

namespace Whitehead.Prove

/-- The kind of a step: an assertion of the file, or the unfolding or folding of a def. -/
inductive StepKind where
  | assertion
  | unfold
  | fold
  deriving BEq, Inhabited, Repr

def Step.kind : Step → StepKind
  | .assertion _ => .assertion
  | .conv _ _ true => .unfold
  | .conv _ _ false => .fold

inductive Filter where
  /-- Every variant. -/
  | all
  /-- The name of the step, by a pattern in which `*` stands for any characters: the
  assertion's name, or for an unfolding the def's. -/
  | name (glob : String)
  /-- An assertion among these, by their numbers. -/
  | scope (ids : Array Nat)
  | kind (k : StepKind)
  /-- The number of premises of the step: of new goals, backward. -/
  | premises (min max : Nat)
  /-- Backward: one of the new goals matches the pattern. -/
  | goal (pat : Exp)
  /-- Backward, the goal; forward, the fact deduced: it matches the pattern. -/
  | result (pat : Exp)
  /-- The assertion is used in at least this many proofs of the theorems before the one
  being proved (`Uses.lean`). -/
  | used (min : Nat)
  /-- Backward: one of the new goals could become what the pattern describes: as `goal`,
  but a variable of the new goal matches anything. -/
  | fits (pat : Exp)
  /-- What the step proves, the goal under its unifier, matches the pattern. -/
  | proves (pat : Exp)
  /-- The goal has no variable. -/
  | ground
  /-- Backward: one of the new goals that is not a bare variable unifies with a premise of
  the theorem, which would prove it at once. -/
  | hyp
  /-- Backward: one of the new goals is a bare variable, such as the minor premise of
  modus ponens: anything fits it. -/
  | bare
  | and (fs : Array Filter)
  | or (fs : Array Filter)
  | not (f : Filter)
  deriving Inhabited

/-- A variant, as a filter sees it. -/
structure View where
  step : Step
  name : String
  premises : Nat
  /-- The new goals: the premises of the step under its unifier. Computed when a filter
  asks for them. -/
  goals : Thunk (Array Exp)
  result : Exp
  /-- In how many proofs before the theorem the assertion is used; 0 for an unfolding. -/
  uses : Nat := 0
  /-- How many of the new goals that are not bare variables unify with a premise of the
  theorem. -/
  closable : Thunk Nat := Thunk.pure 0
  /-- What the step proves: the goal under its unifier. -/
  inst : Thunk Exp := Thunk.pure default

/-- Does `name` match `glob`, in which `*` stands for any characters? -/
partial def globMatch (glob name : String) : Bool :=
  go glob.toList name.toList
where
  go : List Char → List Char → Bool
    | [], [] => true
    | '*' :: g, n => go g n || (match n with | [] => false | _ :: n' => go ('*' :: g) n')
    | c :: g, d :: n => c == d && go g n
    | _, _ => false

namespace Filter

partial def eval (f : Filter) (v : View) : Bool :=
  match f with
  | .all => true
  | .name g => globMatch g v.name
  | .scope ids =>
    match v.step with
    | .assertion id => ids.contains id
    | _ => false
  | .kind k => v.step.kind == k
  | .premises lo hi => lo ≤ v.premises && v.premises ≤ hi
  | .goal p => v.goals.get.any (·.matchesPattern p)
  | .result p => v.result.matchesPattern p
  | .used n => v.uses ≥ n
  | .fits p => v.goals.get.any (·.fitsPattern p)
  | .proves p => v.inst.get.matchesPattern p
  | .ground => !v.result.hasVars
  | .hyp => v.closable.get > 0
  | .bare => v.goals.get.any (·.isVar)
  | .and fs => fs.all (·.eval v)
  | .or fs => fs.any (·.eval v)
  | .not f => !f.eval v

end Filter

/-- In how many proofs before the theorem being proved the step's assertion is used. -/
def Env.stepUses (env : Env) : Step → Nat
  | .assertion id => env.uses.before id env.task.limit
  | .conv .. => 0

/-- The name of a step: the assertion's, or the def's for an unfolding. -/
def Env.stepName (env : Env) : Step → String
  | .assertion id => env.db.asserts[id]!.name
  | .conv t _ _ => env.db.terms[t]!.name

/-- The goal of assertion node `p` as the node would prove it: under its unifier, which
shows what it puts for the goal's variables. -/
def Env.propInstance (env : Env) (p : Nat) : Exp :=
  let prop := env.props[p]!
  let goal := env.hyps[prop.parent]!.expr
  if prop.expanded then prop.sub.apply goal
  else
    match prop.unif.bind (·.toSubst) with
    | some u => u.apply goal
    | none => goal

/-- The view of assertion node `p`. Its new goals are its children's expressions once it
is expanded; before, the premises of its rule under the unifier of the candidate, with
the variables of the rule that the unifier leaves free as they are. -/
def Env.propView (env : Env) (p : Nat) : View :=
  let prop := env.props[p]!
  let goals : Thunk (Array Exp) := Thunk.mk fun _ =>
    if prop.expanded then prop.children.map fun h => env.hyps[h]!.expr
    else
      match prop.unif.bind (·.toSubst) with
      | some u => prop.rule.hyps.map u.apply
      | none => prop.rule.hyps.map prop.outer.apply |>.map prop.sub.apply
  let closable := Thunk.mk fun _ => (goals.get.filter fun g => !g.isVar && !(env.premises.unify g).isEmpty).size
  { step := prop.step, name := env.stepName prop.step, premises := prop.rule.hyps.size, goals,
    result := env.hyps[prop.parent]!.expr, uses := env.stepUses prop.step, closable,
    inst := Thunk.mk fun _ => env.propInstance p }

/-- The view of fact `f` as the deduction that made it: the assertion node under it. A
premise of the task is not a deduction. -/
def Env.factView? (env : Env) (f : Nat) : Option View := do
  let hyp ← env.hyps[f]?
  let p ← hyp.children[0]?
  let prop ← env.props[p]?
  return { step := prop.step, name := env.stepName prop.step, premises := prop.rule.hyps.size,
           goals := Thunk.pure #[], result := hyp.expr, uses := env.stepUses prop.step,
           inst := Thunk.pure hyp.expr }

end Whitehead.Prove
