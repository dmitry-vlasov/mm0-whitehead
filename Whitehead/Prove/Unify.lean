/-
Unification: a port of `russell-flow/src/ru/unify/exps.flow`.

`unifyExps` finds the most general substitution, extending a given one, under which any
number of expressions become the same. `unifySubs` does the same for substitutions: the
most general `δ` with `δ ∘ θ_i` equal for all `i` — the operation `mgu(Ξ)` of the paper
(section 3.2), by which the proofs of the premises of an assertion are joined.

The expressions are walked in step, each with its own position. Where all have an
application of the same term, every position moves to the first argument. Where some
have a variable, the subexpressions that the others have there are unified among
themselves, the variables are bound to the result, and every position moves past its
subexpression.

What differs from Russell: no coercion nodes (see `Subst.lean`); and the walk stops with
`none` instead of crashing if one expression ends before the others, which cannot happen
when the expressions are well typed.
-/
import Whitehead.Prove.Subst

namespace Whitehead.Prove

/-- `RuUnifyStepAcc`: what the expressions have at their current positions. -/
structure UnifyStep where
  /-- How far each position moves if the subexpression there is skipped. -/
  shift : Array Nat := #[]
  /-- The variables found: unbound ones, and those that bound variables stand for. -/
  vars : Array Nat := #[]
  /-- The subexpressions that start with an application, and the images of bound
  variables that do. -/
  exprs : Array Exp := #[]
  /-- The term of those applications, if there is any. -/
  rule : Option Nat := none
  /-- Two applications of different terms were found. -/
  ok : Bool := true
  /-- Every expression has an application here, none a variable. -/
  allRules : Bool := true

/-- `ruDoUnifyStep` -/
def unifyStep (es : Array Exp) (inds : Array Nat) (sub : Subst) : UnifyStep := Id.run do
  let mut st : UnifyStep := {}
  for i in [0:es.size] do
    let e := es[i]!
    let n := e.nodes[inds[i]!]!
    if Node.isVar n then
      st := { st with shift := st.shift.push 1, allRules := false }
      match sub.map[Node.varId n]? with
      | none => st := { st with vars := st.vars.push n }
      | some x =>
        let m := x.exp.nodes[0]!
        if Node.isVar m then
          st := { st with vars := st.vars.push m }
        else
          if st.rule.isSome && st.rule != some (Node.appId m) then return { st with ok := false }
          st := { st with exprs := st.exprs.push x.exp, rule := some (Node.appId m) }
    else
      if st.rule.isSome && st.rule != some (Node.appId n) then return { st with ok := false }
      st := { st with shift := st.shift.push (Node.len n + 1), exprs := st.exprs.push (e.sub inds[i]!),
                      rule := some (Node.appId n) }
  return st

/-- `ruUnifyStepVar`: the variable that the others are bound to, when all the
expressions have a variable: one of the most special type, so that it fits them all. -/
def unifyStepVar (vars : Array Nat) : Option Nat := Id.run do
  let mut t := vars[0]!
  for i in [1:vars.size] do
    let v := vars[i]!
    if Ty.fits (Node.ty t) (Node.ty v) then t := v
    else if Ty.fits (Node.ty v) (Node.ty t) then pure ()
    else return none
  return some t

mutual

/-- `ruUnifyExps`: the most general extension of `sub` that makes all of `es` equal. -/
partial def unifyExps (es : Array Exp) (sub : Subst) : Option Subst :=
  if es.size ≤ 1 then some sub
  else unifyLoop es (Array.replicate es.size 0) sub

/-- `ruDoUnifyExps` -/
partial def unifyLoop (es : Array Exp) (inds : Array Nat) (sub : Subst) : Option Subst :=
  let ended := (Array.range es.size).filter fun i => inds[i]! ≥ es[i]!.size
  if ended.size == es.size then some sub
  else if ended.size != 0 then none
  else
    let step := unifyStep es inds sub
    if !step.ok then none
    else
      let skip := fun (_ : Unit) => (Array.range es.size).map fun i => inds[i]! + step.shift[i]!
      match step.rule with
      | some _ =>
        if step.allRules then unifyLoop es (inds.map (· + 1)) sub
        else
          match unifyExps step.exprs sub with
          | none => none
          | some s =>
            let ex := s.apply step.exprs[0]!
            match step.vars.foldlM (init := s) fun s1 v => s1.add1 v ex with
            | none => none
            | some s1 => unifyLoop es (skip ()) s1
      | none =>
        match unifyStepVar step.vars with
        | none => none
        | some w =>
          let ex := Exp.ofVar w
          match step.vars.foldlM (init := sub) fun s1 v => s1.add1 v ex with
          | none => none
          | some s1 => unifyLoop es (skip ()) s1

end

/-- `ruDoUnifySubs`: for every variable that some substitution binds, its images are
unified, and the variable is bound to the result. -/
def unifySubsRaw (subs : Array Subst) : Option Subst := Id.run do
  -- the variables, each once, in the order of their numbers
  let mut vars : Array Nat := #[]
  for s in subs do
    for v in s.vars do
      if !vars.contains v then vars := vars.push v
  vars := vars.qsort (Node.varId · < Node.varId ·)
  let mut sub : Subst := {}
  for v in vars do
    let exprs := subs.filterMap fun s => (s.lookup v).map sub.apply
    let some sub1 := unifyExps exprs sub | return none
    let e1 := sub1.apply exprs[0]!
    match sub.lookup v with
    | none =>
      let some s := sub1.add1 v e1 | return none
      sub := s
    | some e2 =>
      let some unif := unifyExps #[e1, e2] sub1 | return none
      let some s := sub1.compose unif | return none
      sub := s
  return some sub

/-- `ruUnifySubs` -/
def unifySubs (subs : Array Subst) : Option Subst :=
  let split := splitSubs subs
  (unifySubsRaw split.depend).map fun sub => split.indep.mergeUnsafe sub

end Whitehead.Prove
