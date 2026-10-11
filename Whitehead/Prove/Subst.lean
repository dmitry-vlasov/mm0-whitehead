/-
Substitutions: a port of `russell-flow/src/ru/subst.flow`. The name of the Flow9
function is given at each definition.

A substitution maps variables to expressions. With each image the set of its variables
is kept (`RuSubExpr`), so that the functions that extend a substitution can tell which
images a new binding touches without reading them.

What differs from Russell:

- No coercion nodes. Where Russell wraps an expression into the rule that lifts it to
  the type of the variable (`ruAdd2Subst1`, `ruMatchExp`), here the types must fit
  (`Ty.fits`) and the expression is taken as it is.
- `ruMakeFresherSubst` records, as the variables of the image `v'` of `v`, the set `{v}`.
  Here it is `{v'}`, the variables of the image, as for every other entry. The entries
  made by it only ever end up in `RuProverProp.outer`, where the difference shows in
  `ruMakeProofTree` alone: the statement of a step is instantiated at once, where in
  Russell it is left with the fresh variable until the parent applies its substitution
  to the whole subtree.
-/
import Std.Data.HashMap
import Std.Data.HashSet
import Whitehead.Prove.Exp

namespace Whitehead.Prove

/-- `ruExpVarIdsHashSet`: the numbers of the variables of `e`. -/
def Exp.varIds (e : Exp) : Std.HashSet Nat :=
  e.nodes.foldl (init := {}) fun acc n => if Node.isVar n then acc.insert (Node.varId n) else acc

/-- The numbers of the variables of `e`, each once. An array: an image has few
variables, and a hash set for each of the millions of bindings that the index makes
was a large part of the time spent allocating and freeing. -/
def Exp.varIdArray (e : Exp) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for n in e.nodes do
    if Node.isVar n then
      let id := Node.varId n
      if !out.contains id then out := out.push id
  return out

/-- `RuSubExpr`: the image of the variable `var` (a variable node), with the numbers of
the variables that occur in it. -/
structure SubExp where
  var : Nat
  exp : Exp
  vars : Array Nat
  deriving Inhabited

/-- `RuSubst`, keyed by the number of the variable. -/
structure Subst where
  map : Std.HashMap Nat SubExp := {}
  deriving Inhabited

namespace SubExp

def mk' (v : Nat) (e : Exp) : SubExp := ⟨v, e, e.varIdArray⟩

end SubExp

namespace Subst

/-- `ruLookupSubst` -/
@[inline] def lookup (s : Subst) (v : Nat) : Option Exp :=
  s.map[Node.varId v]? |>.map (·.exp)

/-- `ruLookupSubstDef`: the image of `v`, which is `v` itself if it is not bound. -/
def lookupD (s : Subst) (v : Nat) : Exp :=
  match s.map[Node.varId v]? with
  | some x => x.exp
  | none => Exp.ofVar v

/-- `ruSubstSize` -/
@[inline] def size (s : Subst) : Nat := s.map.size

/-- `ruSubstMapsVar` -/
@[inline] def maps (s : Subst) (id : Nat) : Bool := s.map.contains id

/-- `ruSubstVars`: the variable nodes that `s` binds. -/
def vars (s : Subst) : Array Nat :=
  s.map.fold (init := #[]) fun acc _ x => acc.push x.var

/-- `ruSubstAffectsExp` -/
def affects (s : Subst) (e : Exp) : Bool :=
  e.nodes.any fun n => Node.isVar n && s.map.contains (Node.varId n)

/-- `ruDoApplySubst`. The lengths of the applications are set again as their arguments
grow: an application that is open is remembered with the index of its last node in `e`,
and closed when that node has been copied. (Russell goes from the right and counts
arguments by the arity.) -/
def applyRaw (s : Subst) (e : Exp) : Exp := Id.run do
  let mut out : Array Nat := Array.mkEmpty e.nodes.size
  let mut openAt : Array Nat := #[]
  let mut openEnd : Array Nat := #[]
  for i in [0:e.nodes.size] do
    let n := e.nodes[i]!
    if Node.isVar n then
      match s.map[Node.varId n]? with
      | some x => out := out ++ x.exp.nodes
      | none => out := out.push n
    else if Node.len n == 0 then
      out := out.push n
    else
      openAt := openAt.push out.size
      openEnd := openEnd.push (i + Node.len n)
      out := out.push n
    while openEnd.size > 0 && openEnd.back! == i do
      let at_ := openAt.back!
      let node := out[at_]!
      out := out.set! at_ (Node.setLen node (out.size - at_ - 1))
      openAt := openAt.pop
      openEnd := openEnd.pop
  return ⟨out⟩

/-- `ruApplySubst` -/
def apply (s : Subst) (e : Exp) : Exp :=
  if s.affects e then s.applyRaw e else e

/-- `ruApplySubstVars` -/
def applyVars (s : Subst) (e : SubExp) : SubExp :=
  if e.vars.any fun v => s.map.contains v then SubExp.mk' e.var (s.applyRaw e.exp) else e

/-- The substitution of the one variable `v`. -/
def single (v : Nat) (e : Exp) : Subst :=
  { map := ({} : Std.HashMap Nat SubExp).insert (Node.varId v) (SubExp.mk' v e) }

/-- `ruAdd2SubstVars`: `s` extended by `v ↦ e0`, if that is consistent. The new image
is brought under `s` first; then `v` is replaced in the images that `s` already has, so
that no image contains a bound variable.

The test in the middle is Russell's, kept as it is: a variable `w` of the new image that
`s` binds to an image containing `w` itself is allowed only if the two bindings are
`w ↦ v` and `v ↦ w`, which cancel. With the images' variable sets as they are here
(see the head of this file) no such `w` exists. -/
def addVars (s : Subst) (v : Nat) (e0 : SubExp) : Option Subst :=
  let e := s.applyVars e0
  if e.exp.isTheVar v then some s
  else
    let vid := Node.varId v
    if e.vars.contains vid then none
    else
      match s.map[vid]? with
      | some e1 => if e.exp == e1.exp then some s else none
      | none =>
        let p : Bool × Option Nat := e.vars.foldl (init := (true, none)) fun acc ev =>
          if !acc.1 then acc
          else
            match s.map[ev]? with
            | some e2 =>
              if !e2.vars.contains ev then acc
              else (e2.exp.isTheVar v && e.exp.isVar && Node.varId e.exp.nodes[0]! == ev, some ev)
            | none => acc
        if !p.1 then none
        else
          match p.2 with
          | some w => some { map := s.map.erase w }
          | none =>
            let one := single v e.exp
            let map := s.map.fold (init := s.map) fun m w x =>
              if x.vars.contains vid then m.insert w (SubExp.mk' x.var (one.applyRaw x.exp)) else m
            some { map := map.insert vid { e with var := v } }

/-- `ruAdd2Subst` -/
def add (s : Subst) (v : Nat) (e : Exp) : Option Subst :=
  s.addVars v (SubExp.mk' v e)

/-- `ruAdd2Subst1`: as `add`, if the type of `e` fits the variable. -/
def add1 (s : Subst) (v : Nat) (e : Exp) : Option Subst :=
  if Ty.fits (Node.ty v) e.ty then s.add v e else none

/-- `ruSemiCompose`: the bindings of `s1`, each followed by `s2`. -/
def semiCompose (s1 s2 : Subst) : Option Subst :=
  s1.map.fold (init := some {}) fun acc _ e1 =>
    acc.bind fun s => s.addVars e1.var (s2.applyVars e1)

/-- `ruUnsafeCompose`: as `compose`, without the checks: every image of `s1` followed by
`s2`, and the bindings of `s2` for the variables that `s1` does not bind. -/
def unsafeCompose (s1 s2 : Subst) : Subst :=
  let m : Std.HashMap Nat SubExp := s1.map.fold (init := {}) fun m v e => m.insert v (s2.applyVars e)
  { map := s2.map.fold (init := m) fun m v e => if m.contains v then m else m.insert v e }

/-- `ruComposeSlow`: binding by binding, each added with `addVars`, which scans the
substitution; it decides the cases that the fast path of `compose` leaves to it. -/
def composeSlow (s1 s2 : Subst) : Option Subst :=
  s2.map.fold (init := semiCompose s1 s2) fun acc v2 e2 =>
    acc.bind fun s => if s1.map.contains v2 then some s else s.addVars e2.var e2

/-- `ruCompose`: first `s1`, then `s2`; `none` if a binding contradicts another.

As in Russell since `7657286c`: the images of `s1` with `s2` applied, and the bindings
of `s2` for the variables that `s1` does not bind, in one pass; identity bindings are
dropped. The result is taken if it is idempotent — no image has a variable that it binds
— which it is for idempotent inputs; otherwise `composeSlow` decides (chains, cycles,
renamings that cancel). -/
def compose (s1 s2 : Subst) : Option Subst :=
  let u := unsafeCompose s1 s2
  let m := u.map.fold (init := u.map) fun m v x => if x.exp.isTheVar x.var then m.erase v else m
  if m.fold (init := true) fun ok _ x => ok && !x.vars.any m.contains then some { map := m }
  else composeSlow s1 s2

/-- `ruMergeSubst`: the union of two substitutions, if they agree where both bind. -/
def merge (s1 s2 : Subst) : Option Subst :=
  s2.map.fold (init := some s1) fun acc v e2 =>
    acc.bind fun s =>
      match s.map[v]? with
      | some e1 => if e1.exp == e2.exp then some s else none
      | none => some { map := s.map.insert v e2 }

/-- `ruMergeSubsUnsafe`: the union, the bindings of `s2` winning. -/
def mergeUnsafe (s1 s2 : Subst) : Subst :=
  { map := s2.map.fold (init := s1.map) fun m v e => m.insert v e }

/-- `ruFilterSub` -/
def filter (s : Subst) (pred : Nat → Exp → Bool) : Subst :=
  { map := s.map.fold (init := {}) fun m v x => if pred x.var x.exp then m.insert v x else m }

/-- `ruMakeFresherSubst`: each of `vars` to the variable that `fresher` makes for it. -/
def fresher (vars : Array Nat) (fresh : Nat → Nat) : Subst :=
  { map := vars.foldl (init := {}) fun m v => m.insert (Node.varId v) (SubExp.mk' v (Exp.ofVar (fresh v))) }

/-- `ruSubComplexity` -/
def complexity (s : Subst) : Nat :=
  s.map.fold (init := 0) fun acc _ x => acc + x.exp.size

/-- The bindings as text, sorted by variable, for tests and traces. -/
def toSexp (s : Subst) (term : Nat → String) (var : Nat → String) : String :=
  let items := s.map.fold (init := #[]) fun acc v x => acc.push (var v ++ " := " ++ x.exp.toSexp term var)
  ", ".intercalate (items.qsort (· < ·)).toList

end Subst

/-- `ruMatchExp`: the substitution of the variables of `pattern` that makes it `e`, if
there is one. One-sided: the variables of `e` are not bound. -/
def matchExp (e pattern : Exp) : Option Subst := Id.run do
  let mut sub : Subst := {}
  let mut p := 0
  for n1 in pattern.nodes do
    if p ≥ e.nodes.size then return none
    let n2 := e.nodes[p]!
    if Node.isVar n1 then
      if !Ty.fits (Node.ty n1) (Node.ty n2) then return none
      let image := e.sub p
      match sub.map[Node.varId n1]? with
      | some old => if old.exp != image then return none
      | none => sub := { map := sub.map.insert (Node.varId n1) (SubExp.mk' n1 image) }
      p := p + image.size
    else
      if Node.isVar n2 || Node.appId n1 != Node.appId n2 then return none
      p := p + 1
  return some sub

/-- `RuSplitSubs` -/
structure SplitSubs where
  indep : Subst
  depend : Array Subst

/-- `ruSplitSubs` (with `ruSplitSubIndep1`): the bindings of variables that occur in one
of the substitutions only are set apart; they need not take part in the unification of
the substitutions. -/
def splitSubs (subs : Array Subst) : SplitSubs := Id.run do
  -- for every variable, in which substitutions it occurs: as bound, or in an image
  let mut where_ : Std.HashMap Nat (Array Nat) := {}
  for i in [0:subs.size] do
    for (v, e) in subs[i]!.map do
      let mut ids := #[v]
      for w in e.vars do ids := ids.push w
      for w in ids do
        let seen := where_.getD w #[]
        if !seen.contains i then where_ := where_.insert w (seen.push i)
  let mut indep : Subst := {}
  for sub in subs do
    for (v, e) in sub.map do
      if (where_.getD v #[]).size == 1 then indep := { map := indep.map.insert v e }
  let depend := subs.map fun sub => sub.filter fun v _ => !indep.map.contains (Node.varId v)
  return ⟨indep, depend⟩

end Whitehead.Prove
