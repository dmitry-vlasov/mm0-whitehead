/-
Congruence: rewriting under positions, the first decision procedure of the tactics system
(`docs/DESIGN.md`, "The tactics system"). A goal `L R' R` — `R'` an equality or a
biconditional, in the inference form or under an antecedent, `ph -> L R' R` — whose sides
are applications of the same term differing in some arguments is proved by a congruence
lemma of that term, one hypothesis `x R y` for each argument that differs, and so on
below, down to the arguments whose heads differ, which are left as open goals, and the
arguments that are the same, closed by reflexivity.

The lemmas are not named: they are mined from the file by shape (`CongrTable.ofDb`). A
congruence lemma has hypotheses `[ph ->] xᵢ Rᵢ yᵢ`, binary applications of two distinct
variables, and the conclusion `[ph ->] (t … xᵢ …) R' (t … yᵢ …)`: the same term `t` on
both sides over variables, differing exactly where a hypothesis says, all its variables
distinct. In the deduction form the antecedent is one variable `ph`, first in every
hypothesis and in the conclusion, under whatever term the file uses for the implication
(`wi`, `im`). A reflexivity lemma has no hypotheses and concludes `[ph ->] x R x`. So
set.mm's `oveq1d`, `fveq2d`, `eleq1d`, `anbi12d`, `eqidd`, `biidd` and peano's `oreq1d`,
`aneqd`, `eqidd` are read, each with the positions it rewrites; the implication forms
(`oveq1`, `A = B -> …`) are not, yet.

The procedure's proof is a skeleton (`Skeleton`), replayed by `follow` (`Rails.lean`): the
engine makes the substitutions by unification and emits the proof, as the plan of
2026-10-21 decided. An open leaf is `Skeleton.hyp 0`, which the replay leaves to the rest
of the search; a premise of the theorem that fits it closes it at once.
-/
import Whitehead.Prove.Db

namespace Whitehead.Prove

/-- A congruence lemma, as the table reads it. -/
structure CongrLemma where
  /-- The assertion. -/
  id : Nat
  /-- For each argument of the term rewritten, the relation of the hypothesis that
  rewrites it, or none where both sides have the same variable. -/
  positions : Array (Option Nat)
  /-- For each hypothesis, in order, the argument it rewrites. -/
  hypPos : Array Nat
  deriving Inhabited, Repr

/-- The congruence and reflexivity lemmas of a file, by shape. -/
structure CongrTable where
  /-- By the term rewritten, the relation of the conclusion, and whether the form is the
  deduction one: the lemmas, in the order of the file. -/
  lemmas : Std.HashMap (Nat × Nat × Bool) (Array CongrLemma) := {}
  /-- By the relation and the form: the first reflexivity lemma. -/
  refl : Std.HashMap (Nat × Bool) Nat := {}
  /-- The term of the deduction form's antecedent, `ph -> …`, if the file has one. -/
  connective : Option Nat := none
  deriving Inhabited

namespace CongrTable

/-- `e` as an application: its term and its arguments. -/
def app (e : Exp) : Option (Nat × Array Exp) :=
  let n := e.nodes[0]!
  if Node.isVar n || Node.isConst n then none
  else some (Node.appId n, (e.argStarts 0).map e.sub)

/-- `e` as a binary application: its term and its two arguments. -/
def binary (e : Exp) : Option (Nat × Exp × Exp) := do
  let (t, args) ← app e
  if args.size == 2 then some (t, args[0]!, args[1]!) else none

/-- `e` as an application of a term to variables: the term and the variables. -/
def varApp (e : Exp) : Option (Nat × Array Nat) := do
  let (t, args) ← app e
  if args.all (·.isVar) then some (t, args.map fun a => Node.varId a.nodes[0]!) else none

/-- The statements of `a` in its forms: the inference form as they are; and the deduction
form, the antecedent variable and the connective stripped from every hypothesis and the
conclusion, if they all have the same (`ded`, the connective, the hypotheses, the
conclusion). -/
def forms (a : Assertion) : Array (Bool × Option Nat × Array Exp × Exp) := Id.run do
  let mut out := #[(false, none, a.hyps, a.concl)]
  if let some (c, ante, body) := binary a.concl then
    if ante.isVar then
      let v := ante.nodes[0]!
      let hyps := a.hyps.filterMap fun h => match binary h with
        | some (c', ante', body') => if c' == c && ante'.isTheVar v then some body' else none
        | none => none
      if hyps.size == a.hyps.size && !body.hasVar (Node.varId v) then out := out.push (true, some c, hyps, body)
  return out

/-- The congruence lemma that `a` is, in one of its forms: the form, its connective, the
term rewritten, the relation of the conclusion, and the lemma. -/
def congrOf (a : Assertion) : Option (Bool × Option Nat × Nat × Nat × CongrLemma) := Id.run do
  for (ded, conn, hyps, concl) in forms a do
    if hyps.isEmpty then continue
    let some (rel, l, r) := binary concl | continue
    let some (t, ls) := varApp l | continue
    let some (t', rs) := varApp r | continue
    if t != t' || ls.size != rs.size then continue
    -- each hypothesis `x R y`, two distinct variables
    let hs := hyps.filterMap fun h => do
      let (rh, x, y) ← binary h
      if x.isVar && y.isVar && x != y then some (rh, Node.varId x.nodes[0]!, Node.varId y.nodes[0]!) else none
    if hs.size != hyps.size then continue
    -- each hypothesis rewrites one argument, and each argument that differs has one
    let mut positions : Array (Option Nat) := Array.replicate ls.size none
    let mut hypPos : Array Nat := #[]
    let mut ok := true
    for (rh, x, y) in hs do
      match (Array.range ls.size).find? fun i => ls[i]! == x && rs[i]! == y && positions[i]!.isNone with
      | some i =>
        positions := positions.set! i (some rh)
        hypPos := hypPos.push i
      | none => ok := false
    for i in [0:ls.size] do
      if ls[i]! != rs[i]! && positions[i]!.isNone then ok := false
    if !ok then continue
    -- all the variables distinct: one for an argument that is the same, two for one that differs
    let vars := (ls ++ rs).foldl (init := (#[] : Array Nat)) fun acc v => if acc.contains v then acc else acc.push v
    if vars.size != ls.size + hypPos.size then continue
    return some (ded, conn, t, rel, { id := a.id, positions, hypPos })
  return none

/-- The reflexivity lemma that `a` is, in one of its forms: the form, its connective and
the relation. -/
def reflOf (a : Assertion) : Option (Bool × Option Nat × Nat) := Id.run do
  if !a.hyps.isEmpty then return none
  for (ded, conn, _, concl) in forms a do
    let some (rel, l, r) := binary concl | continue
    if l.isVar && l == r then return some (ded, conn, rel)
  return none

/-- The table of a file. -/
def ofDb (db : Db) : CongrTable := Id.run do
  let mut t : CongrTable := {}
  for a in db.asserts do
    if a.pseudo.isSome then continue
    if let some (ded, conn, term, rel, l) := congrOf a then
      if ded && t.connective.isNone then t := { t with connective := conn }
      t := { t with lemmas := t.lemmas.alter (term, rel, ded) fun ls => some ((ls.getD #[]).push l) }
    else if let some (ded, conn, rel) := reflOf a then
      if ded && t.connective.isNone then t := { t with connective := conn }
      if !t.refl.contains (rel, ded) then t := { t with refl := t.refl.insert (rel, ded) a.id }
  return t

/-- The lemma before `limit` for term `t`, relation `rel` and form `ded` that rewrites the
arguments `diffs`, and the fewest others. -/
def pick (tb : CongrTable) (limit t rel : Nat) (ded : Bool) (diffs : Array Nat) : Option CongrLemma :=
  let fits (l : CongrLemma) : Bool := l.id < limit && diffs.all fun i => (l.positions[i]?.getD none).isSome
  (tb.lemmas.getD (t, rel, ded) #[]).foldl (init := none) fun best l =>
    if !fits l then best
    else match best with
      | none => some l
      | some b => if l.hypPos.size < b.hypPos.size then some l else some b

/-- The reflexivity step for `rel` in form `ded`, from the lemmas before `limit`. -/
def reflStep (tb : CongrTable) (limit rel : Nat) (ded : Bool) : Option Skeleton :=
  tb.refl[(rel, ded)]?.bind fun k => if k < limit then some (.step k #[]) else none

/-- The skeleton that proves `l rel r` in form `ded` by congruence, down to the arguments
whose heads differ, open leaves (`.hyp 0`); none if the sides are not applications of
one term, or no lemma rewrites where they differ. -/
partial def plan (tb : CongrTable) (limit : Nat) (ded : Bool) (rel : Nat) (l r : Exp) : Option Skeleton :=
  if l == r then tb.reflStep limit rel ded
  else do
    let (t, ls) ← app l
    let (t', rs) ← app r
    if t != t' || ls.size != rs.size then none
    let diffs := (Array.range ls.size).filter fun i => ls[i]! != rs[i]!
    let lem ← tb.pick limit t rel ded diffs
    let children := lem.hypPos.map fun i =>
      let ri := (lem.positions[i]?.getD none).getD 0
      if ls[i]! == rs[i]! then (tb.reflStep limit ri ded).getD (.hyp 0)
      else (plan tb limit ded ri ls[i]! rs[i]!).getD (.hyp 0)
    some (.step lem.id children)

/-- The skeleton for goal `g` of a theorem numbered `limit`: in the inference form, or
under the connective in the deduction form. -/
def planGoal (tb : CongrTable) (limit : Nat) (g : Exp) : Option Skeleton :=
  let inference := do
    let (rel, l, r) ← binary g
    plan tb limit false rel l r
  let deduction := do
    let conn ← tb.connective
    let (c, _, body) ← binary g
    if c != conn then none
    let (rel, l, r) ← binary body
    plan tb limit true rel l r
  inference <|> deduction

end CongrTable

end Whitehead.Prove
