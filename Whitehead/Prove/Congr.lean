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
`aneqd`, `eqidd` are read, each with the positions it rewrites. A lemma stated as an
implication without hypotheses (`oveq1`: `A = B -> (A F C) = (B F C)`; peano's `addeq2`;
curried for several) is read too, and applied by the file's modus ponens (`ax-mp`,
`ax_mp`: hypotheses `x` and `x -> y`, mined by shape), one application a hypothesis.

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
  /-- Stated as an implication, its hypotheses the antecedents: applied by modus ponens. -/
  impl : Bool := false
  deriving Inhabited, Repr

/-- A form in which an assertion states something: as it is; as a deduction, every
hypothesis and the conclusion under one antecedent variable; or as a curried implication
without hypotheses, the antecedents its hypotheses. -/
structure Form where
  ded : Bool := false
  impl : Bool := false
  /-- The connective of the deduction or the implication. -/
  conn : Option Nat := none
  hyps : Array Exp
  concl : Exp
  deriving Inhabited

/-- The congruence and reflexivity lemmas of a file, by shape. -/
structure CongrTable where
  /-- By the term rewritten, the relation of the conclusion, and whether the form is the
  deduction one: the lemmas, in the order of the file. -/
  lemmas : Std.HashMap (Nat × Nat × Bool) (Array CongrLemma) := {}
  /-- By the relation and the form: the first reflexivity lemma. -/
  refl : Std.HashMap (Nat × Bool) Nat := {}
  /-- The term of the deduction form's antecedent, `ph -> …`, if the file has one. -/
  connective : Option Nat := none
  /-- Modus ponens, `x, x -> y ⊢ y`: the lemma, and whether the premise comes first. -/
  mp : Option (Nat × Bool) := none
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

/-- The statements of `a` in its forms: as they are; as a deduction, the antecedent
variable and the connective stripped from every hypothesis and the conclusion, if they
all have the same; and, without hypotheses, as a curried implication, its antecedents
the hypotheses, under the connective the deduction form of the file uses (`conn`; any
binary term if none is known). -/
def forms (a : Assertion) (conn : Option Nat := none) : Array Form := Id.run do
  let mut out := #[{ hyps := a.hyps, concl := a.concl : Form }]
  if let some (c, ante, body) := binary a.concl then
    if ante.isVar then
      let v := ante.nodes[0]!
      let hyps := a.hyps.filterMap fun h => match binary h with
        | some (c', ante', body') => if c' == c && ante'.isTheVar v then some body' else none
        | none => none
      if hyps.size == a.hyps.size && !body.hasVar (Node.varId v) then
        out := out.push { ded := true, conn := some c, hyps, concl := body }
  if a.hyps.isEmpty then
    if let some (c, h, rest) := binary a.concl then
      if conn.all (· == c) then
        let mut hyps := #[h]
        let mut body := rest
        for _ in [0:8] do
          match binary body with
          | some (c', h', rest') => if c' == c then hyps := hyps.push h'; body := rest' else break
          | none => break
        -- every prefix of the antecedents is a reading: `x -> y -> z` states `z` from
        -- `x, y`, and `y -> z` from `x`
        let mut b := body
        let mut hs := hyps
        for _ in [0:hyps.size] do
          out := out.push { impl := true, conn := some c, hyps := hs, concl := b }
          let some last := hs.back? | break
          hs := hs.pop
          b := Exp.mkApp c a.concl.ty #[last, b]
  return out

/-- The congruence lemma that `a` is, in one of its forms: the form, its connective, the
term rewritten, the relation of the conclusion, and the lemma. -/
def congrOf (a : Assertion) (conn : Option Nat := none) : Option (Bool × Option Nat × Nat × Nat × CongrLemma) := Id.run do
  for f in forms a conn do
    let (ded, conn, hyps, concl) := (f.ded, f.conn, f.hyps, f.concl)
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
    return some (ded, conn, t, rel, { id := a.id, positions, hypPos, impl := f.impl })
  return none

/-- The reflexivity lemma that `a` is, in one of its forms: the form, its connective and
the relation. -/
def reflOf (a : Assertion) : Option (Bool × Option Nat × Nat) := Id.run do
  if !a.hyps.isEmpty then return none
  for f in forms a do
    if f.impl then continue
    let some (rel, l, r) := binary f.concl | continue
    if l.isVar && l == r then return some (f.ded, f.conn, rel)
  return none

/-- Modus ponens, if `a` is it: `x, x -> y ⊢ y`, with whether the premise comes first. -/
def mpOf (a : Assertion) : Option (Nat × Bool) := do
  if a.hyps.size != 2 || !a.concl.isVar then none
  let y := a.concl
  let imp (h : Exp) (x : Exp) : Bool := match binary h with
    | some (_, x', y') => x' == x && y' == y && x != y
    | none => false
  if a.hyps[0]!.isVar && imp a.hyps[1]! a.hyps[0]! then some (a.id, true)
  else if a.hyps[1]!.isVar && imp a.hyps[0]! a.hyps[1]! then some (a.id, false)
  else none

/-- The table of a file. -/
def ofDb (db : Db) : CongrTable := Id.run do
  let mut t : CongrTable := {}
  -- the connective and modus ponens first: the implication forms are read under them
  for a in db.asserts do
    if a.pseudo.isSome then continue
    if t.mp.isNone then t := { t with mp := mpOf a }
    if t.connective.isNone then
      if let some (true, conn, _, _, _) := congrOf a then t := { t with connective := conn }
      else if let some (true, conn, _) := reflOf a then t := { t with connective := conn }
  for a in db.asserts do
    if a.pseudo.isSome then continue
    if let some (ded, _, term, rel, l) := congrOf a t.connective then
      t := { t with lemmas := t.lemmas.alter (term, rel, ded) fun ls => some ((ls.getD #[]).push l) }
    else if let some (ded, _, rel) := reflOf a then
      if !t.refl.contains (rel, ded) then t := { t with refl := t.refl.insert (rel, ded) a.id }
  return t

/-- The lemma before `limit` for term `t`, relation `rel` and form `ded` that rewrites the
arguments `diffs`, and the fewest others; one with hypotheses before one stated as an
implication, which needs modus ponens. -/
def pick (tb : CongrTable) (limit t rel : Nat) (ded : Bool) (diffs : Array Nat) : Option CongrLemma :=
  let fits (l : CongrLemma) : Bool := l.id < limit && diffs.all fun i => (l.positions[i]?.getD none).isSome &&
    (!l.impl || tb.mp.any (·.1 < limit))
  let better (l b : CongrLemma) : Bool :=
    (!l.impl && b.impl) || (l.impl == b.impl && l.hypPos.size < b.hypPos.size)
  (tb.lemmas.getD (t, rel, ded) #[]).foldl (init := none) fun best l =>
    if !fits l then best
    else match best with
      | none => some l
      | some b => if better l b then some l else some b

/-- The lemma applied to the proofs of its hypotheses: a step; for one stated as an
implication, modus ponens on each antecedent in turn. -/
def applyLemma (tb : CongrTable) (lem : CongrLemma) (children : Array Skeleton) : Skeleton :=
  if !lem.impl then .step lem.id children
  else match tb.mp with
    | none => .hyp 0
    | some (mp, premiseFirst) =>
      children.foldl (init := Skeleton.step lem.id #[]) fun acc c =>
        if premiseFirst then .step mp #[c, acc] else .step mp #[acc, c]

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
    some (tb.applyLemma lem children)

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
