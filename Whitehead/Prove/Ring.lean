/-
`ring`: identities of a commutative ring, the second decision procedure of the tactics
system (`docs/DESIGN.md`, "The tactics system", "`ring`"). A goal `[ph ->] L = R` over an
addition, a multiplication, their units, a negation and a subtraction is proved by
normalizing both sides to one canonical term and chaining the rewrite steps by
transitivity; each step is a congruence down to a position (`Congr.lean`) ending in one
of the file's own lemmas, and a lemma's closure hypotheses (`ph -> x ∈ ℂ`) are closed by
the file's closure lemmas down to the atoms, which are left to the search.

Nothing is named: the signature and the lemmas are mined from the file by shape
(`RingTable.ofDb`), as the congruence table is. An operation is a term with some fixed
arguments (set.mm's `co x y caddc`, the symbol an argument; peano's `add x y`); a rule is
an equation `[ph ->] L = R` over distinct variables whose hypotheses are closure facts
`[ph ->] x ∈ S` of those variables, or none (peano: `nat` is a sort). A ring is an
addition and a multiplication with a distributivity between them; the shapes read for
each are commutativity, associativity, left commutativity, the units, for the
multiplication the absorbing zero, and for a negation the inverse, the double negation,
the definition of subtraction, the negation of a sum and of a product, and `⊝0 = 0`;
besides, the transitivity and symmetry of the equality, the lift of a plain statement
under an antecedent (`a1i`), and the closure of the operations and of the constants.

The normal form is a sum, nested to the right, of monomials in a fixed order, each a
product, nested to the right, of atoms in a fixed order, negated at most as a whole; like
monomials are not collected (`x + x` stays), and numerals other than the units are atoms:
the first version. Every step of the normalization is a rule at a position, so the proof
is a skeleton that the engine replays, as the plan of 2026-10-21 decided: the middle
terms of the transitivities are decided by unification, each rule's conclusion being
explicit.
-/
import Whitehead.Prove.Congr

namespace Whitehead.Prove

/-- An operation of the file: a term, with the arguments that are fixed (set.mm's `caddc`
in `co x y caddc`), by position; the others are its operands. -/
structure RingOp where
  term : Nat
  arity : Nat
  fixed : Array (Nat × Exp) := #[]
  deriving Inhabited, BEq

namespace RingOp

/-- The operands of `e`, if it is an application of the operation. -/
def operands (op : RingOp) (e : Exp) : Option (Array Exp) := do
  let (t, args) ← CongrTable.app e
  if t != op.term || args.size != op.arity then none
  for (i, f) in op.fixed do
    if args[i]? != some f then none
  some ((Array.range args.size).filterMap fun i => if op.fixed.any (·.1 == i) then none else some args[i]!)

/-- The application of the operation to `xs`, with its fixed arguments; `ty` the type of
the application. -/
def apply (op : RingOp) (xs : Array Exp) (ty : Nat) : Exp := Id.run do
  let mut args : Array Exp := #[]
  let mut k := 0
  for i in [0:op.arity] do
    match op.fixed.find? (·.1 == i) with
    | some (_, f) => args := args.push f
    | none =>
      args := args.push (xs[k]?.getD default)
      k := k + 1
  return Exp.mkApp op.term ty args

/-- The argument position of operand `k`. -/
def position (op : RingOp) (k : Nat) : Nat := Id.run do
  let mut seen := 0
  for i in [0:op.arity] do
    if op.fixed.any (·.1 == i) then continue
    if seen == k then return i
    seen := seen + 1
  return k

end RingOp

/-- The shapes of rules. The addition's and the negation's; the multiplication's are the
same shapes read over products, kept apart as `mulComm`, `mulAssoc`, `mulLcomm`, `oneR`,
`oneL`, `zeroR`, `zeroL`. -/
inductive RingShape where
  /-- `x ⊕ y = y ⊕ x` -/
  | comm
  /-- `(x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)` -/
  | assoc
  /-- `x ⊕ (y ⊕ z) = y ⊕ (x ⊕ z)` -/
  | lcomm
  /-- `x ⊕ 0 = x`, `0 ⊕ x = x` -/
  | unitR
  | unitL
  | mulComm
  | mulAssoc
  | mulLcomm
  /-- `x ⊗ 1 = x`, `1 ⊗ x = x` -/
  | oneR
  | oneL
  /-- `x ⊗ 0 = 0`, `0 ⊗ x = 0` -/
  | zeroR
  | zeroL
  /-- `x ⊗ (y ⊕ z) = (x ⊗ y) ⊕ (x ⊗ z)`, `(x ⊕ y) ⊗ z = (x ⊗ z) ⊕ (y ⊗ z)` -/
  | distL
  | distR
  /-- `x ⊕ ⊝x = 0` -/
  | inv
  /-- `⊝⊝x = x` -/
  | negneg
  /-- `x ⊖ y = x ⊕ ⊝y` -/
  | subDef
  /-- `⊝(x ⊕ y) = ⊝x ⊕ ⊝y` -/
  | negAdd
  /-- `⊝x ⊗ y = ⊝(x ⊗ y)`, `x ⊗ ⊝y = ⊝(x ⊗ y)` -/
  | negMulL
  | negMulR
  /-- `⊝0 = 0` -/
  | negZero
  deriving BEq, Hashable, Inhabited, Repr

/-- A rule: a lemma `[ph ->] L = R` in the inference form (`ded` false) or the deduction
form, and for each of its hypotheses, closure facts `[ph ->] x ∈ S`, the role of the
variable in the shape: 0 for `x`, 1 for `y`, 2 for `z`. -/
structure RingRule where
  id : Nat
  ded : Bool
  roles : Array Nat := #[]
  /-- The lemma states the shape the other way round (`negsubd`: `A + -B = A - B`), and
  is applied by symmetry. -/
  flipped : Bool := false
  deriving Inhabited, Repr

/-- A ring of the file: its equality, its operations and constants, its rules by shape
and form, and the transitivity and symmetry of its equality by form. -/
structure Ring where
  eq : Nat
  add : RingOp
  mul : RingOp
  zero : Exp := default
  one : Exp := default
  neg : Option RingOp := none
  sub : Option RingOp := none
  /-- The relation and the carrier of the closure hypotheses (`wcel`, `cc`), if the rules
  have them. -/
  carrier : Option (Nat × Exp) := none
  rules : Std.HashMap (RingShape × Bool) RingRule := {}
  /-- Transitivity by form: `x = y, y = z ⊢ x = z` (`eqtrd`), and the variant with the
  second hypothesis turned, `x = y, z = y ⊢ x = z` (`eqtr4d`), which joins two chains that
  end in the same term. -/
  trans : Std.HashMap Bool Nat := {}
  trans4 : Std.HashMap Bool Nat := {}
  symm : Std.HashMap Bool Nat := {}
  deriving Inhabited

/-- The ring table of a file: its rings, and what serves all of them: the lift of a plain
statement under an antecedent (`a1i`), and the closure lemmas in the deduction form — by
the term applied and the carrier, a lemma whose hypotheses state the closure of its
operands, with for each hypothesis the argument position; and the constants', by the
constant and the carrier (`1cnd`). -/
structure RingTable where
  rings : Array Ring := #[]
  lift : Option Nat := none
  closure : Std.HashMap (Nat × Exp) (Nat × Array Nat) := {}
  constClosure : Std.HashMap (Exp × Exp) Nat := {}
  deriving Inhabited

namespace RingTable

open CongrTable (app binary forms)

/-- An application whose arguments without a variable are the fixed ones of an
operation: the operation and its operands, the arguments with a variable. -/
def opOf (e : Exp) : Option (RingOp × Array Exp) := do
  let (t, args) ← app e
  let fixed := (Array.range args.size).filterMap fun i => if args[i]!.hasVars then none else some (i, args[i]!)
  let operands := args.filter (·.hasVars)
  if operands.isEmpty then none
  some ({ term := t, arity := args.size, fixed }, operands)

def var? (e : Exp) : Option Nat := if e.isVar then some (Node.varId e.nodes[0]!) else none

/-- Distinct variables, all of them? -/
def distinct (xs : Array (Option Nat)) : Bool :=
  xs.all (·.isSome) &&
    (xs.filterMap id).size == ((xs.filterMap id).foldl (init := (#[] : Array Nat)) fun acc v => if acc.contains v then acc else acc.push v).size

/-- What a shape read off `l = r` says: the shape, the operations it names, the constant
it names (a unit or the zero), and the variables in the roles `x`, `y`, `z`. -/
structure ShapeMatch where
  shape : RingShape
  add : Option RingOp := none
  mul : Option RingOp := none
  neg : Option RingOp := none
  sub : Option RingOp := none
  const : Option Exp := none
  vars : Array Nat := #[]
  deriving Inhabited

/-- The shapes `l = r` has, over any operations. The multiplication's own shapes come out
as the addition's (`comm` with `add := ⊗`) and are told apart when a ring is assembled. -/
def shapesOf (l r : Exp) : Array ShapeMatch := Id.run do
  let mut out := #[]
  let bin (e : Exp) : Option (RingOp × Exp × Exp) := do
    let (op, xs) ← opOf e
    if xs.size == 2 then some (op, xs[0]!, xs[1]!) else none
  let un (e : Exp) : Option (RingOp × Exp) := do
    let (op, xs) ← opOf e
    if xs.size == 1 then some (op, xs[0]!) else none
  let vs (xs : Array Exp) : Array Nat := xs.filterMap var?
  -- x ⊕ y = y ⊕ x
  if let some (o, x, y) := bin l then
    if let some (o', x', y') := bin r then
      if o == o' && distinct #[var? x, var? y] && x' == y && y' == x then
        out := out.push { shape := .comm, add := some o, vars := vs #[x, y] }
  -- (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)
  if let some (o, xy, z) := bin l then
    if let some (o1, x, y) := bin xy then
      if let some (o', x', yz) := bin r then
        if let some (o2, y', z') := bin yz then
          if o == o1 && o == o' && o == o2 && distinct #[var? x, var? y, var? z] && x' == x && y' == y && z' == z then
            out := out.push { shape := .assoc, add := some o, vars := vs #[x, y, z] }
  -- x ⊕ (y ⊕ z) = y ⊕ (x ⊕ z)
  if let some (o, x, yz) := bin l then
    if let some (o1, y, z) := bin yz then
      if let some (o', y', xz) := bin r then
        if let some (o2, x', z') := bin xz then
          if o == o1 && o == o' && o == o2 && distinct #[var? x, var? y, var? z] && x' == x && y' == y && z' == z then
            out := out.push { shape := .lcomm, add := some o, vars := vs #[x, y, z] }
  -- x ⊕ c = x (a unit), x ⊗ c = c (a zero); c ⊕ x = x, c ⊗ x = c: an application with one
  -- variable argument; each closed argument may be the constant, the rest being fixed
  if let some (t, args) := app l then
    let varPos := (Array.range args.size).filter fun i => (var? args[i]!).isSome
    if varPos.size == 1 && args.all fun a => (var? a).isSome || !a.hasVars then
      let xi := varPos[0]!
      let x := args[xi]!
      for ci in [0:args.size] do
        if ci == xi then continue
        let c := args[ci]!
        let fixed := (Array.range args.size).filterMap fun i => if i == xi || i == ci then none else some (i, args[i]!)
        let op : RingOp := { term := t, arity := args.size, fixed }
        let right := ci > xi
        if r == x then out := out.push { shape := if right then .unitR else .unitL, add := some op, const := some c, vars := vs #[x] }
        if r == c then out := out.push { shape := if right then .zeroR else .zeroL, mul := some op, const := some c, vars := vs #[x] }
  -- x ⊗ (y ⊕ z) = (x ⊗ y) ⊕ (x ⊗ z)
  if let some (m, x, yz) := bin l then
    if let some (a, y, z) := bin yz then
      if let some (a', xy', xz') := bin r then
        if let some (m1, x1, y1) := bin xy' then
          if let some (m2, x2, z2) := bin xz' then
            if m == m1 && m == m2 && a == a' && m != a && distinct #[var? x, var? y, var? z] &&
                x1 == x && y1 == y && x2 == x && z2 == z then
              out := out.push { shape := .distL, add := some a, mul := some m, vars := vs #[x, y, z] }
  -- (x ⊕ y) ⊗ z = (x ⊗ z) ⊕ (y ⊗ z)
  if let some (m, xy, z) := bin l then
    if let some (a, x, y) := bin xy then
      if let some (a', xz', yz') := bin r then
        if let some (m1, x1, z1) := bin xz' then
          if let some (m2, y2, z2) := bin yz' then
            if m == m1 && m == m2 && a == a' && m != a && distinct #[var? x, var? y, var? z] &&
                x1 == x && z1 == z && y2 == y && z2 == z then
              out := out.push { shape := .distR, add := some a, mul := some m, vars := vs #[x, y, z] }
  -- x ⊕ ⊝x = 0
  if let some (a, x, nx) := bin l then
    if let some (n, x') := un nx then
      if (var? x).isSome && x' == x && !r.hasVars then
        out := out.push { shape := .inv, add := some a, neg := some n, const := some r, vars := vs #[x] }
  -- ⊝⊝x = x
  if let some (n, nx) := un l then
    if let some (n', x) := un nx then
      if n == n' && (var? x).isSome && r == x then out := out.push { shape := .negneg, neg := some n, vars := vs #[x] }
  -- ⊝0 = 0: a closed application, the constant one of its arguments
  if let some (t, args) := app l then
    if !l.hasVars then
      for p in [0:args.size] do
        if r == args[p]! then
          let fixed := (Array.range args.size).filterMap fun i => if i == p then none else some (i, args[i]!)
          out := out.push { shape := .negZero, neg := some { term := t, arity := args.size, fixed }, const := some r }
  -- x ⊖ y = x ⊕ ⊝y
  if let some (s, x, y) := bin l then
    if let some (a, x', ny) := bin r then
      if let some (n, y') := un ny then
        if s != a && distinct #[var? x, var? y] && x' == x && y' == y then
          out := out.push { shape := .subDef, add := some a, neg := some n, sub := some s, vars := vs #[x, y] }
  -- ⊝(x ⊕ y) = ⊝x ⊕ ⊝y
  if let some (n, xy) := un l then
    if let some (a, x, y) := bin xy then
      if let some (a', nx, ny) := bin r then
        if let some (n1, x') := un nx then
          if let some (n2, y') := un ny then
            if n == n1 && n == n2 && a == a' && distinct #[var? x, var? y] && x' == x && y' == y then
              out := out.push { shape := .negAdd, add := some a, neg := some n, vars := vs #[x, y] }
  -- ⊝x ⊗ y = ⊝(x ⊗ y); x ⊗ ⊝y = ⊝(x ⊗ y)
  if let some (m, nx, y) := bin l then
    if let some (n, x) := un nx then
      if let some (n', xy) := un r then
        if let some (m', x', y') := bin xy then
          if n == n' && m == m' && distinct #[var? x, var? y] && x' == x && y' == y then
            out := out.push { shape := .negMulL, mul := some m, neg := some n, vars := vs #[x, y] }
  if let some (m, x, ny) := bin l then
    if let some (n, y) := un ny then
      if let some (n', xy) := un r then
        if let some (m', x', y') := bin xy then
          if n == n' && m == m' && distinct #[var? x, var? y] && x' == x && y' == y then
            out := out.push { shape := .negMulR, mul := some m, neg := some n, vars := vs #[x, y] }
  return out

/-- The hypotheses of a rule as closure facts of variables: for each `x ∈ S`, the
variable; and the relation with the carrier, the same for all. -/
def closureHyps (hyps : Array Exp) : Option (Array Nat × Option (Nat × Exp)) := Id.run do
  if hyps.isEmpty then return some (#[], none)
  let mut vars := #[]
  let mut rel : Option (Nat × Exp) := none
  for h in hyps do
    let some (r, x, s) := binary h | return none
    let some v := var? x | return none
    if s.hasVars then return none
    match rel with
    | none => rel := some (r, s)
    | some (r', s') => if r != r' || s != s' then return none
    vars := vars.push v
  return some (vars, rel)

/-- A shape read off an assertion, with its rule. -/
structure Found where
  eq : Nat
  m : ShapeMatch
  rule : RingRule
  carrier : Option (Nat × Exp)
  deriving Inhabited

/-- The table of a file. -/
def ofDb (db : Db) : RingTable := Id.run do
  let mut t : RingTable := {}
  let mut found : Array Found := #[]
  let mut transs : Array (Nat × Bool × Nat) := #[]
  let mut trans4s : Array (Nat × Bool × Nat) := #[]
  let mut symms : Array (Nat × Bool × Nat) := #[]
  for a in db.asserts do
    if a.pseudo.isSome then continue
    for f in forms a do
      if f.impl then continue
      let (ded, hyps, concl) := (f.ded, f.hyps, f.concl)
      -- the lift: hypothesis `x`, conclusion `y -> x`
      if !ded && hyps.size == 1 && hyps[0]!.isVar && t.lift.isNone then
        if let some (_, y, x) := binary concl then
          if y.isVar && x == hyps[0]! && y != x then t := { t with lift := some a.id }
      let some (rel, l, r) := binary concl | continue
      -- transitivity `x = y, y = z ⊢ x = z` and symmetry `x = y ⊢ y = x`
      if hyps.size == 2 then
        if let some (r1, x, y) := binary hyps[0]! then
          if let some (r2, u, v) := binary hyps[1]! then
            if r1 == rel && r2 == rel && l == x then
              if distinct #[var? x, var? y, var? v] && u == y && r == v then transs := transs.push (rel, ded, a.id)
              if distinct #[var? x, var? y, var? u] && v == y && r == u then trans4s := trans4s.push (rel, ded, a.id)
      if hyps.size == 1 then
        if let some (r1, x, y) := binary hyps[0]! then
          if r1 == rel && distinct #[var? x, var? y] && l == y && r == x then
            symms := symms.push (rel, ded, a.id)
      -- the rules: closure hypotheses of the statement's variables, or none
      let some (vars, carrier) := closureHyps hyps | continue
      let shapes := (shapesOf l r).map (·, false) ++ (shapesOf r l).map (·, true)
      if shapes.isEmpty then continue
      let lvars := ((l.nodes ++ r.nodes).filter Node.isVar).map Node.varId
      if !hyps.isEmpty && !lvars.all vars.contains then continue
      for (m, flipped) in shapes do
        -- the role of each hypothesis' variable in the shape
        let some roles := vars.mapM fun v => m.vars.findIdx? (· == v) | continue
        found := found.push { eq := rel, m, rule := { id := a.id, ded, roles, flipped }, carrier }
  -- the rings: an equality with a distributivity, its addition and its multiplication;
  -- the other shapes attached by the operations they name
  let mut rings : Array Ring := #[]
  for f in found do
    if !(f.m.shape matches .distL | .distR) then continue
    let some add := f.m.add | continue
    let some mul := f.m.mul | continue
    if rings.any fun rg => rg.eq == f.eq && rg.add == add && rg.mul == mul then continue
    let mut rg : Ring := { eq := f.eq, add, mul }
    -- the first lemma of a shape is kept, but one stated the right way round replaces one
    -- that is flipped
    let put (rg : Ring) (sh : RingShape) (r : RingRule) : Ring :=
      match rg.rules[(sh, r.ded)]? with
      | none => { rg with rules := rg.rules.insert (sh, r.ded) r }
      | some old => if old.flipped && !r.flipped then { rg with rules := rg.rules.insert (sh, r.ded) r } else rg
    -- two rounds: the negation is named by the inverse or the subtraction, and then its
    -- own shapes attach
    for _ in [0:2] do
      for g in found do
        if g.eq != f.eq then continue
        let m := g.m
        let isAdd := m.add == some add
        let isMul := m.add == some mul || m.mul == some mul
        let isNeg := m.neg.isSome && m.neg == rg.neg
        match m.shape with
        | .comm | .assoc | .lcomm =>
          if m.add == some add then rg := put rg m.shape g.rule
          else if m.add == some mul then
            rg := put rg (match m.shape with | .comm => .mulComm | .assoc => .mulAssoc | _ => .mulLcomm) g.rule
        | .unitR | .unitL =>
          if m.add == some add then
            rg := put { rg with zero := m.const.getD rg.zero } m.shape g.rule
          else if m.add == some mul then
            rg := put { rg with one := m.const.getD rg.one } (if m.shape == .unitR then .oneR else .oneL) g.rule
        | .zeroR | .zeroL =>
          if isMul && m.mul == some mul then rg := put { rg with zero := m.const.getD rg.zero } m.shape g.rule
        | .distL | .distR =>
          if isAdd && m.mul == some mul then rg := put rg m.shape g.rule
        | .inv =>
          if isAdd then
            if rg.neg.isNone then rg := { rg with neg := m.neg }
            if rg.neg == m.neg then rg := put { rg with zero := m.const.getD rg.zero } m.shape g.rule
        | .subDef =>
          if isAdd then
            if rg.neg.isNone then rg := { rg with neg := m.neg }
            if rg.sub.isNone then rg := { rg with sub := m.sub }
            if rg.neg == m.neg && rg.sub == m.sub then rg := put rg m.shape g.rule
        | .negAdd =>
          if isAdd && isNeg then rg := put rg m.shape g.rule
        | .negMulL | .negMulR =>
          if m.mul == some mul && isNeg then rg := put rg m.shape g.rule
        | .negneg | .negZero =>
          if isNeg then rg := put rg m.shape g.rule
        | _ => pure ()
        if g.carrier.isSome && rg.carrier.isNone && (isAdd || isMul) then rg := { rg with carrier := g.carrier }
    let first (xs : Array (Nat × Bool × Nat)) : Std.HashMap Bool Nat :=
      xs.foldl (init := {}) fun mp (e, d, k) => if e == f.eq && !mp.contains d then mp.insert d k else mp
    rg := { rg with trans := first transs, trans4 := first trans4s, symm := first symms }
    rings := rings.push rg
  t := { t with rings }
  -- the closure lemmas, in the deduction form: `[ph ->] x ∈ S, … ⊢ [ph ->] (t … x …) ∈ S`,
  -- the operands variables each with its closure stated; and the constants' closures
  for a in db.asserts do
    if a.pseudo.isSome then continue
    for f in forms a do
      if !f.ded then continue
      let (hyps, concl) := (f.hyps, f.concl)
      let some (_, e, s) := binary concl | continue
      if s.hasVars then continue
      let some (vars, carrier) := closureHyps hyps | continue
      if hyps.isEmpty then
        if !e.hasVars && !t.constClosure.contains (e, s) then
          t := { t with constClosure := t.constClosure.insert (e, s) a.id }
        continue
      let some (_, s') := carrier | continue
      if s' != s then continue
      let some (term, args) := app e | continue
      let some positions := vars.mapM fun v => (Array.range args.size).find? fun i => var? args[i]! == some v | continue
      if positions.size != (args.filter (·.hasVars)).size then continue
      if !t.closure.contains (term, s) then t := { t with closure := t.closure.insert (term, s) (a.id, positions) }
  return t

end RingTable

/-! ### Normalization -/

/-- A term over a ring: an atom (any other subexpression), a sum, a product, a negation, a
subtraction, the zero and the one. -/
inductive RTerm where
  | atom (e : Exp)
  | add (a b : RTerm)
  | mul (a b : RTerm)
  | neg (a : RTerm)
  | sub (a b : RTerm)
  | zero
  | one
  deriving BEq, Inhabited

namespace RTerm

/-- `e` read over the ring. -/
partial def ofExp (rg : Ring) (e : Exp) : RTerm :=
  if e == rg.zero then .zero
  else if e == rg.one then .one
  else
    match rg.add.operands e with
    | some xs => if xs.size == 2 then .add (ofExp rg xs[0]!) (ofExp rg xs[1]!) else .atom e
    | none =>
      match rg.mul.operands e with
      | some xs => if xs.size == 2 then .mul (ofExp rg xs[0]!) (ofExp rg xs[1]!) else .atom e
      | none =>
        match rg.neg.bind (·.operands e), rg.sub.bind (·.operands e) with
        | some xs, _ => if xs.size == 1 then .neg (ofExp rg xs[0]!) else .atom e
        | _, some xs => if xs.size == 2 then .sub (ofExp rg xs[0]!) (ofExp rg xs[1]!) else .atom e
        | _, _ => .atom e

/-- The term as an expression of the file, with the ring's operations; `ty` the type of
its applications. -/
partial def toExp (rg : Ring) (ty : Nat) : RTerm → Exp
  | .atom e => e
  | .zero => rg.zero
  | .one => rg.one
  | .add a b => rg.add.apply #[toExp rg ty a, toExp rg ty b] ty
  | .mul a b => rg.mul.apply #[toExp rg ty a, toExp rg ty b] ty
  | .neg a => (rg.neg.getD rg.add).apply #[toExp rg ty a] ty
  | .sub a b => (rg.sub.getD rg.add).apply #[toExp rg ty a, toExp rg ty b] ty

/-- The order of atoms and monomials: by the expression of an atom, the structure
otherwise; a monomial and its negation side by side, the positive first. -/
partial def key : RTerm → Array Nat
  | .zero => #[0]
  | .one => #[1]
  | .atom e => #[2] ++ e.nodes
  | .mul x y => #[3] ++ key x ++ #[4] ++ key y
  | .neg x => key x ++ #[5]
  | .add x y => #[6] ++ key x ++ #[7] ++ key y
  | .sub x y => #[8] ++ key x ++ #[9] ++ key y

def lt (a b : RTerm) : Bool := key a < key b

/-- The subterm at `path`, the operand taken at each step. -/
partial def at_ (t : RTerm) (path : List Nat) : Option RTerm :=
  match path, t with
  | [], _ => some t
  | 0 :: p, .add a _ | 0 :: p, .mul a _ | 0 :: p, .sub a _ | 0 :: p, .neg a => at_ a p
  | 1 :: p, .add _ b | 1 :: p, .mul _ b | 1 :: p, .sub _ b => at_ b p
  | _, _ => none

partial def replace (t : RTerm) (path : List Nat) (s : RTerm) : RTerm :=
  match path, t with
  | [], _ => s
  | 0 :: p, .add a b => .add (replace a p s) b
  | 1 :: p, .add a b => .add a (replace b p s)
  | 0 :: p, .mul a b => .mul (replace a p s) b
  | 1 :: p, .mul a b => .mul a (replace b p s)
  | 0 :: p, .sub a b => .sub (replace a p s) b
  | 1 :: p, .sub a b => .sub a (replace b p s)
  | 0 :: p, .neg a => .neg (replace a p s)
  | _, _ => t

/-- Not a sum, a product, a negation or a subtraction. -/
def isLeaf : RTerm → Bool
  | .atom _ | .zero | .one => true
  | _ => false

/-- A factor of a product in normal form: an atom. -/
def isFactor : RTerm → Bool
  | .atom _ => true
  | _ => false

/-- A monomial without its sign: an atom, or a right-nested product of atoms in order. -/
partial def isMonomial : RTerm → Bool
  | .atom _ => true
  | .one => true
  | .mul (.atom a) rest => isMonomial rest && rest != .one &&
      (match rest with
        | .atom b => !lt (.atom b) (.atom a)
        | .mul (.atom b) _ => !lt (.atom b) (.atom a)
        | _ => false)
  | _ => false

def strip : RTerm → RTerm
  | .neg m => m
  | m => m

/-- A term in normal form. -/
partial def isNormal : RTerm → Bool
  | .zero => true
  | .add m rest => isMonomial (strip m) && rest != .zero && isNormal rest &&
      (match rest with
        | .add m' _ => !lt m' m
        | m' => !lt m' m)
  | m => isMonomial (strip m)

end RTerm

/-- One step of a normalization: a rule applied at a position, in the lemma's direction or
backwards. -/
structure RingStep where
  path : List Nat
  shape : RingShape
  back : Bool := false
  deriving Repr, Inhabited

namespace RTerm

/-- The rule applied at the top of `t`, if it applies: what it rewrites `t` to, and the
subterms in the roles `x`, `y`, `z`. -/
def applyTop (shape : RingShape) (back : Bool) (t : RTerm) : Option (RTerm × Array RTerm) :=
  match shape, back, t with
  | .comm, _, .add a b => some (.add b a, #[a, b])
  | .assoc, false, .add (.add a b) c => some (.add a (.add b c), #[a, b, c])
  | .assoc, true, .add a (.add b c) => some (.add (.add a b) c, #[a, b, c])
  | .lcomm, _, .add a (.add b c) => some (.add b (.add a c), #[a, b, c])
  | .unitR, false, .add a .zero => some (a, #[a])
  | .unitL, false, .add .zero a => some (a, #[a])
  | .mulComm, _, .mul a b => some (.mul b a, #[a, b])
  | .mulAssoc, false, .mul (.mul a b) c => some (.mul a (.mul b c), #[a, b, c])
  | .mulAssoc, true, .mul a (.mul b c) => some (.mul (.mul a b) c, #[a, b, c])
  | .mulLcomm, _, .mul a (.mul b c) => some (.mul b (.mul a c), #[a, b, c])
  | .oneR, false, .mul a .one => some (a, #[a])
  | .oneL, false, .mul .one a => some (a, #[a])
  | .zeroR, false, .mul a .zero => some (.zero, #[a])
  | .zeroL, false, .mul .zero a => some (.zero, #[a])
  | .distL, false, .mul a (.add b c) => some (.add (.mul a b) (.mul a c), #[a, b, c])
  | .distR, false, .mul (.add a b) c => some (.add (.mul a c) (.mul b c), #[a, b, c])
  | .inv, false, .add a (.neg a') => if a == a' then some (.zero, #[a]) else none
  | .negneg, false, .neg (.neg a) => some (a, #[a])
  | .subDef, false, .sub a b => some (.add a (.neg b), #[a, b])
  | .negAdd, false, .neg (.add a b) => some (.add (.neg a) (.neg b), #[a, b])
  | .negMulL, false, .mul (.neg a) b => some (.neg (.mul a b), #[a, b])
  | .negMulR, false, .mul a (.neg b) => some (.neg (.mul a b), #[a, b])
  | .negZero, false, .neg .zero => some (.zero, #[])
  | _, _, _ => none

/-- The step to take at the top of `t`, if the term is not yet in normal form there: the
rewrite strategy, with the rules the file has (`avail`). The subterms are assumed normal
already (the strategy works from the inside out). Left commutativity, where the file
lacks it, is associativity backwards, commutativity inside, associativity forward. -/
def stepAt (avail : RingShape → Bool) (t : RTerm) : Option (RingShape × Bool) :=
  let want (s : RingShape) : Option (RingShape × Bool) := if avail s then some (s, false) else none
  match t with
  | .sub _ _ => want .subDef
  | .neg .zero => want .negZero
  | .neg (.neg _) => want .negneg
  | .neg (.add _ _) => want .negAdd
  | .neg (.sub _ _) => none
  | .mul (.neg _) _ => want .negMulL
  | .mul _ (.neg _) => want .negMulR
  | .mul _ .zero => want .zeroR
  | .mul .zero _ => want .zeroL
  | .mul _ .one => want .oneR
  | .mul .one _ => want .oneL
  | .mul _ (.add _ _) => want .distL
  | .mul (.add _ _) _ => want .distR
  | .mul (.mul _ _) _ => want .mulAssoc
  | .mul a (.mul b _) =>
    if lt b a then want .mulLcomm <|> (if avail .mulAssoc then some (.mulAssoc, true) else none) else none
  | .mul a b => if lt b a then want .mulComm else none
  | .add _ .zero => want .unitR
  | .add .zero _ => want .unitL
  | .add (.add _ _) _ => want .assoc
  | .add a (.add b _) =>
    -- a monomial and its negation side by side cancel: (a + -a) + rest, by assoc backwards
    if strip a == strip b && a != b then (if avail .assoc then some (.assoc, true) else none)
    else if lt b a then want .lcomm <|> (if avail .assoc then some (.assoc, true) else none) else none
  | .add a b =>
    if strip a == strip b && a != b then
      (match a, b with | _, .neg _ => want .inv | .neg _, _ => want .comm | _, _ => none)
    else if lt b a then want .comm else none
  | _ => none

/-- The normalization of `t` with the rules `avail`: its steps, innermost first, and the
normal form; none if it does not end within `fuel` steps. -/
partial def normalize (t : RTerm) (avail : RingShape → Bool := fun _ => true) (fuel : Nat := 2000) :
    Option (Array RingStep × RTerm) := Id.run do
  let mut t := t
  let mut steps : Array RingStep := #[]
  for _ in [0:fuel] do
    match firstStep t [] with
    | none => return some (steps, t)
    | some (path, shape, back) =>
      let some here := t.at_ path | return none
      let some (here', _) := applyTop shape back here | return none
      t := t.replace path here'
      steps := steps.push { path, shape, back }
  return none
where
  /-- The first step, innermost and leftmost. -/
  firstStep (t : RTerm) (path : List Nat) : Option (List Nat × RingShape × Bool) :=
    let below := match t with
      | .add a b | .mul a b | .sub a b => firstStep a (path ++ [0]) <|> firstStep b (path ++ [1])
      | .neg a => firstStep a (path ++ [0])
      | _ => none
    below <|> (stepAt avail t).map fun (s, b) => (path, s, b)

end RTerm

/-! ### The skeleton -/

namespace RingTable

/-- How much of `e` a ring reads: its operations in it, counted. -/
partial def coverage (rg : Ring) : RTerm → Nat
  | .atom _ | .zero | .one => 0
  | .add a b | .mul a b | .sub a b => 1 + coverage rg a + coverage rg b
  | .neg a => 1 + coverage rg a

/-- The rings of the file whose equality `rel` is and that read something of the sides,
the one reading most first, then the one with most rules: the file has rings besides
the one meant (set.mm: `·` with `↑`, since exponentiation distributes over
multiplication; `min` with `+`), and a goal is planned with each in turn. -/
def ringsFor (t : RingTable) (rel : Nat) (l r : Exp) : Array Ring :=
  let scored := t.rings.filterMap fun rg =>
    if rg.eq != rel then none
    else
      let c := coverage rg (RTerm.ofExp rg l) + coverage rg (RTerm.ofExp rg r)
      if c == 0 then none else some (c, rg.rules.size, rg)
  (scored.qsort fun a b => a.1 > b.1 || a.1 == b.1 && a.2.1 > b.2.1).map (·.2.2)

/-- The closure of `e` in the ring's carrier, in the deduction form: the file's closure
lemmas down the structure of `e`, a constant's lemma at a constant; open where there is
none (an atom: the search's part). -/
partial def closurePlan (t : RingTable) (limit : Nat) (carrier : Exp) (e : Exp) : Skeleton :=
  match t.constClosure[(e, carrier)]? with
  | some k => if k < limit then .step k #[] else .hyp 0
  | none =>
    match CongrTable.app e with
    | none => .hyp 0
    | some (term, args) =>
      match t.closure[(term, carrier)]? with
      | some (k, positions) =>
        if k < limit then .step k (positions.map fun i => closurePlan t limit carrier (args[i]?.getD default))
        else .hyp 0
      | none => .hyp 0

/-- The skeleton of a step of a ring `rg` at `path` of `t`: the congruence down the path
(`tb`), the rule at its end, backwards by symmetry if `back`, lifted if the rule is plain
and the goal in the deduction form; the rule's closure hypotheses planned. -/
partial def stepSkeleton (t : RingTable) (tb : CongrTable) (rg : Ring) (limit : Nat) (ded : Bool) (ty : Nat)
    (term : RTerm) (st : RingStep) : Option Skeleton := do
  let sub ← term.at_ st.path
  let (_, roles) ← RTerm.applyTop st.shape st.back sub
  -- the rule, in the goal's form or lifted from the plain one
  let (rule, lifted) ← match rg.rules[(st.shape, ded)]? with
    | some r => if r.id < limit then some (r, false) else none
    | none =>
      if ded then
        match rg.rules[(st.shape, false)]? with
        | some r => if r.id < limit && t.lift.any (· < limit) then some (r, true) else none
        | none => none
      else none
  let toExp (x : RTerm) : Exp := RTerm.toExp rg ty x
  let closure := rule.roles.map fun k =>
    match rg.carrier, roles[k]? with
    | some (_, c), some x => if rule.ded then t.closurePlan limit c (toExp x) else .hyp 0
    | _, _ => .hyp 0
  let mut sk : Skeleton := .step rule.id closure
  if lifted then
    let lift ← t.lift
    sk := .step lift #[sk]
  -- backwards, or a lemma stated the other way round: by symmetry (both: as it is)
  if st.back != rule.flipped then
    let symm ← rg.symm[ded]?
    if symm ≥ limit then none
    sk := .step symm #[sk]
  -- the congruence down the path: at each operation on the way, the lemma for the
  -- position taken
  let rec down (x : RTerm) (path : List Nat) : Option Skeleton :=
    match path with
    | [] => some sk
    | i :: rest => do
      let (op, args) ← match x with
        | .add a b => some (rg.add, #[a, b])
        | .mul a b => some (rg.mul, #[a, b])
        | .sub a b => do let s ← rg.sub; some (s, #[a, b])
        | .neg a => do let n ← rg.neg; some (n, #[a])
        | _ => none
      let pos := op.position i
      let lem ← tb.pick limit op.term rg.eq ded #[pos]
      let children := lem.hypPos.map fun j =>
        if j == pos then (down (args[i]?.getD default) rest).getD (.hyp 0)
        else
          let ri := (lem.positions[j]?.getD none).getD 0
          (tb.reflStep limit ri ded).getD (.hyp 0)
      some (tb.applyLemma lem children)
  down term st.path

/-- `l = r`, in form `ded`, proved by normalizing both sides: none if they do not meet, or a
step has no lemma. -/
partial def plan (t : RingTable) (tb : CongrTable) (rg : Ring) (limit : Nat) (ded : Bool) (l r : Exp) :
    Option Skeleton := do
  let tl := RTerm.ofExp rg l
  let tr := RTerm.ofExp rg r
  if tl == tr then return (← tb.reflStep limit rg.eq ded)
  -- the rules the theorem may use: in the goal's form, or plain and lifted
  let avail (sh : RingShape) : Bool :=
    (rg.rules[(sh, ded)]?).any (·.id < limit) ||
      (ded && (rg.rules[(sh, false)]?).any (·.id < limit) && t.lift.any (· < limit))
  let (sl, nl) ← tl.normalize avail
  let (sr, nr) ← tr.normalize avail
  if nl != nr then none
  let ty := l.ty
  -- a chain of steps from `x` along `steps`: x = x₁ = … = n, by transitivity
  let chain (x : RTerm) (steps : Array RingStep) : Option (Option Skeleton) := Id.run do
    let mut cur := x
    let mut parts : Array Skeleton := #[]
    for st in steps do
      let some sk := t.stepSkeleton tb rg limit ded ty cur st | return none
      parts := parts.push sk
      let some sub := cur.at_ st.path | return none
      let some (sub', _) := RTerm.applyTop st.shape st.back sub | return none
      cur := cur.replace st.path sub'
    if parts.isEmpty then return some none
    -- x = x₁ and x₁ = n give x = n: by `trans`, or by `trans4` with the second turned
    let mut sk := parts.back!
    for i in [0:parts.size - 1] do
      let p := parts[parts.size - 2 - i]!
      match rg.trans[ded]?, rg.trans4[ded]?, rg.symm[ded]? with
      | some tr, _, _ => if tr ≥ limit then return none else sk := .step tr #[p, sk]
      | none, some t4, some sy => if t4 ≥ limit || sy ≥ limit then return none else sk := .step t4 #[p, .step sy #[sk]]
      | _, _, _ => return none
    return some (some sk)
  let left ← chain tl sl
  let right ← chain tr sr
  let symm? := rg.symm[ded]?.filter (· < limit)
  match left, right with
  | none, none => tb.reflStep limit rg.eq ded
  | some a, none => some a
  | none, some b => do
    let symm ← symm?
    some (.step symm #[b])
  | some a, some b =>
    -- l = n and r = n give l = r: by `trans4`, or by `trans` with the second turned
    match rg.trans4[ded]?.filter (· < limit), rg.trans[ded]?.filter (· < limit), symm? with
    | some t4, _, _ => some (.step t4 #[a, b])
    | none, some tr, some sy => some (.step tr #[a, .step sy #[b]])
    | _, _, _ => none

/-- The skeleton for goal `g` of a theorem numbered `limit`: in the inference form, or
under the connective in the deduction form. -/
def planGoal (t : RingTable) (tb : CongrTable) (limit : Nat) (g : Exp) : Option Skeleton :=
  let first (ded : Bool) (rel : Nat) (l r : Exp) : Option Skeleton :=
    (t.ringsFor rel l r).findSome? fun rg => t.plan tb rg limit ded l r
  let inference := do
    let (rel, l, r) ← CongrTable.binary g
    first false rel l r
  let deduction := do
    let conn ← tb.connective
    let (c, _, body) ← CongrTable.binary g
    if c != conn then none
    let (rel, l, r) ← CongrTable.binary body
    first true rel l r
  inference <|> deduction

end RingTable

end Whitehead.Prove
