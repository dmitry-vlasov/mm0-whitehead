/-
Strategies built from strategies: a port of the core of
`russell-flow/src/ru/prover/tactics/combinators.flow` and `focus.flow`, with filters
(`Filter.lean`) as what restricts a strategy.

A restricted strategy is handed a tree whose leaves are only those that pass, as
Russell's `focus` does; everything else is shared, so the inner strategy works as it
always does and never learns that it was restricted. The leaves left out stay leaves:
nothing is pruned, and another strategy may expand them later.

The time of a run is not a strategy's business here: a strategy's step reads the tree
and has no clock, and the time is a limit of the run (`Limits.maxMs`).
-/
import Whitehead.Prove.Prove
import Whitehead.Prove.Filter

namespace Whitehead.Prove

/-- A strategy, whatever its state: what the DSL builds (`Dsl.lean`). -/
structure AnyStrategy where
  {σ : Type}
  strategy : Strategy σ

/-- The number of assertion nodes from the root to assertion node `p`, both counted. -/
def Env.propDepth (env : Env) (p : Nat) : Nat := Id.run do
  let mut d := 1
  let mut q := p
  for _ in [0:env.props.size] do
    match env.hyps[env.props[q]!.parent]!.parent with
    | some q' =>
      d := d + 1
      q := q'
    | none => return d
  return d

/-- Is assertion node `p` in the subtree of goal node `h`: is `h` its parent, or the parent
of an assertion node above it? -/
def Env.isUnder (env : Env) (p h : Nat) : Bool := Id.run do
  let mut g := env.props[p]!.parent
  for _ in [0:env.hyps.size] do
    if g == h then return true
    match env.hyps[g]!.parent with
    | some q => g := env.props[q]!.parent
    | none => return false
  return false

namespace Strategy

/-- `s`, seeing as leaves only the assertion nodes that `keep` admits (`ruFocusTactic`).
What `keep` says of a node is asked once and kept, so it must depend on the node only. -/
def restrict {σ : Type} (keep : Env → Nat → Bool) (s : Strategy σ) : Strategy (σ × Std.HashMap Nat Bool) where
  root := s.root
  init := (s.init, {})
  step env st := Id.run do
    let mut seen := st.2
    let mut leafs := #[]
    for p in env.leafs do
      match seen[p]? with
      | some b => if b then leafs := leafs.push p
      | none =>
        let b := keep env p
        seen := seen.insert p b
        if b then leafs := leafs.push p
    let (d, inner) := s.step { env with leafs } st.1
    return (d, (inner, seen))
  forward := s.forward
  admitJoin := s.admitJoin

/-- `s`, expanding only the variants that pass the filter. -/
def filtered {σ : Type} (f : Filter) (s : Strategy σ) : Strategy (σ × Std.HashMap Nat Bool) :=
  s.restrict fun env p => f.eval (env.propView p)

/-- `s` until the tree has `size` more assertion nodes than when it started (the size
cap of `ruLimitedTactic`, a delta). It is looked at between the decisions of `s`, so a
round of breadth-first can go past it. -/
def sized {σ : Type} (size : Nat) (s : Strategy σ) : Strategy (σ × Option Nat) where
  root := s.root
  init := (s.init, none)
  step env st :=
    let start := st.2.getD env.props.size
    if env.props.size ≥ start + size then (.done, (st.1, some start))
    else
      let (d, inner) := s.step env st.1
      (d, (inner, some start))
  forward := s.forward
  admitJoin := s.admitJoin

/-- `a`, then `b` once `a` is done (`ruSequenceTactic`). The search is seeded forward if
either goes forward; a join is admitted if both admit it. -/
def seq {σ τ : Type} (a : Strategy σ) (b : Strategy τ) : Strategy (σ × τ × Bool) where
  root := a.root
  init := (a.init, b.init, false)
  step env st :=
    let (sa, sb, second) := st
    if second then
      let (d, sb') := b.step env sb
      (d, (sa, sb', true))
    else
      match a.step env sa with
      | (.done, sa') =>
        let (d, sb') := b.step env sb
        (d, (sa', sb', true))
      | (d, sa') => (d, (sa', sb, false))
  forward := a.forward || b.forward
  admitJoin f g := a.admitJoin f g && b.admitJoin f g

/-- The strategy that does nothing (`ruDoneTactic`). -/
def done : Strategy Unit where
  root := none
  init := ()
  step _ _ := (.done, ())

end Strategy

namespace AnyStrategy

def filtered (a : AnyStrategy) (f : Filter) : AnyStrategy := ⟨a.strategy.filtered f⟩

/-- `limited(t, size, depth)` (`ruLimitedTactic`): the size is a number of assertion nodes
added (0: no limit); the depth, the depth of the leaves expanded (0: no limit). -/
def limited (a : AnyStrategy) (size depth : Nat) : AnyStrategy :=
  let a := if depth == 0 then a else ⟨a.strategy.restrict fun env p => env.propDepth p ≤ depth⟩
  if size == 0 then a else ⟨a.strategy.sized size⟩

def seq (a b : AnyStrategy) : AnyStrategy := ⟨a.strategy.seq b.strategy⟩

/-- `a`, only in the subtree of goal node `h` (Russell's `focus`, with one seed). -/
def focus (a : AnyStrategy) (h : Nat) : AnyStrategy := ⟨a.strategy.restrict fun env p => env.isUnder p h⟩

end AnyStrategy

end Whitehead.Prove
