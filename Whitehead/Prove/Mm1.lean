/-
A proof of the prover as an MM1 proof term (`mm0-hs/mm1.md`, "refine"), so that an MM1
user can put it where a proof is wanted: the gap filler of the agent bench
(`docs/DESIGN.md`, "Whitehead as a gap filler").

- An application is, by the form asked for:
  - `short`: `(foo p1 ... pm)`, the proofs of `foo`'s hypotheses only; MM1's unification
    finds the variables. It cannot name a dummy: a bound variable that the statement
    does not have is left a metavariable, and MM1 rejects the proof;
  - `bound`: `(!! foo x1 ... xk p1 ... pm)` for an assertion with bound variables, which
    are given by their names; the regular ones are left to unification;
  - `explicit`: `(! foo x1 ... xn p1 ... pm)`, every variable, a bound one by its name and
    a regular one as a formula `$ ... $`.

  A variable that is not one of the theorem's is a dummy, named `wd` and its number,
  which MM1 declares when it meets it.
- A conversion (the pseudo-assertion `conv`, `b, a ≡' b ⊢ a`) is its proof of `b` alone:
  MM1's unification unfolds definitions itself. An unfolding of the prover (`conv` of
  `ProofTree`) is its child, for the same reason.
- A hypothesis of the theorem is its name.
-/
import Whitehead.Prove.Show

namespace Whitehead.Prove

/-- The name of a variable that is not one of the theorem's, in an MM1 term. -/
def mm1Dummy (v : Nat) : String := s!"wd{v}"

/-- How much of the substitution an MM1 term gives (see the header). -/
inductive Mm1Form where
  | short
  | bound
  | explicit
  deriving BEq, Inhabited

/-- `t` as an MM1 proof term. `hypNames` names the hypotheses of the theorem, and `pr`
prints formulas; its constants are the theorem's variables. -/
partial def ProofTree.mm1 (db : Db) (pr : Printer) (hypNames : Array String) (form : Mm1Form) :
    ProofTree → String
  | .hyp i => hypNames[i]?.getD s!"h{i}"
  | .conv _ _ _ _ _ child => child.mm1 db pr hypNames form
  | .step a args children =>
    let as_ := db.asserts[a]!
    match as_.pseudo with
    | some .conv => (children[0]?.map (·.mm1 db pr hypNames form)).getD "_"
    | some _ => "_"
    | none =>
      let kids := children.map (·.mm1 db pr hypNames form)
      let isBound (i : Nat) : Bool := as_.binders[i]?.any (·.bound)
      let render (i : Nat) : String := pr.render args[i]! mm1Dummy
      let app (head : String) (xs : Array String) : String :=
        if xs.isEmpty then head else s!"({head} {" ".intercalate xs.toList})"
      match form with
      | .short => app as_.name kids
      | .bound =>
        let bs := ((Array.range args.size).filter isBound).map render
        if bs.isEmpty then app as_.name kids else app s!"!! {as_.name}" (bs ++ kids)
      | .explicit =>
        let vars := (Array.range args.size).map fun i => if isBound i then render i else s!"$ {render i} $"
        app s!"! {as_.name}" (vars ++ kids)

/-- A statement of MM1 with its metavariables `?a` made holes `_`, and the name of each
hole, in order. -/
def mm1Holes (text : String) : String × Array String := Id.run do
  let cs := text.toList.toArray
  let mut out := ""
  let mut names := #[]
  let mut i := 0
  while i < cs.size do
    if cs[i]! == '?' && i + 1 < cs.size && (cs[i + 1]!.isAlphanum || cs[i + 1]! == '_') then
      let mut j := i + 1
      let mut name := ""
      while j < cs.size && (cs[j]!.isAlphanum || cs[j]! == '_') do
        name := name.push cs[j]!
        j := j + 1
      out := out.push '_'
      names := names.push name
      i := j
    else
      out := out.push cs[i]!
      i := i + 1
  return (out, names)

end Whitehead.Prove
