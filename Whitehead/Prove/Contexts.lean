/-
Contexts of use, per assertion (`docs/DESIGN.md`, "Contexts per assertion"): the 2013
paper's experience of an assertion, E⁺ and E⁻, as data for the rank of variants. For each
assertion, the goals of the earlier proofs where it was used (positive), and a sample of
the goals it unified with where another assertion was used (negative). A goal is a weighted
vector of its terms and parent–child term pairs, as the theorem prior's statements are
(`Prior.lean`); the features of a variant at a goal read how like the goal is to the
assertion's positive and negative contexts, and the rival similarity between the two.

Only the contexts of theorems before the one being proved are read, so a model tested on
later theorems is tested out of sample. The build is in `Dataset.lean` (`Contexts.build`):
it replays the known proofs with every variant of each goal, as the export does.
-/
import Std.Data.HashMap
import Whitehead.Prove.Exp

namespace Whitehead.Prove

/-- The parent–child term pairs of `e`: for each application, its term with the term of
each of its arguments that is an application. -/
def Exp.termPairs (e : Exp) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  for i in [0:e.nodes.size] do
    let n := e.nodes[i]!
    if Node.isVar n || Node.isConst n then continue
    for j in e.argStarts i do
      let m := e.nodes[j]!
      if Node.isVar m || Node.isConst m then continue
      let p := (Node.appId n, Node.appId m)
      if !out.contains p then out := out.push p
  return out

/-- A goal as a weighted vector of its features (terms, then pairs), of length 1. -/
abbrev CtxVec := Array (Nat × Float)

/-- A context of use: the theorem whose proof it is from, and the goal's vector. -/
abbrev Context := Nat × CtxVec

structure Contexts where
  /-- The weight of each term, 0 for one left out as too common. -/
  idf : Array Float := #[]
  /-- The numbers of the pairs, after the terms, and their weights. -/
  pairIds : Std.HashMap (Nat × Nat) Nat := {}
  pairIdf : Array Float := #[]
  /-- For each assertion, the goals where it was used, by theorem. -/
  pos : Array (Array Context) := #[]
  /-- For each assertion, a sample of the goals it unified with where another assertion
  was used, by theorem. -/
  neg : Array (Array Context) := #[]
  deriving Inhabited

namespace Contexts

/-- The vector of goal `e`. -/
def vectorOf (c : Contexts) (e : Exp) : CtxVec := Id.run do
  let mut ws : Array (Nat × Float) := #[]
  for t in e.terms do
    let w := c.idf[t]?.getD 0
    if w > 0 then ws := ws.push (t, w)
  for p in e.termPairs do
    let some id := c.pairIds[p]? | continue
    let w := c.pairIdf[id]?.getD 0
    if w > 0 then ws := ws.push (c.idf.size + id, w)
  let norm := Float.sqrt (ws.foldl (init := 0) fun acc (_, w) => acc + w * w)
  return if norm == 0 then #[] else ws.map fun (t, w) => (t, w / norm)

/-- A vector as a map, for the dot products of `best`. -/
def lookup (v : CtxVec) : Std.HashMap Nat Float :=
  v.foldl (init := {}) fun m (t, w) => m.insert t w

/-- The dot product of a context's vector with a goal's map. -/
def dot (v : CtxVec) (g : Std.HashMap Nat Float) : Float :=
  v.foldl (init := 0) fun acc (t, w) => acc + w * (g.getD t 0)

/-- The best similarity of a goal `g` (as `lookup` gives it) to the contexts `cs` of
theorems before `limit`; 0 if there are none. -/
def bestOf (cs : Array Context) (limit : Nat) (g : Std.HashMap Nat Float) : Float :=
  cs.foldl (init := 0) fun acc (thm, v) => if thm < limit then max acc (dot v g) else acc

/-- At a goal `g`, assertion `a`'s best similarity to its positive and to its negative
contexts of theorems before `limit`. -/
def best (c : Contexts) (a limit : Nat) (g : Std.HashMap Nat Float) : Float × Float :=
  (bestOf (c.pos[a]?.getD #[]) limit g, bestOf (c.neg[a]?.getD #[]) limit g)

/-- The rival similarity of the 2013 paper: how much nearer the positive contexts are than
the negative, from −1 to 1; 0 where there is neither. -/
def rival (p n : Float) : Float := if p + n == 0 then 0 else (p - n) / (p + n)

/-- The contexts as lines: the assertion, the theorem, 1 for positive, and the vector as
`feature:weight` pairs. -/
def toLines (c : Contexts) : Array String := Id.run do
  let mut out := #[]
  let line (a thm : Nat) (p : Bool) (v : CtxVec) : String :=
    s!"{a}\t{thm}\t{if p then 1 else 0}\t" ++ " ".intercalate (v.map fun (t, w) => s!"{t}:{w}").toList
  for a in [0:c.pos.size] do
    for (thm, v) in c.pos[a]! do out := out.push (line a thm true v)
  for a in [0:c.neg.size] do
    for (thm, v) in c.neg[a]! do out := out.push (line a thm false v)
  return out

/-- A float from its text, as `toString` writes it (a decimal with a fraction, possibly in
exponent form); 0 if it does not read. -/
def readFloat (s : String) : Float :=
  let (mant, ex) := match s.splitOn "e" with
    | [m, e] => (m, e.toInt?.getD 0)
    | _ => (s, 0)
  let (neg, mant) := if mant.startsWith "-" then (true, (mant.drop 1).toString) else (false, mant)
  let v := match mant.splitOn "." with
    | [w] => (w.toNat?.getD 0).toFloat
    | [w, f] => (w.toNat?.getD 0).toFloat + (f.toNat?.getD 0).toFloat / Float.pow 10 f.length.toFloat
    | _ => 0
  let v := v * Float.pow 10 (Float.ofInt ex)
  if neg then -v else v

/-- The contexts of `c` (its weights kept) with the records of `lines` (`toLines`). -/
def withLines (c : Contexts) (lines : Array String) (asserts : Nat) : Contexts := Id.run do
  let mut pos : Array (Array Context) := Array.replicate asserts #[]
  let mut neg : Array (Array Context) := Array.replicate asserts #[]
  for l in lines do
    let fields := l.splitOn "\t"
    let [a, thm, p, vec] := fields | continue
    let some a := a.toNat? | continue
    let some thm := thm.toNat? | continue
    if a ≥ asserts then continue
    let v : CtxVec := (vec.splitOn " ").filterMap (fun fw => match fw.splitOn ":" with
      | [f, w] => f.toNat?.map fun f => (f, readFloat w)
      | _ => none) |>.toArray
    if p == "1" then pos := pos.modify a (·.push (thm, v))
    else neg := neg.modify a (·.push (thm, v))
  -- by theorem, for the reader's limit
  pos := pos.map fun cs => cs.qsort fun x y => x.1 < y.1
  neg := neg.map fun cs => cs.qsort fun x y => x.1 < y.1
  return { c with pos, neg }

/-- How many positive and negative contexts there are, and of how many assertions. -/
def counts (c : Contexts) : Nat × Nat × Nat :=
  (c.pos.foldl (· + ·.size) 0, c.neg.foldl (· + ·.size) 0,
   (Array.range c.pos.size).foldl (init := 0) fun n a => if (c.pos[a]!).isEmpty then n else n + 1)

end Contexts

end Whitehead.Prove
