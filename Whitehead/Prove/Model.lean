/-
A model of the learned ranking layer, as `learn/train.py` writes it (`docs/DESIGN.md`,
"The learned ranking layer"): a score for a variant, from its features (`Env.features`).

- **Linear:** `{"features", "mean", "scale", "weights"}`, the score Σ wᵢ (xᵢ − μᵢ) / σᵢ.
- **Trees:** LightGBM's `dump_model()`, the score the sum of its trees' leaves. A node
  sends `x` left when `x ≤ threshold`; a value that LightGBM takes as missing (a zero,
  for `missing_type` `Zero`) goes the node's default way.

The model names the features it was trained on, and they must be `featureNames`, in
that order: a model of other features is refused when it is read.
-/
import Whitehead.Json
import Whitehead.Prove.Features

namespace Whitehead.Prove

/-- A number of JSON, written as text: an optional sign, digits, a decimal part, an
exponent. -/
def parseFloat (s : String) : Option Float := Id.run do
  let cs := s.trimAscii.toString.toList.toArray
  let mut i := 0
  let mut neg := false
  if cs[i]? == some '-' then
    neg := true
    i := i + 1
  else if cs[i]? == some '+' then i := i + 1
  let mut mant : Nat := 0
  let mut exp : Int := 0
  let mut digits := 0
  while i < cs.size && cs[i]!.isDigit do
    mant := mant * 10 + (cs[i]!.toNat - '0'.toNat)
    digits := digits + 1
    i := i + 1
  if cs[i]? == some '.' then
    i := i + 1
    while i < cs.size && cs[i]!.isDigit do
      mant := mant * 10 + (cs[i]!.toNat - '0'.toNat)
      exp := exp - 1
      digits := digits + 1
      i := i + 1
  if digits == 0 then return none
  if cs[i]? == some 'e' || cs[i]? == some 'E' then
    i := i + 1
    let mut eneg := false
    if cs[i]? == some '-' then
      eneg := true
      i := i + 1
    else if cs[i]? == some '+' then i := i + 1
    let mut e : Nat := 0
    let mut ed := 0
    while i < cs.size && cs[i]!.isDigit do
      e := e * 10 + (cs[i]!.toNat - '0'.toNat)
      ed := ed + 1
      i := i + 1
    if ed == 0 then return none
    exp := exp + (if eneg then -(e : Int) else e)
  if i != cs.size then return none
  let m := mant.toFloat
  let v := if exp ≥ 0 then m * Float.pow 10 exp.toNat.toFloat else m / Float.pow 10 (-exp).toNat.toFloat
  return some (if neg then -v else v)

/-- A JSON number as a float. -/
def jsonFloat? : Json → Option Float
  | .int n => some (if n < 0 then -((-n).toNat.toFloat) else n.toNat.toFloat)
  | .float t => parseFloat t
  | _ => none

/-- A tree, flattened: node `i` tests feature `feature[i]` against `threshold[i]`; a child
`c ≥ 0` is a node, `c < 0` the leaf `-c - 1`. The numbers are unboxed (`FloatArray`): a
tree is walked a hundred times for each variant of each new goal. -/
structure Tree where
  feature : Array Nat := #[]
  threshold : FloatArray := .empty
  defaultLeft : Array Bool := #[]
  missingZero : Array Bool := #[]
  left : Array Int := #[]
  right : Array Int := #[]
  leaves : FloatArray := .empty
  deriving Inhabited

instance : Repr Tree := ⟨fun t _ => s!"<a tree of {t.feature.size} nodes>"⟩

/-- The value of tree `t` at `x`. -/
def Tree.eval (t : Tree) (x : FloatArray) : Float := Id.run do
  if t.feature.isEmpty then return t.leaves.get! 0
  let mut i : Int := 0
  for _ in [0:t.feature.size + 1] do
    if i < 0 then break
    let k := i.toNat
    let v := x.get! t.feature[k]!
    let goLeft := if t.missingZero[k]! && v.abs ≤ 1e-35 then t.defaultLeft[k]! else v ≤ t.threshold.get! k
    i := if goLeft then t.left[k]! else t.right[k]!
  return t.leaves.get! (-i - 1).toNat

inductive Model where
  | linear (mean scale weights : Array Float)
  | trees (ts : Array Tree)
  deriving Inhabited, Repr

/-- The score of a variant with features `x`. -/
def Model.score (m : Model) (x : Array Float) : Float :=
  match m with
  | .linear mean scale weights => Id.run do
    let mut s := 0
    for i in [0:weights.size] do
      s := s + weights[i]! * ((x[i]?.getD 0) - mean[i]!) / scale[i]!
    return s
  | .trees ts =>
    let xs : FloatArray := ⟨x⟩
    ts.foldl (init := 0) fun s t => s + t.eval xs

/-- A tree of LightGBM's dump, added to `t`; returns the child reference of the node. -/
partial def addNode (j : Json) (t : Tree) : Except String (Int × Tree) := do
  if let some v := j.get? "leaf_value" then
    let some f := jsonFloat? v | throw "a leaf value is not a number"
    return (-(t.leaves.size : Int) - 1, { t with leaves := t.leaves.push f })
  let some (.int fi) := j.get? "split_feature" | throw "a node has no split_feature"
  let some th := (j.get? "threshold").bind jsonFloat? | throw "a node has no threshold"
  let some (.str dt) := j.get? "decision_type" | throw "a node has no decision_type"
  if dt != "<=" then throw s!"a decision of type {dt}: only <= is read"
  let dl := match j.get? "default_left" with | some (.bool b) => b | _ => true
  let mz := match j.get? "missing_type" with | some (.str "Zero") => true | _ => false
  let some l := j.get? "left_child" | throw "a node has no left child"
  let some r := j.get? "right_child" | throw "a node has no right child"
  let k := t.feature.size
  let t := { t with feature := t.feature.push fi.toNat, threshold := t.threshold.push th,
                    defaultLeft := t.defaultLeft.push dl, missingZero := t.missingZero.push mz,
                    left := t.left.push 0, right := t.right.push 0 }
  let (lc, t) ← addNode l t
  let (rc, t) ← addNode r t
  return (k, { t with left := t.left.set! k lc, right := t.right.set! k rc })

/-- The features a model names must be `featureNames`. -/
def checkFeatures (names : Array Json) : Except String Unit := do
  let ns := names.filterMap fun n => match n with | .str s => some s | _ => none
  if ns != featureNames then
    throw s!"the model's features are not those of this program: {ns.size} against {featureNames.size}"

/-- A model from its JSON. -/
def Model.ofJson (j : Json) : Except String Model := do
  if let some (.arr treeInfo) := j.get? "tree_info" then
    let some (.arr names) := j.get? "feature_names" | throw "the trees name no features"
    checkFeatures names
    let ts ← treeInfo.mapM fun t => do
      let some s := t.get? "tree_structure" | throw "a tree has no structure"
      return (← addNode s {}).2
    return .trees ts
  let some (.arr names) := j.get? "features" | throw "the model names no features"
  checkFeatures names
  let floats (key : String) : Except String (Array Float) := do
    let some (.arr xs) := j.get? key | throw s!"the model has no {key}"
    xs.mapM fun x => match jsonFloat? x with
      | some f => pure f
      | none => throw s!"{key}: not a number"
  return .linear (← floats "mean") (← floats "scale") (← floats "weights")

/-- A model from a file. -/
def Model.load (path : System.FilePath) : IO (Except String Model) := do
  match Json.parse (← IO.FS.readFile path) with
  | .error e => return .error s!"{path}: {e.msg}"
  | .ok j => return (Model.ofJson j).mapError fun e => s!"{path}: {e}"

end Whitehead.Prove
