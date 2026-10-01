/-
`dump`: a decoded `.mmb` file as text, for reading and for diffing.

Every statement is printed as the `.mm0` declaration it stands for, with its formulas as
s-expressions (which is valid MM0 math syntax: `$ imp a (al x ph) $`), followed, if it
has a proof body, by its proof commands, one per line with the file offset. Names come
from the index; where there is none they are generated (`t5`, `v0`, ...).

The output is written line by line through a callback, so that a large file is never
held as one string.
-/
import Whitehead.Mmb.Reader

namespace Whitehead.Mmb

namespace Dump

abbrev DumpM := ExceptT MmbError IO

/-- The binders of a declaration in `.mm0` style, consecutive binders of the same type
grouped: ` {x y: set} (ph: wff x)`. Each group is preceded by a space. -/
def binders (f : MmbFile) (args : Array Arg) (names : Array String) : String := Id.run do
  -- the names of the bound variables, in order: bit `j` of `deps` is the `j`-th of them
  let mut boundNames : Array String := #[]
  for i in [0:args.size] do
    if args[i]!.bound then boundNames := boundNames.push (names[i]?.getD s!"v{i}")
  let typeOf (a : Arg) : String := Id.run do
    let mut s := f.sortName a.sort
    if !a.bound then
      for j in [0:55] do
        if (a.deps >>> j.toUInt64) &&& 1 != 0 then
          s := s ++ " " ++ boundNames[j]?.getD s!"?{j}"
    return s
  let mut out := ""
  let mut i := 0
  while i < args.size do
    let a := args[i]!
    let mut group := names[i]?.getD s!"v{i}"
    let mut k := i + 1
    while k < args.size && args[k]!.raw == a.raw && !a.bound do
      group := group ++ " " ++ names[k]?.getD s!"v{k}"
      k := k + 1
    -- bound variables differ in their own bit, so compare them by sort
    while a.bound && k < args.size && args[k]!.bound && args[k]!.sort == a.sort do
      group := group ++ " " ++ names[k]?.getD s!"v{k}"
      k := k + 1
    out := out ++ (if a.bound then " {" else " (") ++ group ++ ": " ++ typeOf a ++
      (if a.bound then "}" else ")")
    i := k
  return out

/-- A return type: the sort and the bound variables it depends on. -/
def retType (f : MmbFile) (args : Array Arg) (names : Array String) (ret : Arg) : String := Id.run do
  let mut s := f.sortName ret.sort
  let mut j := 0
  for i in [0:args.size] do
    if args[i]!.bound then
      if (ret.deps >>> j.toUInt64) &&& 1 != 0 then
        s := s ++ " " ++ names[i]?.getD s!"v{i}"
      j := j + 1
  return s

/-- A pattern as an s-expression. `heap` holds the text of every heap entry known so far
(the arguments, then saved terms and dummies in stream order) and is extended on the
way. `dummyNames` are the names for the dummies, in order; `nextDummy` counts them. -/
partial def pattern (f : MmbFile) (dummyNames : Array String) (top : Bool) (p : Pattern)
    (heap : Array String) (nextDummy : Nat) : String × Array String × Nat :=
  match p with
  | .ref i => (heap[i]?.getD s!"?{i}", heap, nextDummy)
  | .dummy _ _ =>
    let name := dummyNames[nextDummy]?.getD s!"d{nextDummy}"
    (name, heap.push name, nextDummy + 1)
  | .app t save args => Id.run do
    -- reserve the slot of a saved term before its arguments, as the stream does
    let slot := heap.size
    let mut heap := if save.isSome then heap.push "" else heap
    let mut nextDummy := nextDummy
    let mut inner := f.termName t
    for a in args do
      let (s, h, d) := pattern f dummyNames false a heap nextDummy
      inner := inner ++ " " ++ s
      heap := h
      nextDummy := d
    let nested := if args.isEmpty then inner else "(" ++ inner ++ ")"
    if save.isSome then heap := heap.set! slot nested
    return (if top then inner else nested, heap, nextDummy)

/-- The conclusion and the hypotheses of a statement as text, the hypotheses in
declaration order. Heap entries are assigned in stream order, which is the conclusion
first and then the hypotheses from the last to the first. -/
def statementText (f : MmbFile) (argNames dummyNames : Array String) (s : Statement) :
    String × Array String := Id.run do
  let (concl, heap, d) := pattern f dummyNames true s.concl argNames 0
  let mut heap := heap
  let mut d := d
  let mut hyps := #[]
  for h in s.hyps.reverse do
    let (text, heap', d') := pattern f dummyNames true h heap d
    hyps := hyps.push text
    heap := heap'
    d := d'
  return (concl, hyps.reverse)

def sortMods (s : SortData) : String :=
  (if s.isPure then "pure " else "") ++ (if s.isStrict then "strict " else "") ++
  (if s.isProvable then "provable " else "") ++ (if s.isFree then "free " else "")

/-- The proof commands of `stmt`, one per line. `labels` names the heap entries that are
variables (the arguments); `dummyNames` and `hypNames` name what `Dummy` and `Hyp`
add to the heap. -/
partial def proofLines (f : MmbFile) (stmt : Stmt) (argNames dummyNames hypNames : Array String)
    (emit : String → IO Unit) : DumpM Unit := do
  let b := f.bytes
  let mut labels : Array (Option String) := argNames.map some
  let mut pos := stmt.bodyStart
  let mut dummies := 0
  let mut hyps := 0
  -- the commands were validated when the body was decoded; here they are walked again
  -- to have their offsets
  let cmds ← (f.proofCmds stmt : Except MmbError _)
  for cmd in cmds do
    let (_, _, next) ← (Reader.readCmd b pos : Except MmbError _)
    let saved := s!"  -- heap[{labels.size}]"
    let line ←
      match cmd with
      | .term t save =>
        if save then
          labels := labels.push none
          pure s!"TermSave {f.termName t}{saved}"
        else pure s!"Term {f.termName t}"
      | .ref i =>
        pure <| match labels[i]?.join with
          | some name => s!"Ref {i}  -- {name}"
          | none => s!"Ref {i}"
      | .dummy s =>
        let name := dummyNames[dummies]?.getD s!"d{dummies}"
        dummies := dummies + 1
        labels := labels.push (some name)
        pure s!"Dummy {f.sortName s}{saved}: {name}"
      | .thm t save =>
        if save then
          labels := labels.push none
          pure s!"ThmSave {f.thmName t}{saved}"
        else pure s!"Thm {f.thmName t}"
      | .hyp =>
        let name := hypNames[hyps]?.getD s!"h{hyps}"
        hyps := hyps + 1
        labels := labels.push (some name)
        pure s!"Hyp{saved}: {name}"
      | .conv => pure "Conv"
      | .refl => pure "Refl"
      | .symm => pure "Symm"
      | .cong => pure "Cong"
      | .unfold => pure "Unfold"
      | .convCut => pure "ConvCut"
      | .convSave =>
        labels := labels.push none
        pure s!"ConvSave{saved}"
      | .save =>
        labels := labels.push none
        pure s!"Save{saved}"
      | .sorry => pure "Sorry"
    emit s!"  0x{hex pos}: {line}"
    pos := next

/-- Notes on things a verifier may object to but that do not stop decoding. -/
def argNotes (what : String) (args : Array Arg) (emit : String → IO Unit) : DumpM Unit := do
  for i in [0:args.size] do
    if args[i]!.reservedBit then
      emit s!"-- note: the reserved bit 55 is set in binder {i} of {what}"

def dumpStmt (f : MmbFile) (stmt : Stmt) (emit : String → IO Unit) : DumpM Unit := do
  match stmt.kind with
  | .sort =>
    emit s!"{sortMods f.sorts[stmt.index]!}sort {f.sortName stmt.index};"
  | .termDef isLocal =>
    let i := stmt.index
    let t := f.terms[i]!
    let args := f.termArgs i
    let ret := f.termRet i
    argNotes s!"term {f.termName i}" (args.push ret) emit
    if t.reserved != 0 then
      emit s!"-- note: the reserved byte of term-table entry {i} is 0x{hex t.reserved}"
    if ret.sort != t.sort then
      emit s!"-- note: the term table gives sort {t.sort} for {f.termName i}, its return type sort {ret.sort}"
    let loc := if isLocal then "local " else ""
    if t.isDef then
      let value ← (f.termValue i : Except MmbError _)
      let names := MmbFile.fillNames (f.names.termVars[i]?.getD #[]) (t.numArgs + value.dummies.size) "v"
      let argNames := names.extract 0 t.numArgs
      let dummyNames := names.extract t.numArgs names.size
      let (text, _) := statementText f argNames dummyNames value
      let mut dummies := ""
      for k in [0:value.dummies.size] do
        dummies := dummies ++ " {." ++ dummyNames[k]! ++ ": " ++ f.sortName value.dummies[k]! ++ "}"
      emit s!"{loc}def {f.termName i}{binders f args argNames}{dummies}: {retType f args argNames ret} = $ {text} $;"
      proofLines f stmt argNames dummyNames #[] emit
    else
      let argNames := (f.termVarNames i).extract 0 t.numArgs
      emit s!"{loc}term {f.termName i}{binders f args argNames}: {retType f args argNames ret};"
  | .ax | .thm _ =>
    let i := stmt.index
    let t := f.thms[i]!
    let args := f.thmArgs i
    argNotes s!"theorem {f.thmName i}" args emit
    if t.reserved != 0 then
      emit s!"-- note: the reserved field of theorem-table entry {i} is 0x{hex t.reserved}"
    let st ← (f.thmStatement i : Except MmbError _)
    let names := f.thmVarNames i
    let argNames := names.extract 0 t.numArgs
    let dummyNames := names.extract t.numArgs names.size
    let hypNames := MmbFile.fillNames (f.names.thmHyps[i]?.getD #[]) st.hyps.size "h"
    let (concl, hyps) := statementText f argNames #[] st
    let mut hypBinders := ""
    for k in [0:hyps.size] do
      hypBinders := hypBinders ++ " (" ++ hypNames[k]! ++ ": $ " ++ hyps[k]! ++ " $)"
    let kw := match stmt.kind with
      | .ax => "axiom"
      | .thm true => "local theorem"
      | _ => "theorem"
    emit s!"{kw} {f.thmName i}{binders f args argNames}{hypBinders}: $ {concl} $;"
    proofLines f stmt argNames dummyNames hypNames emit

end Dump

/-- Writes the whole file as text, one line per call of `emit`. -/
def dump (f : MmbFile) (emit : String → IO Unit) : ExceptT MmbError IO Unit := do
  let h := f.header
  emit s!"-- MMB version 1: {h.numSorts} sorts, {h.numTerms} terms, {h.numThms} theorems"
  if f.indexEntries.isEmpty then
    emit "-- no index: names are generated"
  else
    emit s!"-- index: {" ".intercalate (f.indexEntries.toList.map (·.type))}"
  if h.reserved != 0 || h.reserved2 != 0 then
    emit s!"-- note: the reserved header fields are 0x{hex h.reserved} and 0x{hex h.reserved2}"
  emit ""
  for stmt in f.stmts do
    Dump.dumpStmt f stmt emit

end Whitehead.Mmb
