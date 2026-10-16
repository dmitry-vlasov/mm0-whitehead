/-
Elaboration of a `.mm0` specification: from the statements of the primary parser to an
`Env`, the sorts, terms and statements with their formulas parsed.

Statements are elaborated in order, each against the declarations and notations before
it, as the formal specification does (`Elaborate` in `examples/mm0.mm0`). What is checked
here is what is needed to give every formula a meaning: names, the shape of binders,
arities, sorts and coercions, and the validity of notation declarations. The conditions
on a well-formed environment (`strict`, `pure`, `free`, the free variables of a
definition) are not checked here; they belong to the verifier.
-/
import Std.Data.HashSet
import Whitehead.Mm0.Math
import Whitehead.Mm0.Parser
import Whitehead.Mm0.Load

namespace Whitehead.Mm0

/-- The elaborator's state: the environment so far, and how to find things in it. -/
structure ElabState where
  env : Env := {}
  math : MathEnv := {}
  sortIds : Std.HashMap String Nat := {}
  termIds : Std.HashMap String Nat := {}
  thmNames : Std.HashSet String := {}
  deriving Inhabited

namespace ElabState

/-! The functions that add a declaration take the state apart and build a new one, so
that the arrays are not shared when they are pushed to: a `{ st with ... }` that reads
`st.env.thms` would copy the array every time. -/

def pushSort (st : ElabState) (d : SortDecl) : ElabState :=
  let { env, math, sortIds, termIds, thmNames } := st
  let { sorts, terms, thms, order } := env
  let id := sorts.size
  { env := { sorts := sorts.push d, terms, thms, order := order.push (.sort id) },
    math, sortIds := sortIds.insert d.name id, termIds, thmNames }

def pushTerm (st : ElabState) (d : TermDecl) : ElabState :=
  let { env, math, sortIds, termIds, thmNames } := st
  let { sorts, terms, thms, order } := env
  let id := terms.size
  let name := d.name
  { env := { sorts, terms := terms.push d, thms, order := order.push (.term id) },
    math, sortIds, termIds := termIds.insert name id, thmNames }

def pushThm (st : ElabState) (d : ThmDecl) : ElabState :=
  let { env, math, sortIds, termIds, thmNames } := st
  let { sorts, terms, thms, order } := env
  let id := thms.size
  let name := d.name
  { env := { sorts, terms, thms := thms.push d, order := order.push (.thm id) },
    math, sortIds, termIds, thmNames := thmNames.insert name }

def setMath (st : ElabState) (math : MathEnv) : ElabState :=
  let { env, math := _, sortIds, termIds, thmNames } := st
  { env, math, sortIds, termIds, thmNames }

end ElabState

namespace Elab

def fail {α : Type} (pos : Nat) (msg : String) : Except ParseError α :=
  .error ⟨pos, msg⟩

/-- Turns the message of a `MathEnv` operation into an error at `pos`. -/
def atPos {α : Type} (pos : Nat) (r : Except String α) : Except ParseError α :=
  match r with
  | .ok a => .ok a
  | .error msg => .error ⟨pos, msg⟩

/-- The variables and hypotheses of the declaration being elaborated. -/
structure Locals where
  /-- The arguments, in order: named, anonymous, and those that arrows stand for. -/
  vars : Array VarDecl := #[]
  dummies : Array VarDecl := #[]
  hyps : Array (Option String × MathString) := #[]

def lookupSort (st : ElabState) (id : Ident) : Except ParseError Nat :=
  match st.sortIds[id.name]? with
  | some s => .ok s
  | none => fail id.span.start s!"unknown sort `{id.name}`"

def lookupTerm (st : ElabState) (id : Ident) : Except ParseError Nat :=
  match st.termIds[id.name]? with
  | some t => .ok t
  | none => fail id.span.start s!"unknown term `{id.name}`"

/-- The sort of a type and the variables it depends on. A dependency must be a bound
variable of an earlier binder. -/
def resolveType (st : ElabState) (loc : Locals) (t : DepType) : Except ParseError (Nat × Array Nat) := do
  let sort ← lookupSort st t.sort
  let mut deps := #[]
  for d in t.deps do
    match loc.vars.findIdx? (·.name == some d.name) with
    | none => fail d.span.start s!"unknown variable `{d.name}`"
    | some i =>
      if !loc.vars[i]!.bound then
        fail d.span.start s!"`{d.name}` is not a bound variable; only bound variables can be depended on"
      deps := deps.push i
  return (sort, deps)

def isDeclared (loc : Locals) (name : String) : Bool :=
  loc.vars.any (·.name == some name) || loc.dummies.any (·.name == some name)

/-- One binder group. Variables come before hypotheses. -/
def addBinder (st : ElabState) (loc : Locals) (b : Binder) : Except ParseError Locals := do
  match b.type with
  | .formula f =>
    return { loc with hyps := b.names.foldl (fun hs n => hs.push (n.name, f)) loc.hyps }
  | .type t =>
    if !loc.hyps.isEmpty then
      fail b.span.start "a variable binder cannot come after a hypothesis"
    let (sort, deps) ← resolveType st loc t
    if b.curly && !deps.isEmpty then
      fail t.deps[0]!.span.start "a bound variable cannot have dependencies"
    let mut loc := loc
    for n in b.names do
      if let some name := n.name then
        if isDeclared loc name then
          fail n.span.start s!"variable `{name}` is declared twice"
      if n.dummy then
        if !deps.isEmpty then
          fail t.deps[0]!.span.start "a dummy variable cannot have dependencies"
        loc := { loc with dummies := loc.dummies.push ⟨n.name, sort, true, #[]⟩ }
      else
        loc := { loc with vars := loc.vars.push ⟨n.name, sort, b.curly, deps⟩ }
    return loc

/-- An argument given as a type before an arrow: an anonymous regular variable. -/
def addArrowVar (st : ElabState) (loc : Locals) (t : DepType) : Except ParseError Locals := do
  if !loc.hyps.isEmpty then
    fail t.sort.span.start "a variable cannot come after a hypothesis"
  let (sort, deps) ← resolveType st loc t
  return { loc with vars := loc.vars.push ⟨none, sort, false, deps⟩ }

def mathCtx (st : ElabState) (vars : Array VarDecl) : MathCtx :=
  { env := st.math, sorts := st.env.sorts, terms := st.env.terms, termIds := st.termIds,
    vars, tokens := #[], endPos := 0 }

/-- The single token of a notation constant such as `$ -> $`. -/
def constToken (m : MathString) : Except ParseError String := do
  let tokens := ({} : MathEnv).tokens m.text
  if tokens.size != 1 then
    fail m.span.start "a notation constant must be exactly one token"
  let token := tokens[0]!
  if token == "(" || token == ")" then
    fail m.span.start "parentheses cannot be notation tokens: they are reserved for grouping"
  return token

/-- The delimiter characters named in a math string: single characters separated by
whitespace. -/
def delimiterBytes (m : MathString) : Except ParseError ByteArray := do
  let mut out := ByteArray.empty
  for t in ({} : MathEnv).tokenize m.text.toUTF8 (m.span.start + 1) do
    let b := t.text.toUTF8
    if b.size != 1 then
      fail t.pos s!"a delimiter must be one character, `{t.text}` is not"
    out := out.push (b.get! 0)
  return out

def checkNewTerm (st : ElabState) (name : Ident) : Except ParseError Unit :=
  if st.termIds.contains name.name then
    fail name.span.start s!"term `{name.name}` is already declared"
  else .ok ()

def elabStmt (st : ElabState) (stmt : Stmt) : Except ParseError ElabState := do
  match stmt.kind with
  | .sort mods name =>
    if st.sortIds.contains name.name then
      fail name.span.start s!"sort `{name.name}` is already declared"
    return st.pushSort ⟨name.name, mods⟩
  | .term name binders args ret =>
    checkNewTerm st name
    let loc ← binders.foldlM (addBinder st) {}
    let loc ← args.foldlM (addArrowVar st) loc
    let (retSort, retDeps) ← resolveType st loc ret
    return st.pushTerm { name := name.name, args := loc.vars, retSort, retDeps, isDef := false, value := none }
  | .defn name binders args ret value =>
    checkNewTerm st name
    let loc ← binders.foldlM (addBinder st) {}
    let loc ← args.foldlM (addArrowVar st) loc
    let (retSort, retDeps) ← resolveType st loc ret
    let value ←
      match value with
      | none =>
        if !loc.dummies.isEmpty then
          fail name.span.start "a def without a value cannot have dummy variables"
        pure none
      | some m =>
        let expr ← parseMath (mathCtx st (loc.vars ++ loc.dummies)) m (.sort retSort)
        pure (some { dummies := loc.dummies, expr : DefValue })
    return st.pushTerm { name := name.name, args := loc.vars, retSort, retDeps, isDef := true, value }
  | .assert kind name binders arrows concl =>
    if st.thmNames.contains name.name then
      fail name.span.start s!"axiom or theorem `{name.name}` is already declared"
    let loc ← binders.foldlM (addBinder st) {}
    let loc ← arrows.foldlM (init := loc) fun loc a =>
      match a with
      | .type t => addArrowVar st loc t
      | .formula f => pure { loc with hyps := loc.hyps.push (none, f) }
    let ctx := mathCtx st loc.vars
    let hyps ← loc.hyps.mapM fun (hypName, f) => do
      return { name := hypName, expr := ← parseMath ctx f .provable : HypDecl }
    let concl ← parseMath ctx concl .provable
    return st.pushThm { name := name.name, isAxiom := kind == .ax, args := loc.vars, hyps, concl }
  | .delimiter left right =>
    let l ← delimiterBytes left
    let r ← match right with
      | some m => delimiterBytes m
      | none => pure l
    return st.setMath (st.math.addDelimiters l r)
  | .simpleNota kind term const prec =>
    let t ← lookupTerm st term
    let token ← constToken const
    let arity := st.env.terms[t]!.args.size
    match kind with
    | .pfx =>
      -- all arguments at max, the last at the precedence of the notation
      let lits := (Array.range arity).map fun i =>
        Literal.var i (if i + 1 == arity then prec else .max)
      let math ← atPos const.span.start (st.math.addConst token prec)
      let math ← atPos const.span.start (math.addPrefix token { term := t, lits })
      return st.setMath math
    | .infl | .infr =>
      if arity != 2 then
        fail term.span.start s!"an infix notation needs a term with two arguments; `{term.name}` has {arity}"
      if prec == .max then
        fail term.span.start "an infix notation cannot have precedence max"
      let math ← atPos const.span.start (st.math.addConst token prec)
      let math ← atPos const.span.start (math.addInfix token { term := t, rassoc := kind == .infr })
      return st.setMath math
  | .coercion term src tgt =>
    let t ← lookupTerm st term
    let s1 ← lookupSort st src
    let s2 ← lookupSort st tgt
    let decl := st.env.terms[t]!
    if decl.args.size != 1 then
      fail term.span.start s!"a coercion needs a term with one argument; `{term.name}` has {decl.args.size}"
    let sortName (s : Nat) : String := (st.env.sorts[s]?.map (·.name)).getD s!"s{s}"
    if decl.args[0]!.sort != s1 || decl.retSort != s2 then
      fail term.span.start s!"`{term.name}` goes from sort `{sortName decl.args[0]!.sort}` to sort `{sortName decl.retSort}`, not from `{src.name}` to `{tgt.name}`"
    let provable (s : Nat) : Bool := (st.env.sorts[s]?.map (·.mods.isProvable)).getD false
    let math ← atPos term.span.start (st.math.addCoe provable sortName s1 s2 t)
    return st.setMath math
  | .genNota term binders _ head lits =>
    let t ← lookupTerm st term
    -- the variables of the notation, by position
    let mut names : Array String := #[]
    for b in binders do
      for n in b.names do
        match n.name with
        | some name => names := names.push name
        | none => fail n.span.start "a variable of a notation needs a name: it has to be used in the notation"
    let arity := st.env.terms[t]!.args.size
    if names.size != arity then
      fail term.span.start s!"`{term.name}` has {arity} arguments, but the notation declares {names.size} variables"
    let token ← constToken head.const
    let mut math ← atPos head.const.span.start (st.math.addConst token head.prec)
    let mut out : Array Literal := #[]
    let mut used := Array.replicate arity false
    for i in [0:lits.size] do
      match lits[i]! with
      | .const c =>
        let tk ← constToken c.const
        math ← atPos c.const.span.start (math.addConst tk c.prec)
        out := out.push (.const tk)
      | .var x =>
        let some idx := names.findIdx? (· == x.name)
          | fail x.span.start s!"unknown variable `{x.name}` in the notation"
        if used[idx]! then
          fail x.span.start s!"variable `{x.name}` is used twice in the notation"
        used := used.set! idx true
        -- the precedence of a variable: one above the constant that follows it, max
        -- before another variable, and that of the notation at the end
        let prec ←
          match lits[i + 1]? with
          | none => pure head.prec
          | some (.var _) => pure Prec.max
          | some (.const c) =>
            match c.prec with
            | .num q => pure (Prec.num (q + 1))
            | .max =>
              fail c.const.span.start "a constant that follows a variable cannot have precedence max"
        out := out.push (.var idx prec)
    for i in [0:arity] do
      if !used[i]! then
        fail term.span.start s!"variable `{names[i]!}` is not used in the notation"
    math ← atPos head.const.span.start (math.addPrefix token { term := t, lits := out })
    return st.setMath math
  | .inout _ _ args =>
    -- the formulas must parse; what they mean is up to the input or output kind
    let ctx := mathCtx st #[]
    for a in args do
      if let .math m := a then
        discard <| parseMath ctx m .any
    return st
  | .importFile _ _ =>
    fail stmt.span.start "an `import` cannot be resolved here: load the specification from its file"

end Elab

/-- Elaborates the statements of one source text. It must not contain `import`. -/
def elabString (src : String) : Except ParseError Env := do
  let stmts ← parseString src
  let st ← stmts.foldlM Elab.elabStmt {}
  return st.env

/-- Elaborates a loaded specification, keeping the state: the notations and the names,
with which more formulas can be read (`Prove/Pattern.lean`). An error is reported in the
file it occurs in. -/
def elaborateState (spec : Spec) : Except LoadError ElabState := do
  let mut st : ElabState := {}
  for s in spec.stmts do
    match Elab.elabStmt st s.stmt with
    | .ok st' => st := st'
    | .error e => throw (.parse spec.sources[s.file]! e)
  return st

/-- Elaborates a loaded specification. An error is reported in the file it occurs in. -/
def elaborate (spec : Spec) : Except LoadError Env :=
  return (← elaborateState spec).env

end Whitehead.Mm0
