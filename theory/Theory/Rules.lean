/-
The conversion judgment as assertions (`docs/THEORY.md`, "Definitions", decision 10,
milestone 9): the language of a file extended by the judgment terms `≡_s` and `≡'_s`,
the rules `conv_s`, `refl_s`, `cong_t`, `cong'_t_i`, `unfold_f`, `unfold'_f`, `fold_f`,
`fold'_f` exactly as the production engine lays them out (`convRules` of
`Whitehead/Prove/Db.lean`), the database extended by them (`Database.withConv`), and
the translation of a proof over the extended database into an MM0 proof (`toD`),
with the certificate a rule tree stands for (`toC`). The engine runs over
`withConv` unchanged; the theorems about it are the first variant's.
-/
import Theory.Defs

namespace Theory

/-- The language of a file: its sorts and which are provable, its terms with their
signature, and the sort number of the judgment, which is none of the file's. The
judgment terms come after the file's terms. -/
structure Language where
  sorts : ℕ
  provable : ℕ → Bool
  terms : ℕ
  sig : Signature
  judg : ℕ

namespace Language

/-- The type of a judgment `a ≡ b`. -/
def judgTy (L : Language) : Ty := ⟨L.judg, false⟩

/-- The term `≡_s`, or `≡'_s` when `strict`. -/
def eqTerm (L : Language) (s : ℕ) (strict : Bool) : ℕ := L.terms + 2 * s + (if strict then 1 else 0)

/-- The judgment `a ≡_s b` (`strict`: `a ≡'_s b`). -/
def eq (L : Language) (s : ℕ) (strict : Bool) (a b : Exp) : Exp :=
  .app (L.eqTerm s strict) L.judgTy [a, b]

/-- Is `f` a judgment term? -/
def isEqTerm (L : Language) (f : ℕ) : Bool := L.terms ≤ f

/-- The signature with the judgment terms: each takes two expressions of its sort. -/
def sigConv (L : Language) : Signature where
  args f := if f < L.terms then L.sig.args f else [⟨(f - L.terms) / 2, false⟩, ⟨(f - L.terms) / 2, false⟩]
  sort f := if f < L.terms then L.sig.sort f else L.judg

end Language

/-- A rule of the judgment, by what it is for: `refl_s`; `conv_s`; `cong_t`, or
`cong'_t_i` with the strict judgment at argument `i`; `unfold_f` and `fold_f` for the
definition `d`, strict or not. -/
inductive RuleKind where
  | refl (s : ℕ)
  | conv (s : ℕ)
  | cong (t : ℕ) (strictAt : Option ℕ)
  | unfold (d : ℕ) (strict : Bool)
  | fold (d : ℕ) (strict : Bool)
  deriving DecidableEq, Repr, Inhabited

namespace Rules

/-- The variable `k` of a rule, of type `t`. -/
def v (k : ℕ) (t : Ty) : Exp := .var ⟨k, t⟩

/-- `refl_s: ⊢ a ≡ a`. -/
def reflRule (L : Language) (s : ℕ) : Assertion :=
  let t : Ty := ⟨s, false⟩
  { vars := [⟨0, t⟩], pairs := [], hyps := [], concl := L.eq s false (v 0 t) (v 0 t) }

/-- `conv_s: b, a ≡' b ⊢ a`. -/
def convRule (L : Language) (s : ℕ) : Assertion :=
  let t : Ty := ⟨s, false⟩
  { vars := [⟨0, t⟩, ⟨1, t⟩], pairs := [], hyps := [v 1 t, L.eq s true (v 0 t) (v 1 t)], concl := v 0 t }

/-- The variables of a congruence rule from the argument types, numbered from `k`: one
variable at an argument that takes names, two otherwise; with the left and the right
side of the arguments. -/
def congVars : List Ty → ℕ → List Var × List Exp × List Exp
  | [], _ => ([], [], [])
  | ty :: tys, k =>
    if ty.name then
      let p := congVars tys (k + 1)
      (⟨k, ty⟩ :: p.1, v k ty :: p.2.1, v k ty :: p.2.2)
    else
      let p := congVars tys (k + 2)
      (⟨k, ty⟩ :: ⟨k + 1, ty⟩ :: p.1, v k ty :: p.2.1, v (k + 1) ty :: p.2.2)

/-- The premises of a congruence rule: a judgment at every argument that does not take
names, strict at `strictAt`. -/
def congHyps (L : Language) (strictAt : Option ℕ) : List Ty → List Exp → List Exp → ℕ → List Exp
  | ty :: tys, a :: as, b :: bs, k =>
    (if ty.name then [] else [L.eq ty.sort (strictAt == some k) a b]) ++ congHyps L strictAt tys as bs (k + 1)
  | _, _, _, _ => []

/-- `cong_t: a_i ≡ b_i ⊢ t(as) ≡ t(bs)`, and `cong'_t_i` with `≡'` at argument `i` and in
the conclusion. -/
def congRule (L : Language) (t : ℕ) (strictAt : Option ℕ) : Assertion :=
  let tys := L.sig.args t
  let p := congVars tys 0
  let rs := L.sig.sort t
  { vars := p.1, pairs := [], hyps := congHyps L strictAt tys p.2.1 p.2.2 0,
    concl := L.eq rs strictAt.isSome (.app t ⟨rs, false⟩ p.2.1) (.app t ⟨rs, false⟩ p.2.2) }

/-- The regular argument positions of a term. -/
def regularArgs (tys : List Ty) : List ℕ :=
  (List.range tys.length).filter fun k => !(tys[k]!).name

/-- The variable for the other side of an unfolding or folding: above every binder of
the definition — the largest binder number plus one, and `0` when there is none —
which is the number of binders when they are numbered from zero, as the production
engine numbers them. -/
def other (D : Def) : Var :=
  ⟨match D.args ++ D.dummies with
    | [] => 0
    | l => l.foldl (fun m x => max m x.id) 0 + 1, ⟨D.ty.sort, false⟩⟩

/-- The pairs `(y, y')` of each dummy with every later one. -/
def laterPairs : List Var → List (Var × Var)
  | [] => []
  | y :: ys => ys.map (fun y' => (y, y')) ++ laterPairs ys

/-- The pairs of an unfolding: every dummy apart from every argument and from every
later dummy. -/
def defPairs (D : Def) : List (Var × Var) :=
  (D.dummies.flatMap fun y => D.args.map fun x => (y, x)) ++ laterPairs D.dummies

/-- `f(xs)` over the definition's own binders. -/
def defApp (D : Def) : Exp := .app D.term D.ty (D.args.map Exp.var)

/-- `unfold_f: B ≡ b ⊢ f(xs) ≡ b` (`strict`: `≡'` in the conclusion). -/
def unfoldRule (L : Language) (D : Def) (strict : Bool) : Assertion :=
  let o := other D
  { vars := D.args ++ D.dummies ++ [o], pairs := defPairs D,
    hyps := [L.eq D.ty.sort false D.value (.var o)], concl := L.eq D.ty.sort strict (defApp D) (.var o) }

/-- `fold_f: a ≡ B ⊢ a ≡ f(xs)`. -/
def foldRule (L : Language) (D : Def) (strict : Bool) : Assertion :=
  let o := other D
  { vars := D.args ++ D.dummies ++ [o], pairs := defPairs D,
    hyps := [L.eq D.ty.sort false (.var o) D.value], concl := L.eq D.ty.sort strict (.var o) (defApp D) }

/-- The rules of the sorts: `refl_s`, and `conv_s` where `s` is provable. -/
def sortRules (L : Language) : List (RuleKind × Assertion) :=
  (List.range L.sorts).flatMap fun s =>
    (.refl s, reflRule L s) :: (if L.provable s then [(.conv s, convRule L s)] else [])

/-- The rules of the terms: for a term with an argument that does not take names,
`cong_t` and a `cong'_t_i` per such argument. -/
def termRules (L : Language) : List (RuleKind × Assertion) :=
  (List.range L.terms).flatMap fun t =>
    let regular := regularArgs (L.sig.args t)
    if regular.isEmpty then []
    else (.cong t none, congRule L t none) :: regular.map fun i => (.cong t (some i), congRule L t (some i))

/-- The rules of the definitions, in the order of the production engine: `unfold_f`,
`fold_f`, `unfold'_f`, `fold'_f`. -/
def defRules (L : Language) (defs : List Def) : List (RuleKind × Assertion) :=
  defs.zipIdx.flatMap fun (D, d) =>
    [(.unfold d false, unfoldRule L D false), (.fold d false, foldRule L D false),
     (.unfold d true, unfoldRule L D true), (.fold d true, foldRule L D true)]

/-- All the rules, in the production engine's order. -/
def all (L : Language) (defs : List Def) : List (RuleKind × Assertion) :=
  sortRules L ++ termRules L ++ defRules L defs

end Rules

/-- The database extended by the rules of the judgment: the file's assertions, then the
rules; the definitions as they are. -/
def Database.withConv (L : Language) (db : Database) : Database :=
  { asserts := db.asserts ++ (Rules.all L db.defs).map (·.2), defs := db.defs }

/-- Which rule assertion `a` of the extended database is; `none` for an assertion of
the file. -/
def Database.ruleAt (L : Language) (db : Database) (a : ℕ) : Option RuleKind :=
  if a < db.asserts.length then none else ((Rules.all L db.defs)[a - db.asserts.length]?).map (·.1)

/-! ### The translation to MM0 proofs -/

namespace Translate

/-- The certificates of a congruence from those of its regular arguments: at an
argument that takes names, reflexivity of the one variable's value. The variables are
numbered as `congVars` numbers them. -/
def congCerts (θ : Subst) : List Ty → List CTree → ℕ → List CTree
  | [], _, _ => []
  | ty :: tys, ks, k =>
    if ty.name then CTree.refl (θ.f ⟨k, ty⟩) :: congCerts θ tys ks (k + 1)
    else
      match ks with
      | k' :: ks' => k' :: congCerts θ tys ks' (k + 2)
      | [] => CTree.refl (θ.f ⟨k, ty⟩) :: congCerts θ tys [] (k + 2)

/-- The unfolding certificate of a step of `unfold_f` or `fold_f`: the arguments and
the dummies under the step's substitution. -/
def unfoldCert (d : ℕ) (D : Def) (θ : Subst) : CTree :=
  .unfold d (D.args.map fun x => θ.f x) (D.dummies.map fun y => θ.f y)

end Translate

open Translate in
mutual
/-- The certificate a rule tree stands for: `refl_s` is `CRefl`; `cong_t` is `CCong`
with reflexivity at the arguments that take names; `unfold_f` is the unfolding and
then the child's certificate; `fold_f` the child's and then the unfolding backwards.
Anything else — which a valid rule tree has not — is reflexivity of its expression. -/
def PTree.toC (L : Language) (db : Database) : PTree → CTree
  | .hyp _ e => .refl e
  | .step e a θ cs =>
    match db.ruleAt L a with
    | some (.refl s) => .refl (θ.f ⟨0, ⟨s, false⟩⟩)
    | some (.cong t _) => .cong t ⟨L.sig.sort t, false⟩ (congCerts θ (L.sig.args t) (PTree.toCList L db cs) 0)
    | some (.unfold d _) =>
      match db.defs[d]? with
      | some D => .trans (unfoldCert d D θ) ((PTree.toCList L db cs).headD (.refl e))
      | none => .refl e
    | some (.fold d _) =>
      match db.defs[d]? with
      | some D => .trans ((PTree.toCList L db cs).headD (.refl e)) (.symm (unfoldCert d D θ))
      | none => .refl e
    | _ => .refl e
def PTree.toCList (L : Language) (db : Database) : List PTree → List CTree
  | [] => []
  | t :: ts => PTree.toC L db t :: PTree.toCList L db ts
end

mutual
/-- The MM0 proof a tree over the extended database stands for: a step of the file as
it is; a `conv_s` step as `VConv` of the certificate its second child stands for,
backwards, over the proof its first child stands for. Anything else — which a valid
proof has not at this level — is a leaf. -/
def PTree.toD (L : Language) (db : Database) : PTree → DTree
  | .hyp h e => .hyp h e
  | .step e a θ cs =>
    match db.ruleAt L a with
    | none => .step e a θ (PTree.toDList L db cs)
    | some (.conv _) =>
      .conv e (.symm ((PTree.toCList L db cs)[1]?.getD (.refl e)))
        ((PTree.toDList L db cs)[0]?.getD (.hyp 0 e))
    | some _ => .hyp 0 e
def PTree.toDList (L : Language) (db : Database) : List PTree → List DTree
  | [] => []
  | t :: ts => PTree.toD L db t :: PTree.toDList L db ts
end

end Theory
