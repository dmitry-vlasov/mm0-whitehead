/-
A port of `mm0-lean/mm0/mm0.lean` of the MM0 repository (Lean 3, mathlib of 2020) to
Lean 4, line for line: the formal semantics of MM0 environments and proofs, the Lean
form of `examples/mm0.mm0`. The names are the original's, so that the two can be read
side by side (`docs/VERIFIER-THEORY.md`). Lean 3's `list.nth` is `[i]?`, `inth` is
`getD`, `list.forall₂` is `List.Forall₂`, `set` is `Set`; the original's `let Γ := … in`
of `env.proof'.thm` is written out. One rule is added, `conv'.trans`: the primary
specification `examples/mm0.mm0` has the certificate `CTrans` (`VerifyConvTrans`), and
`mm0.lean` omits it; the judge is the primary specification, and the `Unfold` command
of a proof file needs it. Two definitions are corrected, `safe_subst` and
`sexpr.free'`: see the comments there. Nothing else is changed.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Forall2

namespace mm0

structure sort_data where
  pure : Bool := false
  strict : Bool := false
  provable : Bool := false
  free : Bool := false

abbrev sort_id := ℕ
abbrev term_id := ℕ
abbrev thm_id := ℕ
abbrev var_id := ℕ

inductive binder
  | bound : sort_id → binder
  | reg : sort_id → Finset var_id → binder

def binder.sort : binder → sort_id
  | .bound s => s
  | .reg s _ => s

-- Lean doesn't do great with nested inductives
-- inductive sexpr
-- | var : var_id → sexpr
-- | app : term_id → list sexpr → sexpr

inductive sexpr
  | var : var_id → sexpr
  | term : term_id → sexpr
  | app1 : sexpr → sexpr → sexpr

def sexpr.app' : sexpr → List sexpr → sexpr
  | f, [] => f
  | f, x :: xs => sexpr.app' (sexpr.app1 f x) xs

def sexpr.app (t : term_id) : List sexpr → sexpr :=
  sexpr.app' (sexpr.term t)

abbrev dep_type := sort_id × Finset var_id

abbrev ctx := List binder

inductive decl
  | sort : sort_id → sort_data → decl
  | term : term_id → ctx → dep_type → decl
  | defn : term_id → ctx → dep_type → Option (List sort_id × sexpr) → decl
  | ax : ctx → List sexpr → sexpr → decl
  | thm : ctx → List sexpr → sexpr → decl

abbrev env := List decl

def env.get_sd (e : env) (s : sort_id) (sd : sort_data) : Prop :=
  decl.sort s sd ∈ e

inductive env.get_term (e : env) (t : term_id) (a : ctx) (r : dep_type) : Option (List sort_id × sexpr) → Prop
  | term : decl.term t a r ∈ e → env.get_term e t a r none
  | defn {o} : decl.defn t a r o ∈ e → env.get_term e t a r o

def env.get_thm (e : env) (t : ctx) (a : List sexpr) (r : sexpr) : Prop :=
  decl.ax t a r ∈ e ∨ decl.thm t a r ∈ e

def env.is_sort (e : env) (s : sort_id) : Prop := ∃ sd, e.get_sd s sd

def ctx.is_bound (Γ : ctx) (x : var_id) : Prop :=
  ∃ s, Γ[x]? = some (binder.bound s)

def dep_type.ok (e : env) (Γ : ctx) : dep_type → Prop
  | (s, vs) => env.is_sort e s ∧ ∀ x ∈ vs, ctx.is_bound Γ x

-- Lean doesn't like induction on lists on the right, but
-- we write it this way for consistency with mm0.mm0
inductive ctx.ok (e : env) : ctx → Prop
  | nil : ctx.ok e []
  | bound {s sd Γ} :
    env.get_sd e s sd → ¬ sd.strict →
    ctx.ok e Γ → ctx.ok e (Γ ++ [binder.bound s])
  | reg {s vs Γ} : dep_type.ok e Γ (s, vs) →
    ctx.ok e Γ → ctx.ok e (Γ ++ [binder.reg s vs])

-- Helper function to allow defining the mutual recursive functions Expr and ExprBi
def sexpr.ok_bi' (e : env) (Γ : ctx) (x : sexpr) (P : sort_id → Prop) : binder → Prop
  | .bound s => ∃ v, x = sexpr.var v ∧ Γ[v]? = some (binder.bound s)
  | .reg s _ => P s

-- The lean version has an extra argument because there are preterms
-- (unapplied expressions)
inductive sexpr.ok' (e : env) (Γ : ctx) : sexpr → List binder → sort_id → Prop
  | var {v bi} : Γ[v]? = some bi → sexpr.ok' e Γ (sexpr.var v) [] bi.sort
  | term {f bis ret o} : e.get_term f bis ret o →
    sexpr.ok' e Γ (sexpr.term f) bis ret.1
  | app_var {f s v bis ret} :
    Γ[v]? = some (binder.bound s) →
    sexpr.ok' e Γ f (binder.bound s :: bis) ret →
    sexpr.ok' e Γ (sexpr.app1 f (sexpr.var v)) bis ret
  | app_reg {f x s vs bis ret} :
    sexpr.ok' e Γ f (binder.reg s vs :: bis) ret →
    sexpr.ok' e Γ x [] s →
    sexpr.ok' e Γ (sexpr.app1 f x) bis ret

def sexpr.ok (E : env) (Γ : ctx) (x : sexpr) (s : sort_id) : Prop :=
  sexpr.ok' E Γ x [] s

def sexpr.ok_bi (E : env) (Γ : ctx) (x : sexpr) : binder → Prop
  | .bound s => ∃ v, x = sexpr.var v ∧ Γ[v]? = some (binder.bound s)
  | .reg s _ => sexpr.ok E Γ x s

def sexpr.ok_prov (E : env) (Γ : ctx) (x : sexpr) : Prop :=
  ∃ s sd, sexpr.ok E Γ x s ∧ E.get_sd s sd ∧ sd.provable

def append_dummies (Γ : ctx) (ds : List sort_id) : ctx :=
  Γ ++ ds.map binder.bound

def sexpr.has_var (Γ : ctx) : sexpr → var_id → Prop
  | .var u, v => ∃ bi, Γ[u]? = some bi ∧
    match bi with
    | binder.bound _ => u = v
    | binder.reg _ vs => v ∈ vs
  | .term _, _ => False
  | .app1 f x, v => sexpr.has_var Γ f v ∨ sexpr.has_var Γ x v

def maybe_free_args (es : List sexpr) (a : binder) (v : var_id) : Prop :=
  ∃ s vs, a = binder.reg s vs ∧ ¬ ∃ u ∈ vs, es[u]? = some (sexpr.var v)

def sexpr.free' (E : env) (Γ : ctx) (v : var_id) :
    sexpr → List sexpr → List Prop → Prop
  | .var u, _, _ => sexpr.has_var Γ (sexpr.var u) v
  -- the original joins the two cases with `∧`; `mm0.mm0`'s `FreeApp` has `∨`, and the
  -- rule's sense is the disjunction. The third deviation of the port.
  | .term f, es, ps => ∃ args r rs o,
    E.get_term f args (r, rs) o ∧
    ((∃ (n : ℕ) (free : Prop) (a : binder), ps[n]? = some free ∧ args[n]? = some a ∧
      free ∧ maybe_free_args es a v) ∨
    ∃ u ∈ rs, es[u]? = some (sexpr.var v))
  | .app1 f x, es, ps =>
    sexpr.free' E Γ v f (x :: es) (sexpr.free' E Γ v x [] [] :: ps)

def sexpr.free (E : env) (Γ : ctx) (x : sexpr) (v : var_id) : Prop :=
  sexpr.free' E Γ v x [] []

def term_ok (E : env) (t : term_id) (args : ctx) (ret : dep_type) : Prop :=
  (¬ ∃ a r v, E.get_term t a r v) ∧
  ctx.ok E args ∧ dep_type.ok E args ret ∧
    ∃ sd, E.get_sd ret.1 sd ∧ ¬ sd.pure

def defn_ok (E : env) (t : term_id) (args : ctx) (ret : dep_type) (ds : List sort_id) (x : sexpr) : Prop :=
  term_ok E t args ret ∧
    let Γ := append_dummies args ds
    ctx.ok E Γ ∧ sexpr.ok E Γ x ret.1 ∧
      ∀ v, sexpr.free E Γ x v → v ∈ ret.2 ∨
        ∃ sd s, (Γ[v]? = some (binder.bound s) ∧
          E.get_sd s sd ∧ sd.free)

def axiom_ok (E : env) (args : ctx) (hs : List sexpr) (ret : sexpr) : Prop :=
  ctx.ok E args ∧ ∀ x ∈ List.cons ret hs, sexpr.ok_prov E args x

def decl.ok (E : env) : decl → Prop
  | .sort _ _ => True
  | .term t args ret => term_ok E t args ret
  | .defn t args ret none => term_ok E t args ret
  | .defn t args ret (some (ds, x)) => defn_ok E t args ret ds x
  | .ax args hs ret => axiom_ok E args hs ret
  | .thm args hs ret => axiom_ok E args hs ret

inductive env.ok : env → Prop
  | nil : env.ok []
  | cons {E d} : env.ok E → decl.ok E d → env.ok (E ++ [d])

inductive env.extend : env → env → Prop
  | nil : env.extend [] []
  | keep {E1 E2 d} : env.extend E1 E2 → env.extend (E1 ++ [d]) (E2 ++ [d])
  | defn_skip {E1 E2 id a r o} :
    env.extend E1 E2 →
    env.extend E1 (E2 ++ [decl.defn id a r o])
  | defn_def {E1 E2 id a r o} :
    env.extend E1 E2 →
    env.extend (E2 ++ [decl.defn id a r none]) (E2 ++ [decl.defn id a r o])
  | thm_skip {E1 E2 a h r} :
    env.extend E1 E2 →
    env.extend E1 (E2 ++ [decl.thm a h r])

instance : Inhabited sexpr := ⟨sexpr.var (0 : ℕ)⟩

def sexpr.subst (σ : List sexpr) : sexpr → sexpr
  | .var v => σ.getD v default
  | .term f => sexpr.term f
  | .app1 f x => sexpr.app1 (sexpr.subst σ f) (sexpr.subst σ x)

-- In mm0.mm0, we use a type CExpr to denote proofs and existentially
-- quantify over them to get the proof judgment. In Lean, we can do this
-- directly with an inductive proof predicate.
inductive conv' (E : env) (Γ : ctx) : sexpr → sexpr → List binder → sort_id → Prop
  | refl {e args s} : sexpr.ok' E Γ e args s → conv' E Γ e e args s
  | symm {e1 e2 s} : conv' E Γ e1 e2 [] s → conv' E Γ e2 e1 [] s
  -- `CTrans` of `mm0.mm0`, absent from `mm0.lean`
  | trans {e1 e2 e3 s} : conv' E Γ e1 e2 [] s → conv' E Γ e2 e3 [] s → conv' E Γ e1 e3 [] s
  | cong {f1 f2 bi bis x1 x2 s} :
    sexpr.ok_bi E Γ x1 bi → sexpr.ok_bi E Γ x2 bi →
    conv' E Γ f1 f2 (bi :: bis) s →
    conv' E Γ x1 x2 [] bi.sort →
    conv' E Γ (sexpr.app1 f1 x1) (sexpr.app1 f2 x2) bis s
  | unfold {t args ret ys val es zs e2 s} :
    E.get_term t args ret (some (ys, val)) →
    List.Forall₂ (sexpr.ok_bi E Γ) es args →
    List.Forall₂ (fun y z => Γ[z]? = some (binder.bound y)) ys zs →
    conv' E Γ (sexpr.app t es) e2 [] s →
    conv' E Γ (sexpr.subst (es ++ List.map sexpr.var zs) val) e2 [] s

def conv (E : env) (Γ : ctx) (e1 e2 : sexpr) (s : sort_id) : Prop :=
  conv' E Γ e1 e2 [] s

-- The original reads the binders `u` and `v` and the dependency of `v` on `u` in `Γ`,
-- the context of the proof, where `args`, the binders of the theorem applied, are
-- meant (`mm0.mm0`, `VerifyProofThm`, has the same, against its own comment, "the
-- disjoint variable conditions of the theorem", and `mm0.md`); the substituted
-- expression `e2` lives in `Γ`, which stays. The second deviation of the port.
def safe_subst (Γ args : ctx) (σ : List sexpr) : Prop :=
  ∀ u v, (∃ s, args[u]? = some (binder.bound s)) →
    v < args.length → ¬ sexpr.has_var args (sexpr.var v) u →
    ∀ y e2, σ[u]? = some (sexpr.var y) → σ[v]? = some e2 →
      ¬ sexpr.has_var Γ e2 y

-- We generalize to a possibly infinite set of hypotheses for no particular reason
inductive proof (E : env) (Γ : ctx) (Hs : Set sexpr) : sexpr → Prop
  | hyp {h} : h ∈ Hs → proof E Γ Hs h
  | thm {args hs ret σ} :
    E.get_thm args hs ret →
    List.Forall₂ (sexpr.ok_bi E Γ) σ args →
    safe_subst Γ args σ →
    (∀ h ∈ hs, proof E Γ Hs (sexpr.subst σ h)) →
    proof E Γ Hs (sexpr.subst σ ret)
  | conv {e1 e2 s} : conv E Γ e1 e2 s → proof E Γ Hs e1 → proof E Γ Hs e2

inductive env.proof' : env → Prop
  | nil : env.proof' []
  | sort {E s sd} : env.proof' E → env.proof' (E ++ [decl.sort s sd])
  | term {E id a r} : env.proof' E → env.proof' (E ++ [decl.term id a r])
  | defn {E id a r o} : env.proof' E → env.proof' (E ++ [decl.defn id a r (some o)])
  | ax {E a h r} : env.proof' E → env.proof' (E ++ [decl.ax a h r])
  | thm {E a hs r ds} :
    ctx.ok E (append_dummies a ds) → proof E (append_dummies a ds) {h | h ∈ hs} r →
    env.proof' E → env.proof' (E ++ [decl.thm a hs r])

def env.proof (E : env) : Prop := ∃ E', env.extend E E' ∧ env.proof' E'

end mm0
