# The 2017 paper and the Lean theory: a correspondence

Written for reading `theory/Theory/*.lean` with D. Vlasov, *Proof Search Algorithm in
Pure Logical Framework* (2017, `russell-flow/docs/proof_search_algo.pdf`; "the paper"
below) open beside it, and with `docs/THEORY.md` for what the Lean adds to the paper.
Four parts:

1. [The correspondence](#1-the-correspondence): for each definition and theorem of the
   paper, the Lean declaration, the statement in the paper's notation and in Lean, the
   lemmas the proof uses, and a proof sketch over those lemma names.
2. [What THEORY.md adds](#2-what-theorymd-adds-to-the-paper): the same for the parts of
   the theory the paper has not (conditions, closing, the unifier, the engine lemmas,
   the keyed engine, definitions).
3. [Where the Lean differs from the paper](#3-where-the-lean-differs-from-the-paper):
   every place found, each with where to look in both.
4. [The lemma dependency graphs](#4-the-lemma-dependency-graphs) of `soundness`,
   `generality` and `completeness`, and [the reading order](#5-reading-order).

How this was made (2026-10-27, at commit 629abdd). The declarations, their
statements, docstrings and the constants their proofs use were extracted from the
compiled package by a Lean metaprogram (`theory/tools/Extract.lean`: every constant of
the `Theory.*` modules, auxiliary constants of mutual and well-founded recursion
expanded into their parents); the closures, the graphs and the reading order were
computed from that by `theory/tools/correspondence.py`. The statements quoted below
are copied from the sources, with binders abbreviated where noted. The prose — the
paper-side statements, the sketches and the list of differences — is a reading, not an
extraction, and is where to disagree.

Notation. The paper writes `θ(e)` for application and `θ ∘ η` for composition with
`(θ ∘ η)(e) = θ(η(e))`; the Lean has `θ.apply e` and `θ.comp η` with the same order
(`Subst.apply_comp`). `θ ≼ σ` ("σ is an instance of θ", `Subst.IsInstance σ θ`) means
`σ = δ ∘ θ` for some `δ`. `run n` is `State.run U db st n`, the proof variant tree
after `n` rounds; `root n` is `(run n).rootEntries U st`. Every theorem of the first
variant is stated for an arbitrary unification structure `U : Unification`; the
concrete unifier is `Unify.postulate`.

## 1. The correspondence

### Index

| Paper | Lean | File |
|---|---|---|
| §2.1 grammar `G`, `e : n`, variables of type `n` | `Ty`, `Var`, `Exp`, `Exp.ty`, `Signature`, `Signature.WF` | `Term.lean` |
| §2.1 assertion `a = p₁,…,pₙ / p₀`; system `D = (G, A)` | `Assertion`, `Database`, `Assertion.WF`, `Database.WF` | `Deduction.lean` |
| §2.1 the statement `s` to prove | `Statement`, `Statement.subst`, `Consts` | `Deduction.lean`, `Term.lean` |
| §2.2 substitution `v : n ↦ e : m`, application, composition | `Subst`, `Subst.Typed`, `Ty.fits`, `Subst.apply`, `Subst.comp` | `Subst.lean` |
| §2.2 unification, uniqueness of the unifier | `Problem`, `Solves`, `Unification` (the postulate), `Unify.postulate` | `Unification.lean`, `Unify.lean` |
| §2.3 proof tree, a-nodes `(a, θ)`, e-nodes | `PTree`, `PTree.subst`, `PTree.expr` | `Deduction.lean` |
| §2.3 congruent `T₁ ∼ T₂` | `PTree.Congruent` | `Deduction.lean` |
| §2.3 more general `T₁ ≽ T₂` | `PTree.IsInstance` | `Deduction.lean` |
| §2.3 proof; witness; proof of a statement | `Shape`, `CondsHold`, `Valid`, `IsProof` | `Deduction.lean` |
| Lemma 1 (monotonicity) | `Shape.subst` | `Deduction.lean` |
| §3.1 PVT, its growth, fresh variables, `n ≺ m` | `ENode`, `ANode`, `State`, `State.init`, `tryAssertion`, `expandNode`, `expandAll`, `run` | `Search.lean` |
| §3.1 proof variant `v`, `π(v)` | `SptTree`, `SptTree.At`, `State.proofOf`, `Entry.proof` | `Search.lean`, `Spt.lean` |
| §3.2 SPT, `s(n)`, `θ(T)`; the leaf SPT from a premise | `Entry`, `leafEntries`, `sptE`, `sptA`, `rootEntries` | `Search.lean` |
| §3.2 unification of substitutions, `mgu(Ξ)`, `com(Ξ)` | `Subst.eqs`, `Unification.join`, `joinAll`, `joinAll_spec` | `Subst.lean`, `Unification.lean`, `Spt.lean`, `General.lean`, `Engine.lean` |
| §3.2 SPT of an a-node `T₀(T₁,…,Tₙ)` | `tuples`, `anodeEntries` | `Search.lean` |
| §3.2 SPT of an e-node `T₀(T₁)` | `sptE` | `Search.lean` |
| Lemma 2 (an SPT defines one proof variant) | by construction; `anodes_nodup`, `sibling_disjoint` | `Generality.lean` |
| Theorem 1 (correctness) | `soundness_valid`, `soundness` | `Theorems.lean`, `Spt.lean`, `Preserve.lean`, `Closing.lean` |
| Theorem 2 (generality) | `generality`, `generality'` | `Theorems.lean`, `Generality.lean` |
| Theorem 3 (completeness) | `completeness`, `completeness'` | `Theorems.lean`, `Completeness.lean` |
| Corollary 1 (provability is c.e.) | — (not stated; see §3, item 23) | |

### §2.1 Language: `G`, `e : n`, variables

**Paper.** A context-free unambiguous grammar `G` with non-terminals `N`; `Gₙ` is `G`
started at `n`; `e : n` means `e ∈ L(Gₙ)`; for every `n` an infinite set of terminal
symbols `v` with the rule `n → v`, the variables of type `n`.

**Lean** (`Term.lean:16–218`).

```lean
structure Ty where sort : ℕ; name : Bool          -- a sort, and "names only"
structure Var where id : ℕ; ty : Ty
inductive Exp | var (v : Var) | const (k : ℕ) (ty : Ty) | app (f : ℕ) (ty : Ty) (args : List Exp)
def Exp.ty : Exp → Ty                               -- the type of an expression, e : n
structure Signature where args : ℕ → List Ty; sort : ℕ → ℕ
def Signature.WF (sig : Signature) : Exp → Prop     -- well-formed under a signature
```

`e : n` is `e.ty = n`. A variable is `⟨id, ty⟩`, so there are infinitely many of every
type. `Exp.const` is a variable of the statement being proved (see "the statement"
below); `Consts.names` (line 179) lists the names that occur in an expression, with
the declared dependencies of the constants. **Uses.** `Exp.vars`, `Exp.consts`,
`Exp.rename` (line 159: `id ↦ base + id`, the fresh renaming of §3.1).

**Note.** `Signature.WF` is defined and used by nothing in the theory: no theorem of
§1 or §2 assumes that expressions are well formed under a signature (§3, item 1).

### §2.1 Assertions and the deductive system

**Paper.** An assertion `a = (p₁, …, pₙ) / p₀` with premises `pᵢ` and proposition
`p₀`; `D = (G, A)` with `A` a set of assertions.

**Lean** (`Deduction.lean:10–48`).

```lean
structure Assertion where vars : List Var; pairs : List (Var × Var); hyps : List Exp; concl : Exp
structure Database  where asserts : List Assertion; defs : List Def := []
structure Assertion.WF (A : Assertion) : Prop where
  concl_vars : A.concl.vars ⊆ A.vars.toFinset
  hyps_vars  : ∀ h ∈ A.hyps, h.vars ⊆ A.vars.toFinset
  pairs_vars : ∀ p ∈ A.pairs, p.1 ∈ A.vars ∧ p.2 ∈ A.vars
  pairs_bound : ∀ p ∈ A.pairs, p.1.ty.name = true
def Database.WF (db : Database) : Prop := ∀ A ∈ db.asserts, A.WF
```

`A` is `db.asserts`, indexed by number; `db.asserts[a]? = some A` everywhere an
assertion is used. Beyond the paper, an assertion lists its binders `vars` (the
variables it is over) and its `pairs` (`D(A)` of `DESIGN.md`, "Where MM0 differs",
condition 2: the bound-variable conditions the paper sets aside). `WF` is the
hypothesis `hwf : db.WF` of every theorem: the binders cover the assertion.

### §2.1 The statement being proved

**Paper.** A statement `s = (p₁, …, pₙ) / p₀` like any assertion; its variables are
"non-replaceable" in the PVT (§3.1).

**Lean** (`Deduction.lean:50–66`, `Term.lean:173`).

```lean
structure Consts where ty : ℕ → Ty; deps : ℕ → Finset ℕ
structure Statement where consts : Consts; dummies : ℕ → Bool; hyps : List Exp; concl : Exp
def Statement.subst (σ : Subst) (st : Statement) : Statement :=
  { st with hyps := st.hyps.map σ.apply, concl := σ.apply st.concl }
```

The variables of the statement are constants `Exp.const k (consts.ty k)` with their
declared dependencies `consts.deps k` (regular `(ph: wff x)` depends on `x`); nothing
in a `Subst` moves them, which is the paper's "non-replaceable". A statement may also
contain variables — metavariables (`THEORY.md`, decision 7) — and then every theorem is
about its instances `st.subst σ`. `dummies s` says whether sort `s` admits dummies
(decision 8). **Uses.** `Statement.subst_subst` (line 64): `(st.subst θ).subst δ =
st.subst (δ.comp θ)`.

### §2.2 Substitutions

**Paper.** A substitution is a mapping `v : n ↦ e : m` where `n → m` is derivable in
`G` (the class/set example); application `θ(e)`, component-wise on complex objects;
composition `(θ ∘ η)(e) = θ(η(e))`.

**Lean** (`Subst.lean:11–135`, `Term.lean:22`).

```lean
structure Subst where f : Var → Exp; dom : Finset Var; hdom : ∀ v, v ∈ dom ↔ f v ≠ .var v
def Ty.fits (v e : Ty) : Prop := v.sort = e.sort ∧ (v.name = true → e.name = true)
def Subst.Typed (θ : Subst) : Prop := ∀ v, v.ty.fits (θ.f v).ty ∧ (v.ty.name = true → (θ.f v).IsName)
def Subst.apply (θ : Subst) : Exp → Exp                -- θ(e); constants untouched
def Subst.comp (θ η : Subst) : Subst                    -- θ ∘ η
theorem Subst.apply_comp : (θ.comp η).apply e = θ.apply (η.apply e)
theorem Subst.comp_assoc / comp_id / id_comp / Subst.ext (h : θ.f = η.f) : θ = η
def Subst.IsInstance (σ θ : Subst) : Prop := ∃ δ, σ = δ.comp θ        -- θ ≼ σ
def Subst.Idem (θ : Subst) : Prop := θ.comp θ = θ
def Subst.restrict (θ : Subst) (s : Finset Var) : Subst  -- the identity outside s
```

The paper's rule `n → m` is `Ty.fits`: the same sort, and a name type only to names
(`DESIGN.md`, condition 1: "names of sort `s`" is the one subtype). The paper assumes
every application "correct"; the Lean makes it a property `Typed` of the substitution
and carries `θ.Typed` as a hypothesis through every theorem. A substitution has a
finite support `dom`, so two with the same map are equal (`Subst.ext`). **Uses.**
`Subst.ty_apply`, `apply_isName`, `Typed.comp`, `vars_apply`, `consts_apply`,
`restrict_apply` (lines 142–235).

### §2.2 Unification

**Paper.** `e₁` unifies with `e₂` iff `e₂ = θ(e₁)` for some `θ`; non-symmetric, "the
consequence of such non-symmetry is that if a unifier exists, it is unique".

**Lean** (`Unification.lean:11–56`).

```lean
abbrev Problem := List (Exp × Exp)
def Solves (σ : Subst) (E : Problem) : Prop := ∀ p ∈ E, σ.apply p.1 = σ.apply p.2
structure Unification where
  mgu : Problem → Option Subst
  typed : mgu E = some θ → θ.Typed
  idem  : mgu E = some θ → θ.Idem
  solves : mgu E = some θ → Solves θ E
  mostGeneral : σ.Typed → Solves σ E → ∃ θ, mgu E = some θ ∧ σ.IsInstance θ
  dom_sub   : mgu E = some θ → ∀ v ∈ θ.dom, v ∈ E.vars
  range_sub : mgu E = some θ → ∀ v, ∀ w ∈ (θ.f v).vars, w ∈ E.vars ∨ w = v
theorem Unification.none_iff : U.mgu E = none ↔ ∀ σ, σ.Typed → ¬ Solves σ E
```

This is the draft's Postulate 2.5 (`THEORY.md`, "The documents"), two-sided: a
substitution solves `e₁ = e₂` when `σ(e₁) = σ(e₂)`, the unifier is idempotent, typed,
and most general among *typed* solutions, hence unique up to renaming only. The
structure is a parameter `U` of every theorem of §1; `Unify.postulate : Unification`
(`Unify.lean:800`) is the concrete first-order unifier with its proof (§2, "The
unifier"). The difference from the paper's one-sided, unique unifier is §3, item 4.

### §2.3 Proof trees

**Paper.** A proof tree: nodes of odd depth labelled with assertions (a-nodes), of
even depth with expressions (e-nodes); an e-node has at most one descendant a-node;
leaves are e-nodes; an a-node's label is the pair `(a, θ)`. Validity is not demanded.

**Lean** (`Deduction.lean:94–250`).

```lean
inductive PTree | hyp (h : ℕ) (e : Exp) | step (e : Exp) (a : ℕ) (θ : Subst) (children : List PTree)
def PTree.expr : PTree → Exp
def PTree.binders (db) (a : ℕ) : Finset Var := db.asserts[a]!.vars.toFinset
def PTree.subst (db) (δ : Subst) : PTree → PTree           -- δ(T), component-wise
  | hyp h e => hyp h (δ.apply e)
  | step e a θ cs => step (δ.apply e) a ((δ.comp θ).restrict (binders db a)) (substList db δ cs)
def PTree.conds (db) : PTree → List Cond                   -- the pairs of every step under its θ
def PTree.exprs (db) : PTree → List Exp;  def PTree.allVars (db) (T) : Finset Var
```

An e-node and the a-node below it are one constructor `step e a θ children`: the
expression, the assertion, its substitution and the children (the e-nodes of the
premises). A leaf `hyp h e` carries the number `h` of the hypothesis of the statement
it is, with its expression (§3, item 5). `subst` is the paper's component-wise
application, with the step's substitution composed and then kept on the binders of
its assertion (§3, item 6). **Uses.** `expr_subst`, `conds_subst`, `exprs_subst`,
`cond_mem_exprs`, `mem_allVars`.

### §2.3 Congruent, `T₁ ∼ T₂`

**Paper.** Isomorphic graphs, corresponding a-nodes labelled with the same assertion,
no condition on e-nodes.

**Lean** (`Deduction.lean:348`).

```lean
def PTree.Congruent : PTree → PTree → Prop
  | .hyp h _, .hyp h' _ => h = h'
  | .step _ a _ cs, .step _ a' _ cs' => a = a' ∧ PTree.CongruentList cs cs'
  | _, _ => False
```

The same shape and assertions; and, beyond the paper, the same hypothesis at
corresponding leaves (§3, item 5).

### §2.3 More general, `T₁ ≽ T₂`

**Paper.** `T₁ ≽ T₂` iff `T₂ = δ(T₁)` for some `δ`; it implies `T₁ ∼ T₂`.

**Lean** (`Deduction.lean:344`).

```lean
def PTree.IsInstance (db) (T' T : PTree) : Prop := ∃ δ : Subst, T' = T.subst db δ   -- T ≽ T'
```

The implication `≽ ⟹ ∼` is not stated (it is not needed: `generality` and
`completeness` give both).

### §2.3 Proof, witness, proof of a statement

**Paper.** A proof tree is a *proof* iff every transition from `e₁, …, eₘ` through
`(a, θ)` to `e₀` has `(e₁, …, eₘ) / e₀ = θ(a)`; `θ` is the *witness*. It is a proof
*of* `s = (p₁, …, pₙ) / p₀` iff it is a proof, its root is `p₀` and every leaf is some
`pᵢ`.

**Lean** (`Deduction.lean:264–326`).

```lean
inductive Shape (db : Database) (st : Statement) : PTree → Prop
  | hyp  (h e) (hh : h < st.hyps.length) (he : e = st.hyps[h]!) : Shape db st (.hyp h e)
  | step (e a θ cs A) (hA : db.asserts[a]? = some A) (hθ : θ.Typed) (hdom : θ.dom ⊆ A.vars.toFinset)
         (he : e = θ.apply A.concl) (hcs : cs.map PTree.expr = A.hyps.map θ.apply)
         (hall : ∀ c ∈ cs, Shape db st c) : Shape db st (.step e a θ cs)
def CondsHold (db st) (T : PTree) : Prop := ∀ k ∈ T.conds db, k.Holds st.consts
def Valid   (db st) (T : PTree) : Prop := Shape db st T ∧ CondsHold db st T
def IsProof (db st) (T : PTree) : Prop :=
  Valid db st T ∧ T.expr = st.concl ∧ ∀ v ∈ T.allVars db, v.ty.name = true ∧ st.dummies v.ty.sort = true
```

`Shape` is the paper's "proof" (`he`, `hcs`: the transition is `θ(a)`, the witness
`θ` typed and on the binders) *with* the leaf condition of "proof of `s`" built in: a
leaf is a hypothesis of `st`. `Valid` adds the bound-variable conditions (§2,
"Conditions"). `IsProof` is "proof of `s`": root `p₀`, and — not in the paper — every
variable left in the tree is a name of a sort that admits dummies (§3, items 7, 22).

### Lemma 1 (monotonicity)

**Paper.** If `π` is a proof of `a = (p₁, …, pₙ) / p₀` and `θ` any substitution of the
variables occurring in `a`, then `θ(π)` is a proof of `θ(a)`. Proof: a transition with
witness `η` has, under `θ`, the witness `θ ∘ η`.

**Lean** (`Deduction.lean:283`).

```lean
theorem Shape.subst (hwf : db.WF) (h : Shape db st T) (hδ : δ.Typed) :
    Shape db (st.subst δ) (T.subst db δ)
```

**Uses.** `Subst.Typed.comp`, `Subst.Typed.restrict`, `Subst.restrict_apply`,
`Subst.apply_comp`, `Assertion.WF.concl_vars`, `Assertion.WF.hyps_vars`,
`PTree.expr_subst`, `PTree.substList_eq_map`, `getElem!_map'`.

**Sketch.** Induction on `Shape`. At a step with witness `θ`, the new witness is
`(δ ∘ θ)` restricted to the binders (`Typed.comp`, `Typed.restrict`); it acts on the
conclusion and the hypotheses as `δ ∘ θ` does because they are over the binders
(`WF.concl_vars`, `WF.hyps_vars`, `restrict_apply`), and `apply_comp` turns
`(δ ∘ θ)(q)` into `δ(θ(q))`, the substituted expression. At a leaf, `st.subst δ` has
`δ(st.hyps[h])` at `h`. The lemma needs `db.WF` and a typed `δ`, which the paper does
not say, and it is about `Shape` only: the conditions are not monotone (§3, item 8).

### §3.1 The proof variant tree

**Paper.** A tree with e-nodes (expressions) and a-nodes (assertions); variables of
e-nodes flagged replaceable or not; the root `p₀` with all variables non-replaceable;
an e-node `e` is forked with all assertions `a` whose propositions unify with `e` with
unifier `θ`, the free variables of `a` replaced by fresh ones; the children of
`(a, θ)` with `a = (q₁, …, qₙ) / q₀` are `θ(q₁), …, θ(qₙ)`; `n ≺ m` for "n is a direct
descendant of m".

**Lean** (`Search.lean:18–141`).

```lean
structure ENode where expr : Exp; parent : Option (ℕ × ℕ); expanded : Bool
structure ANode where parent : ℕ; assertion : ℕ; base : ℕ; sub : Subst; children : List ℕ; conds : List Cond
structure State where enodes : Array ENode; anodes : Array ANode; freshBase stride : ℕ; tried : List (ℕ × ℕ × ℕ)
def State.init (db st) : State        -- one e-node, st.concl, unexpanded
def State.baseOf (s) (j : ℕ) : ℕ := s.freshBase + j * s.stride
def State.renamed (base : ℕ) (x : Var) : Var := ⟨base + x.id, x.ty⟩
def State.tryAssertion (U db) (i a : ℕ) (s : State) : State :=   -- one fork
  match db.asserts[a]? with
  | some A => match U.mgu [(s.enodes[i]!.expr, A.concl.rename (s.baseOf s.anodes.size))] with
    | some θ => recordAt i a _ (addNode i a s A θ)      -- children: θ(A.hyps[k].rename base)
    | none   => recordAt i a _ s
  | none => recordAt i a _ s
def State.expandNode (U db) (i : ℕ) (s) : State := mark i (foldl over every a of tryAssertion)
def State.expandAll  (U db) (s) : State := foldl expandNode over every unexpanded e-node
def State.run (U db st) : ℕ → State | 0 => init db st | n + 1 => expandAll U db (run U db st n)
```

The e-nodes and a-nodes are two arrays; `n ≺ m` is `ENode.parent = some (j, k)` (the
`k`-th child of a-node `j`) and `ANode.parent`, `ANode.children`. The replaceable flag
is not needed: the statement's variables are constants. The fresh variables of the
`j`-th a-node are the assertion's binders renamed by `baseOf j`: `freshBase` is above
every variable of the statement, `stride` above every binder of the database
(`strideOf`), so blocks of distinct nodes never meet. "Unify" is `U.mgu` on the one
equation `expr = A.concl.rename base` (two-sided, §3, item 4). The order of expansion,
which the paper leaves open, is breadth first by rounds (`run n`, §3, item 11).
`tried` records every attempt with its base — read by no computation, only by the
completeness proof (`StateInv.tried_spec`, `tried_of_lt`). `ANode.conds` are the pairs
of the assertion under `θ`, renamed (`nodeConds`, §2, "Conditions").

### §3.1 Proof variant `v`, `π(v)`

**Paper.** A subtree of the PVT in which every e-node has at most one descendant is a
*proof variant* `v`; removing the unrelated data gives a proof tree `π(v)`.

**Lean** (`Search.lean:38`, `Spt.lean:70`, `Search.lean:190–213`).

```lean
inductive SptTree | leaf (enode : ℕ) (hyp : ℕ) | node (anode : ℕ) (children : List SptTree)
inductive SptTree.At (s : State) : ℕ → SptTree → Prop      -- the tree sits at e-node i of s
  | leaf (i h) (hi : i < s.enodes.size) : At s i (.leaf i h)
  | node (i j cs) (hj : j < s.anodes.size) (hp : s.anodes[j]!.parent = i)
         (hlen : cs.length = s.anodes[j]!.children.length)
         (hcs : ∀ k < cs.length, At s (s.anodes[j]!.children[k]!) cs[k]!) : At s i (.node j cs)
def State.stepSub (db) (a : ANode) (θ : Subst) : Subst     -- x ↦ θ(θ_a(renamed a.base x)) on A.vars
def State.proofOf (db) (s : State) (θ : Subst) : SptTree → PTree   -- π(v) under θ
  | .leaf i h => .hyp h (θ.apply s.enodes[i]!.expr)
  | .node j cs => .step (θ.apply s.enodes[a.parent]!.expr) a.assertion (stepSub db a θ) (proofsOf db s θ cs)
def Entry.proof (db) (s) (E : Entry) : PTree := State.proofOf db s E.sub E.tree
```

A variant is a tree of node numbers: at each e-node either the hypothesis that closes
it or one a-node with a variant at each child. `π(v)` is `proofOf` and takes a
substitution `θ`, the answer, applied to every expression: a `PTree` has concrete
expressions, a variant has only node numbers (§3, item 13). The substitution of a step
is `stepSub`: the renamed binder under the node's unifier `θ_a` and then `θ`.

### §3.2 Substitution proof trees, `s(n)`, `θ(T)`; the leaf SPT

**Paper.** Each PVT node `n` has a set `s(n)` of SPTs; an SPT is a proof tree whose
nodes are labelled with PVT nodes and substitutions; `θ(T)` is the substitution at
the root. For a new e-node `e`, if a premise `pᵢ` of the statement unifies with `e`
("variables in `e` are also non-replaceable"), the one-node SPT with that unifier is
put into `s(e)`.

**Lean** (`Search.lean:45, 144, 172–186`).

```lean
structure Entry where tree : SptTree; sub : Subst; conds : List Cond
def State.leafEntries (U st) (i : ℕ) (e : Exp) : List Entry :=
  (List.range st.hyps.length).filterMap fun h =>
    (U.mgu [(e, st.hyps[h]!)]).map fun θ => { tree := .leaf i h, sub := θ, conds := [] }
def State.sptE (U st) (s : State) : ℕ → ℕ → List Entry      -- s(e) down to a depth (fuel)
  | 0, _ => []
  | fuel + 1, i => leafEntries U st i s.enodes[i]!.expr ++
      (aChildren s i).flatMap fun j => anodeEntries U st.consts j s.anodes[j]! (children's sptE at fuel)
def State.rootEntries (U st) (s) : List Entry := sptE U st s s.enodes.size 0
```

`s(n)` for an e-node is `sptE U st s fuel i`, a pure function of the state, computed
to depth `fuel` (`fuel_le`: the number of e-nodes is depth enough, hence
`rootEntries`); for an a-node, `sptA`. `θ(T)` is `Entry.sub`; `Entry.conds` is new
(§2, "Conditions"). The leaf SPT is `leafEntries`: the hypotheses `pᵢ` unified
two-sidedly with `e` (§3, item 4).

### §3.2 Unification of substitutions: `Ξ`, `mgu(Ξ)`, `com(Ξ)`

**Paper.** For `Ξ = {θ₁, …, θₙ}`, `δ` is a unifier iff `δ ∘ θᵢ = δ ∘ θⱼ` for all
`i, j`; most general iff every unifier `η` is `η' ∘ δ`; `mgu(Ξ)` is unique up to
renaming; `com(Ξ) = mgu(Ξ) ∘ θᵢ` is the common substitution.

**Lean** (`Subst.lean:122`, `Unification.lean:59–66`, `Spt.lean:15–60, 121`,
`General.lean:19`, `Engine.lean:271`).

```lean
def Subst.eqs (θ : Subst) : List (Exp × Exp) := (θ.dom.sort (· ≤ ·)).map fun v => (.var v, θ.f v)
def Unification.join (U) (θ η : Subst) : Option Subst := U.mgu (θ.eqs ++ η.eqs)
def Unification.joinAll (U) : List Subst → Option Subst
  | [] => some Subst.id | θ :: θs => (U.joinAll θs).bind fun η => U.join θ η
theorem Subst.solves_eqs_iff : Solves θ σ.eqs ↔ θ.comp σ = θ
theorem joinAll_absorbs : U.joinAll θs = some θ → ∀ σ ∈ θs, θ.comp σ = θ
theorem joinAll_typed / joinAll_idem : U.joinAll θs = some θ → θ.Typed / θ.Idem
theorem joinAll_mostGeneral : ρ.Typed → (∀ σ ∈ θs, σ.Idem) → (∀ σ ∈ θs, ρ.comp σ = ρ) →
    ∃ θ, U.joinAll θs = some θ ∧ ρ.IsInstance θ
theorem joinAll_spec (hidem : ∀ σ ∈ θs, σ.Idem) :
    (∀ θ, U.joinAll θs = some θ → θ.Typed ∧ θ.Idem ∧ AbsorbsAll θ θs) ∧
    ∀ ρ, ρ.Typed → AbsorbsAll ρ θs → ∃ θ, U.joinAll θs = some θ ∧ ρ.comp θ = ρ
```

The *join* is the draft's Definition 2.6: the most general unifier of the equations
`v = θᵢ(v)` of every member. A substitution solves `θ.eqs` exactly when it *absorbs*
`θ`, `ρ ∘ θ = ρ` (`solves_eqs_iff`); so the join `J` absorbs every member
(`joinAll_absorbs`), is typed and idempotent, and is most general among the typed
substitutions that absorb every member (`joinAll_mostGeneral`, for idempotent
members). Read against the paper: `J ∘ θᵢ = J = J ∘ θⱼ`, so `J` is a unifier of `Ξ` in
the paper's sense whose `com` is `J` itself; the paper's `mgu(Ξ)` with
`δ ∘ θᵢ = δ ∘ θⱼ` is never defined (§3, item 15). `joinAll` folds binary joins from the
right; nothing depends on the order but through `joinAll_spec`.

### §3.2 The SPT of an a-node, `T₀(T₁, …, Tₙ)`

**Paper.** For an a-node `a` whose children `e₁, …, eₙ` have non-empty `s(eᵢ)`, for
every tuple `Tᵢ ∈ s(eᵢ)` with `{θ(T₁), …, θ(Tₙ)}` unifiable by `δ`, the SPT
`T₀(T₁, …, Tₙ) = (δ(T₁), …, δ(Tₙ)) / (θ, a)` with `θ = com(θ(T₁), …, θ(Tₙ))` is added
to `s(a)`; `δ` propagates through the whole `Tᵢ`; non-replaceable variables are not
substituted.

**Lean** (`Search.lean:150–166`).

```lean
def State.tuples : List (List Entry) → List (List Entry)        -- one entry per child
def State.anodeEntries (U) (c : Consts) (j : ℕ) (a : ANode) (childEntries : List (List Entry)) : List Entry :=
  (tuples childEntries).filterMap fun tup =>
    match U.joinAll (a.sub :: tup.map (·.sub)) with
    | none => none
    | some θ =>
      let conds := (a.conds ++ tup.flatMap (·.conds)).map (Cond.apply θ)
      if conds.all (fun k => decide (k.Holds c)) then
        some { tree := .node j (tup.map (·.tree)), sub := θ, conds } else none
```

Two differences from the paper's formula. The join is of `θ_a` — the node's own
unifier `a.sub` — *with* the children's answers, not of the children's answers alone
(§3, item 14: the correction of `THEORY.md`; `Search.lean`'s header). And the
conditions: the node's pairs and the children's carried conditions, under the join;
an entry is made only if every one holds (§2, "Conditions"). The subtrees are not
substituted (`δ(Tᵢ)`): the tree keeps node numbers and the answer sits at the root
(§3, item 13).

### §3.2 The SPT of an e-node, `T₀(T₁)`

**Paper.** When a descendant a-node of `e` gets an SPT `T₁`, `s(e)` gets
`T₀(T₁) = T₁ / (θ, e)` with the same substitution; `s(e) = ⋃_{a ≺ e} {T₀(T₁) | T₁ ∈ s(a)}`.

**Lean.** `sptE` above: `s(e)` is the leaf entries together with the entries of every
a-child, the entries themselves, with no wrapping node; the union over `a ≺ e` is the
`flatMap` over `aChildren s i` (`Preserve.lean:672`, `mem_aChildren`). The
incremental "shift one step down to the root" of the paper is not modelled: the sets
are recomputed from the state (§3, item 12).

### Lemma 2 (an SPT defines one proof variant)

**Paper.** Each SPT `T` defines a unique proof variant `π(T)`; by induction on the
depth of `T`, since each SPT e-node has at most one direct descendant.

**Lean.** No statement: an `SptTree` is a variant by its type (one a-node per e-node),
and `SptTree.At` places it in the state. Two facts stand where the lemma would:
`anodes_nodup` (`Generality.lean:262`: a tree never visits an a-node twice) and
`sibling_disjoint` (line 220: the subtrees at two children share no e-node), both
from the chain of nodes above a node (`chain`, `mem_chain_of_at`, `le_of_mem_enodes`,
`StateInv.up_lt`, `up_children`).

### Theorem 1 (correctness)

**Paper.** For any SPT `T` with root `(θ, e)`, `π(T)` is a proof of `θ(e)`. Proof by
induction on the depth of `T`: at an a-node with `θ₀ = δ ∘ θᵢ` and the PVT unifier
`η` (`η(q₀) = e₀`, `η(qⱼ) = eⱼ`), the witness is `η' = θ₀ ∘ η`, since
`η'(q₀) = θ₀(e₀)` and `η'(qᵢ) = δ(θᵢ(eᵢ))`, which the children prove by monotonicity.

**Lean** (`Theorems.lean:27, 39`).

```lean
theorem soundness_valid (U db) (hwf : db.WF) (st) (n : ℕ) :
    ∀ E ∈ root n, Valid db (st.subst E.sub) (E.proof db (run n)) ∧ (E.proof db (run n)).expr = E.sub.apply st.concl
theorem soundness (U db) (hwf : db.WF) (st) (n : ℕ) :
    ∀ E ∈ root n, (∀ v ∈ (E.proof db (run n)).allVars db, st.dummies v.ty.sort = true) →
      IsProof db (st.subst (((E.proof db (run n)).closing db).comp E.sub)) ((E.proof db (run n)).close db)
```

"`π(T)` is a proof of `θ(e)`" is `soundness_valid`: the proof of a root entry `E` is
valid for the statement under its answer and proves `E.sub(st.concl)`. `soundness`
adds the closing: with every variable left turned into a distinct dummy, it is a proof
of the statement under `closing ∘ E.sub` (§2, "Closing").

**Uses.** `soundness_valid`: `run_inv`, `sptE_inv`, `valid_of_inv`, `StateInv.root_lt`.
`soundness`: `soundness_valid`, `close_isProof`.

**Sketch** (the argument of `Spt.lean` and `Preserve.lean`). The paper's induction
is split into an invariant and its preservation.

- `StateInv U db st s` (`Spt.lean:164`): every a-node `j` has `ANodeInv` for its
  assertion `A` (`Spt.lean:141`): `a.sub` is `U.mgu` of its equation (`is_mgu`),
  typed and idempotent, it unifies the parent's expression with the renamed
  conclusion (`unifies`), the children are the renamed hypotheses under it
  (`children`), a block made after the parent (`children_eq`), the parent's variables
  below the block (`parent_vars_lt`); and the state's numbering (`base_eq`,
  `stride_gt`, `fresh_gt`, `vars_lt`), the parent links (`up_lt`, `up_children`,
  `parent_lt_children`) and the attempt log (`tried_spec`, `expanded_tried`).
- `EntryInv s st i E` (`Spt.lean:132`): the tree sits at `i` (`At`); the answer
  `Absorbs` the tree (`Spt.lean:79`: `E.sub ∘ a.sub = E.sub` at every a-node, and at a
  leaf `E.sub(e) = E.sub(pₕ)`); typed, idempotent; `E.conds` are the tree's conditions
  under the answer, and they hold.
- Preservation: `init_inv`; `addNode_inv` (the new node has `ANodeInv`: the postulate
  gives `is_mgu`, `unifies`, typing, idempotence, and `range_sub` keeps the variables
  within the equation), `recordAt_inv`, `tryAssertion_inv`, `mark_inv` (with
  `StateInv.mono`, `ANodeInv.mono`), `expandNode_inv`, `expandAll_inv`, hence
  `run_inv`. For entries, `anodeEntries_inv`: the join absorbs every member
  (`joinAll_absorbs`), so by `Absorbs.of_comp` it absorbs every child's tree, and the
  conditions are those of the tree under the join (`Cond.apply_comp`); hence
  `sptE_inv` by induction on the fuel.
- `valid_of_inv` (`Spt.lean:339`): `shape_of_inv` by induction on `At`. At an a-node
  with answer `θ`, the step's substitution `stepSub db a θ` is the paper's
  `θ₀ ∘ η` (`η` = `a.sub` after renaming): `stepSub_apply` gives
  `stepSub(q) = θ(a.sub(q.rename base))`, so the conclusion is `θ(a.sub(concl'))` =
  `θ(a.sub(expr))` (`unifies`) = `θ(expr)` (absorption); each child's expression is
  `θ(a.sub(hyp'))`, the child's claim by induction; `stepSub_typed`. The leaf case is
  `Absorbs.leaf`. `conds_proofOf`: the proof's conditions are the tree's under `θ`,
  which `EntryInv.holds` says hold.
- `soundness`: `close_isProof` on the valid tree (§2, "Closing").

### Theorem 2 (generality)

**Paper.** If the algorithm finds an SPT `T` for the root of the PVT of
`a = (p₁, …, pₙ) / p₀`, then `π(T)` is more general than any proof `π'` of `a`
congruent to `π(T)`. Proof: the root of `T` is `(∅, p₀)`; by induction on depth, with
`e'ᵢ = ε(eᵢ)` for the children (copies with disjoint variables let one `ε` serve), the
chain `θ'(qᵢ) = ε(θᵢ(θ(qᵢ)))` gives `ε ∘ θᵢ = ε ∘ θⱼ`, so `ε ∘ θᵢ = ε' ∘ δ ∘ θᵢ` by the
mgu property, and `θ' = ε' ∘ θ₀ ∘ θ`.

**Lean** (`Theorems.lean:51`, `Generality.lean:723`).

```lean
theorem generality (U db) (hwf : db.WF) (st) (n : ℕ) :
    ∀ E ∈ root n, ∀ σ, σ.Typed → ∀ π, IsProof db (st.subst σ) π →
      π.Congruent (E.proof db (run n)) → π.IsInstance db (E.proof db (run n))
```

For every proof `π` of an instance `st.subst σ` of the statement that is congruent to
the proof of a root entry, `π` is an instance of that proof. The paper's "proof of
`a`" is the case `σ = id` (§3, item 17).

**Uses** (`generality'`). `run_inv`, `sptE_inv`, `matches_of_congruent`,
`assign_keys`, `anodes_nodup`, `assign_typed`, `build_typed`, `build_f_lt`,
`build_f_renamed`, `apply_congr_vars`, `sim`, `entry_mostGeneral`, `proofOf_subst`,
`StateInv.{root_expr, fresh_gt, stride_pos, stride_gt, anodes}`, `anodes_lt`.

**Sketch** (`Generality.lean`'s header). Instead of the paper's induction with one
`ε` per subtree, one substitution `ρ` on the whole state.

- `Matches s π T` (line 291): `π` follows the variant `T` — the same assertions at the
  steps, the same hypotheses at the leaves; `matches_of_congruent` gets it from
  congruence with `E.proof`.
- `assign π T` (line 333): the list `(j, θ_j^π)` of `π`'s step substitutions by the
  a-node of `T` they sit at; its keys are `T.anodes` (`assign_keys`), which are
  distinct (`anodes_nodup`) — this is the paper's "copies with disjoint variables":
  the blocks `baseOf j` keep the a-nodes' variables apart.
- `build db s σ L` (line 450): `ρ` is `σ` below `freshBase` (`build_f_lt`) and, at the
  renamed binder `renamed (baseOf j) x` of a node `(j, θ_j^π) ∈ L`, `θ_j^π(x)`
  (`build_f_renamed`, by `nodeOf`/`binderOf`, the inverse of the renaming); typed
  (`build_typed`).
- `sim` (line 537), the simulation lemma, by induction on `At`: under such a `ρ`,
  `π = proofOf db s ρ T` and `Absorbs s st ρ T`. At an a-node `j`, `ρ` solves the
  node's equation (the parent's expression under `ρ` is `π`'s expression there,
  `apply_congr_vars`; the renamed conclusion under `ρ` is `θ_j^π(concl)`,
  `apply_rename_eq`), so `ρ` is an instance of `a.sub` by `Unification.mostGeneral`
  and absorbs it (`Subst.comp_eq_of_instance`, idempotence); the step substitution is
  `stepSub db a ρ` by `Subst.ext`; the children by induction.
- `entry_mostGeneral` (line 644), by induction on the fuel: every typed `ρ` that
  absorbs `E.tree` is an instance of `E.sub`. At a leaf by `mostGeneral`; at an a-node
  `ρ` absorbs each child's answer (induction, `comp_eq_of_instance`) and `a.sub`, so
  it is an instance of the join (`joinAll_mostGeneral`). This is the paper's
  "`ε ∘ θᵢ = ε' ∘ δ ∘ θᵢ`".
- `generality'`: `ρ := build …`; `sim` gives `π = proofOf ρ T` and absorption;
  `entry_mostGeneral` gives `ρ = δ ∘ E.sub`; `proofOf_subst` (`General.lean:95`:
  `(proofOf θ T).subst δ = proofOf (δ ∘ θ) T`, with `stepSub_comp`) gives
  `π = (E.proof).subst db δ`.

### Theorem 3 (completeness)

**Paper.** If `(p₁, …, pₙ) / p₀` has a proof `π`, then at some moment `s(p₀)` contains
an SPT `T` with `π = θ(π(T))`. Proof: by Theorem 2 it suffices that `s(p₀)` gets an
SPT congruent to `π`, which "is clear from the character of the algorithm": every
expansion uses all variants, so all nodes corresponding to `π` appear.

**Lean** (`Theorems.lean:59`, `Completeness.lean:915`).

```lean
theorem completeness (U db) (hwf : db.WF) (st) (σ) (hσ : σ.Typed) (π : PTree) (hπ : IsProof db (st.subst σ) π) :
    ∃ n, ∃ E ∈ root n, π.Congruent (E.proof db (run n)) ∧ π.IsInstance db (E.proof db (run n))
```

`completeness'` gives `n = π.height + 1` (§3, item 18). The "clear from the character
of the algorithm" is the bulk of `Completeness.lean`.

**Uses** (`completeness'`). `treeOf_at`, `entry_exists`, `fuel_le`, `sptE_mono`,
`congruent_of_matches`, `conds_proofOf`, and generality's `sim`, `entry_mostGeneral`,
`proofOf_subst`, `anodes_nodup`, `assign_keys`, `build_*`; `run_inv`, `init_inv`,
`sptE_inv`.

**Sketch.**

- *What the rounds do.* `State.Le` (line 23): a state grows (nodes, marks, attempts
  kept); `run_le_of_le`. `expandAll_expanded_iff` (line 231): after a round exactly
  the nodes that existed before it are expanded; `tried_of_lt` (line 279): a node that
  exists after round `m` has tried every assertion by round `m + 1`; `anode_round`
  (line 379): every a-node was made in the round after its parent appeared, so its
  children exist after that round (`children_lt_of_parent`).
- *The variant of `π`.* `treeOf s π i` (line 567): at each step of `π` the a-node of
  the state at `i` for its assertion (`findNode`), at each leaf its hypothesis.
  `treeOf_at` (line 598), by induction on `Shape` with the round `m` and a local
  substitution `ρ`: the attempt `(i, a, B)` is in `tried` (`tried_of_lt`); if it had
  no node, `tried_spec` says the equation at base `B` has no typed solution — but
  `override ρ B A θ^π` (line 494: `ρ` overridden at the renamed binders by `π`'s step
  substitution) solves it (`override_solves`, `override_typed`), contradiction. So
  the node exists; the children's expressions are `π`'s children's, and the induction
  continues with `ρ' = override …`, which absorbs `a.sub` by `mostGeneral`. Result:
  `(treeOf π 0).At (run n) 0` and `Matches (run n) π (treeOf π 0)` for
  `n = height + 1`.
- *The global substitution*, as in generality: `build` from `assign π T`; `sim` gives
  `π = proofOf ρ T` and `Absorbs ρ T`.
- *The conditions hold under `ρ`*: they are the conditions of `π` (`conds_proofOf`),
  and `π` is valid.
- `entry_exists` (line 754), by induction on `At`: a tree that a typed `ρ` absorbs,
  whose conditions hold under `ρ`, has an entry with that tree at every fuel
  `≥ T.fuel`. At a leaf by `mostGeneral`; at an a-node, entries for the children
  (induction), their tuple (`mem_tuples_of_index`), the join exists and `ρ` is its
  instance (`entry_mostGeneral`, `joinAll_mostGeneral`), and every condition holds
  under the join because it holds under its instance `ρ` (`holds_of_instance`,
  `General.lean:72`) — this is the rule of `DESIGN.md`, "a tree may be discarded only
  when a condition is violated for every instantiation", in the form the proof needs.
- `fuel_le` (line 470): `T.fuel + i ≤ enodes.size`, so the entry is in `rootEntries`
  (`sptE_mono`); `congruent_of_matches` gives congruence; `entry_mostGeneral` and
  `proofOf_subst` give the instance, as in generality.

### Corollary 1

**Paper.** The set of provable assertions of a pure deductive system is computably
enumerable.

**Lean.** Not stated. `run`, `rootEntries` and `Unify.postulate` are computable
(`lake exe ref-search` runs them), and `completeness` plus `soundness` are the content;
the corollary itself has no declaration (§3, item 23).

## 2. What THEORY.md adds to the paper

The same columns, shorter: these have no paper counterpart, so the "paper statement"
is the sentence of `THEORY.md` or `DESIGN.md` that asks for them.

### Conditions on bound variables (`DESIGN.md`, "Where MM0 differs", condition 2)

**Asked.** For an assertion, the pairs `D(A) = {(x, v) : x bound, v another binder,
not (v regular and x among v's declared dependencies)}`; a substitution satisfies
`(x, v)` when the name `θ(x)` does not occur in `θ(v)`, "occurs" counting the
declared dependencies of the statement's constants. A tree may be discarded only
when a condition is violated for every instantiation.

**Lean** (`Deduction.lean:68–92`, `Term.lean:179`, `Search.lean:86`).

```lean
def SatPair (c : Consts) (θ : Subst) (p : Var × Var) : Prop := θ.f p.1 ∉ c.names (θ.f p.2)
abbrev Cond := Exp × Exp;  def Cond.Holds (c) (k : Cond) : Prop := k.1 ∉ c.names k.2
def Cond.apply (θ) (k : Cond) : Cond := (θ.apply k.1, θ.apply k.2)
def stepConds (db) (a : ℕ) (θ : Subst) : List Cond := A.pairs.map fun p => (θ.f p.1, θ.f p.2)
def State.nodeConds (A : Assertion) (b : ℕ) (θ : Subst) : List Cond   -- the pairs renamed, under θ_a
def SptTree.conds (s) : SptTree → List Cond                            -- of every a-node on the tree
```

A condition travels as a pair of expressions (name, expression) and is re-judged
under every substitution; `Entry.conds` are the tree's conditions under the answer,
every one holding (`EntryInv.conds`, `EntryInv.holds`); `anodeEntries` drops a tuple
whose join violates one. **The rule**: `holds_of_instance` (`General.lean:72`): if
`k` holds under `δ ∘ θ` it holds under `θ` — contrapositive, a condition that fails
under the most general answer fails under every instance, so dropping the entry
loses no proof; `mem_names_apply` (a typed substitution keeps an occurrence) is the
whole of it. `conds_name` (`Closing.lean:110`): in a valid tree of a well-formed
database the name of every condition is a name, from `pairs_bound` and typing.
`conds_subst`: the conditions of `δ(T)` are `T`'s under `δ`.

### Closing (`THEORY.md`, decision 8)

**Asked.** Every variable a proof leaves becomes a dummy of its sort, which MM0
allows for every sort that is neither `strict` nor `free`; the step is apart from the
search.

**Lean** (`Deduction.lean:328–342`, `Closing.lean`).

```lean
def Var.dummy (v : Var) : Var := ⟨v.code, ⟨v.ty.sort, true⟩⟩       -- injective (Var.code_injective)
def PTree.closing (db) (T : PTree) : Subst   -- every v ∈ T.allVars ↦ .var v.dummy
def PTree.close (db) (T : PTree) : PTree := T.subst db (T.closing db)
theorem close_isProof (hwf : db.WF) (st) (θ) (T) (hv : Valid db (st.subst θ) T) (he : T.expr = θ.apply st.concl)
    (hd : ∀ v ∈ T.allVars db, st.dummies v.ty.sort = true) :
    IsProof db (st.subst ((T.closing db).comp θ)) (T.close db)
```

**Uses.** `Shape.subst` (the shape under the closing), `holds_closing` (a condition
keeps holding: the dummies are fresh and distinct, `vars_closing_apply`,
`consts_closing_apply`, `Var.dummy_injective`), `conds_name`, `allVars_close` (the
closed tree's variables are the dummies), `closing_typed`, `Statement.subst_subst`.
**Sketch.** Validity by monotonicity; a condition `(y, e)` with `y` a variable of the
tree becomes `(y', e')` with `y'` fresh, and `y' ∈ names(e')` would need `y ∈ vars e`,
which the condition excludes; with `y` a constant nothing changes. The root is
`closing(θ(concl))`, and every variable of the closed tree is a dummy name of an
allowed sort.

### Metavariables in the statement (decision 7)

No declaration of its own: `Statement.hyps`/`concl` may contain `Exp.var`, the root
e-node is an e-node like any other, and every theorem speaks of `st.subst E.sub` or
`st.subst σ`. With no metavariables `st.subst σ = st` for every `σ` (constants are
untouched), which recovers the paper's statements.

### The unifier and the postulate discharged (milestone 7)

**Asked.** The postulate (`Unification`) holds for sorted first-order terms.

**Lean** (`Unify.lean`).

```lean
def Unify.go : Problem → Subst → Option Subst   -- Robinson, one equation at a time, binding applied to the rest
def Unify.mgu (E : Problem) : Option Subst := go E Subst.id
structure Unify.Inv (V : Finset Var) (E : Problem) (θ : Subst) : Prop   -- typed; images avoid dom; dom apart from E; within V
theorem Unify.go_sound : Inv V E θ → go E θ = some θ' → Solves θ' E ∧ θ'.comp θ = θ' ∧ Inv V [] θ'
theorem Unify.go_complete : Inv V E θ → ρ.Typed → Solves ρ E → ρ.comp θ = ρ → ∃ θ', go E θ = some θ' ∧ ρ.IsInstance θ'
def Unify.postulate : Unification     -- Unify.lean:800, no sorry
```

**Uses** (`postulate`). `go_sound`, `go_complete`, `Inv.init`, `Inv.{typed, sep,
dom_sub, range_sub}`, `idem_of_sep`, `Subst.comp_id`. **Sketch.** Recursion on
(number of variables, size of the problem) (`measure_bind`, `measure_drop`,
`measure_zip`); a binding `bind v e θ` when `v.ty.fits e.ty`, `v ∉ e.vars`, and a
name for a name type keeps `Inv` (`Inv.bind`); `bind_sound`/`bind_complete` move a
solution across a binding step; the failing branches contradict a typed solution (the
occurs check by `size_lt_of_mem_vars_app`). Idempotence from the invariant's
separation (`idem_of_sep`). Of two variables that fit each other the one with the
larger number is bound (`go`, since milestone 15), which is `Oriented` below.

### The engine lemmas (milestone 5): restriction, key, settled

**Asked.** The arguments the production engine rests on where it does more than the
reference engine: a proof goes up with its substitution restricted to the visible
variables (`DESIGN.md`, change 5); one proof per key; conditions settled and
forgotten.

**Lean** (`Engine.lean`).

```lean
def Subst.Mentions (θ : Subst) (v : Var) : Prop        -- moved, or in an image
def visible (st) (s : State) (c : ℕ) : Finset Var      -- vars of e-node c's expression and of the statement
def State.InBlock (s) (j : ℕ) (v : Var) : Prop         -- v is a renamed binder of a-node j
def ApartBelow (θ) (V) (η) : Prop                      -- η mentions nothing θ moves outside V
theorem joinAll_mentions : U.joinAll θs = some θ → θ.Mentions v → ∃ σ ∈ θs, σ.Mentions v
theorem entry_mentions : E ∈ sptE U st s fuel i → E.sub.Mentions v →
    v ∈ st.vars ∨ v ∈ s.enodes[i]!.expr.vars ∨ ∃ j ∈ E.tree.anodes, s.InBlock j v
theorem joinAll_restrict_exists  : … → ((∃ J, joinAll (L₁ ++ θ :: L₂) = some J) ↔ ∃ J', joinAll (L₁ ++ θ.restrict V :: L₂) = some J')
theorem joinAll_restrict_instance : … → J is an instance of J', and J' of J on every v with (v ∈ θ.dom → v ∈ V)
theorem joinAll_key / joinAll_key_holds : θ₁.restrict V = θ₂.restrict V → the two joins exist together, agree up to
    instance each way on the visible variables, and judge a condition on them alike
theorem settled : ¬ J.Mentions y → (Cond.Holds c (Cond.apply J (.var y, e)) ↔ Cond.Holds c (.var y, e))
theorem spt_restrict / spt_key / spt_settled   -- the three, at an a-node of the reference engine's SPT sets
```

**Sketch.** `joinAll_spec` says what a join is semantically; `Subst.extend ρ θ V`
(line 182) extends an absorbing substitution of the restricted member to one of the
full member below `V`, which gives existence and the two instances. At an a-node the
hypotheses of these lemmas hold (`spt_join_hyps`): a child's entry mentions, beyond
the visible variables, only the blocks of its tree (`entry_mentions`), those blocks
come after the node (`anode_lt_of_child`) and are apart from the other children's
trees (`sibling_trees_disjoint`, `below_not_mentioned`), so no other member of the
join mentions them. The finding on the way (`THEORY.md`, milestone 5): the visible
variables include the statement's metavariables.

### The keyed engine (milestones 12–16)

**Asked.** A third engine with the production engine's three ideas over the model's
data, and two theorems: every keyed entry is the restriction of a reference entry
with the same pending conditions, and every reference entry has a keyed entry with
its key.

**Lean** (`Keyed.lean`, `KeyedLemmas.lean`, `KeyedCorr.lean`, `Oriented.lean`,
`KeyedExact.lean`, `Theorems.lean:104–170`).

```lean
structure KEntry where tree : SptTree; sub : Subst; conds : List Cond    -- sub restricted to visible vars; pending conds
def judgeK (c : Consts) (st) (e : Exp) (J : Subst) (k : Cond) : Option Bool   -- none violated / some false settled / some true pending
def anodeK … : List KEntry        -- join of θ_a with the children's restricted subs; judged; restricted; dedupKeys
def keyedE (U st) (s) : ℕ → ℕ → List KEntry;  def keyedRoot (U st) (s) : List KEntry
-- without pairs, up to instance each way (milestones 13–14):
theorem keyed_sound_np    : … db.NoPairs → ∀ K ∈ keyedE U st s fuel i, ∃ E ∈ sptE U st s fuel i,
    K.tree = E.tree ∧ K.conds = [] ∧ SameOn (visible st s i) K.sub E.sub
theorem keyed_complete_np : … db.NoPairs → ∀ E ∈ sptE …, ∃ K ∈ keyedE …, SameOn (visible st s i) K.sub E.sub
-- oriented unifiers (decision 16):
def Var.before (r v : Var) : Prop;  def Subst.Oriented;  def Unification.Oriented
theorem oriented_unique : σ.Idem → σ'.Idem → σ.Oriented → σ'.Oriented → σ.IsInstance σ' → σ'.IsInstance σ → σ = σ'
theorem Unify.postulate_oriented : Unify.postulate.Oriented
-- exactly (milestone 16):
theorem joinAll_restrict_eq : U.Oriented → … → joinAll (L₁ ++ θ :: L₂) = some J → joinAll (L₁ ++ θ.restrict V :: L₂) = some J' →
    ∀ v, (v ∈ θ.dom → v ∈ V) → J.f v = J'.f v
structure KEq (st s i) (K : KEntry) (E : Entry) : Prop   -- K.sub = E.sub.restrict (visible st s i); K.conds = E.conds filtered to pending
theorem keyed_sound_ex    : U.Oriented → … → ∀ K ∈ keyedE …, ∃ E ∈ sptE …, K.tree = E.tree ∧ KEq st s i K E
theorem keyed_complete_ex : U.Oriented → … → ∀ E ∈ sptE …, ∃ K ∈ keyedE …, KEq st s i K E
-- at the root (Theorems.lean): keyed_soundness, keyed_completeness; _np; _postulate for Unify.postulate
```

**Sketch.** `KInv` (`KeyedCorr.lean:16`) and `keyedE_inv`: a keyed entry's
substitution moves only visible variables and mentions beyond them only blocks of its
tree. `Member` (line 156) is what both engines' members have in common at a join, and
`restrict_chain` (line 388) replaces the full members by their restrictions one at a
time, each step by `joinAll_sameOn` (`KeyedLemmas.lean:164`, from `joinAll_inst`);
`dedupKeys_spec` picks the representative. For the exact version, `oriented_unique`
makes the choice of which of two equal variables is kept no longer free, so
`restrict_chain_eq` gives equality on the undropped variables, and `Joined`
(`KeyedExact.lean:633`) packages the two joins: `Joined.restrict_eq`,
`isPending_eq`, `all_hold_iff`, `pending_eq` (the node's and the children's
conditions are judged alike, `cond_var_not_dropped`; a condition settled at a child
stays settled, `settled_at_parent`, `settled_child`).

### Definitions (milestones 8–11)

**Asked.** Definitions with MM0's conversion judgment (`mm0.mm0`'s `VerifyConv`), the
engine unchanged over a database extended by the judgment as rules, and the link
between the two kinds of proof by two translations.

**Lean** (`Defs.lean`, `Rules.lean`, `ToD.lean`, `OfD.lean`, `Theorems.lean:68–96`).

```lean
structure Def where term : ℕ; ty : Ty; args dummies : List Var; value : Exp;   structure Def.WF
inductive CTree | refl (e) | symm (k) | trans (k₁ k₂) | cong (f t ks) | unfold (d es zs)   -- CExpr
inductive CValid (db sig c) : CTree → Exp → Exp → Prop                                -- VerifyConv
inductive DTree | hyp (h e) | step (e a θ cs) | conv (e k t)                            -- VExpr with VConv
inductive DShape;  def DValid;  def IsProofD (db sig st) (D : DTree) : Prop
theorem PTree.isProofD_ofP : IsProof db st T → IsProofD db sig st T.ofP
structure Language;  def Database.withConv (L) (db) : Database   -- the file's assertions, then Rules.all
def PTree.toC (L db) : PTree → CTree;  def PTree.toD (L db) : PTree → DTree
theorem toD_isProof (hL : L.WF db st) (hdefs : db.DefsWF) : IsProof (db.withConv L) st T → IsProofD db L.sig st (T.toD L db)
theorem soundness_defs … : ∀ E ∈ root n over db.withConv L, (dummies ok) → IsProofD db L.sig (st.subst (closing ∘ E.sub)) ((E.proof).close.toD L db)
def CTree.NoTrans;  structure DTree.Fits (L db st) (D : DTree);  def Consts.NameDeps
def CTree.toTree / toTreeR : … → PTree;  def DTree.toP (L db) : DTree → PTree
theorem DTree.toP_isProof (hL) (hdefs) (hnd : st.consts.NameDeps) : IsProofD db L.sig st D → D.Fits L db st → IsProof (db.withConv L) st (D.toP L db)
theorem completeness_defs … : ∃ n, ∃ E ∈ root n over db.withConv L, (D.toP L db).Congruent (E.proof) ∧ (D.toP L db).IsInstance (E.proof)
```

**Sketch.** `toD_isProof` is `proof_valid` (a valid tree whose expression is no
judgment is a valid MM0 proof, by the sort at the root: `Language.WF` says the
judgment sort is none of the file's) over `cert_valid` (a valid rule tree whose
expression is a judgment is a valid certificate: `congList_valid` for congruences,
`Def.inst_apply` and `nodup_map_of_laterPairs` for unfoldings), with `conds_toD`,
`cert_vars`, `proof_vars`; `withConv_WF` makes the extended database well-formed.
`DTree.toP_isProof` is `DTree.toP_valid` over `CTree.toTree_valid`/`toTreeR_valid`
(the two directions of a certificate without transitivity, decision 14; `congStep_ok`,
`unfoldStep_ok`, substitutions from association lists `Subst.ofAssoc`). The two root
theorems are `soundness` and `completeness` over `db.withConv L` composed with the
translations.

## 3. Where the Lean differs from the paper

Each item: what the paper has, what the Lean has, where, and — when the docs say —
why. The ones marked **judge** are where the paper's text and the Lean read
differently and the paper may be the one to change, or the Lean; the others are
choices of the formalization that the paper does not contradict.

1. **Grammar versus trees; no well-formedness hypothesis** (§2.1; `Term.lean`).
   The paper's expressions are words of a context-free unambiguous grammar; the Lean's
   are trees `Exp`, unambiguous by construction. The theorems assume nothing about the
   shape of expressions: `Signature.WF` is defined (`Term.lean:206`) and used by no
   declaration of the theory. So `soundness` etc. hold for ill-formed trees too —
   validity in the model does not include MM0 well-formedness, which is the verifier's
   track (`VERIFIER-THEORY.md`) and, for the translations with definitions,
   `Language.Good` (`OfD.lean:165`).
2. **Typing of substitutions** (§2.2; `Ty.fits`, `Term.lean:22`). The paper allows
   `v : n ↦ e : m` whenever `n → m` is derivable in `G`, a general subtype order. The
   Lean has exactly one subtype per sort: names of sort `s` within `s` (`DESIGN.md`,
   condition 1); `Ty.fits` is "same sort, and a name type only to a name type".
3. **Non-replaceable variables are constants; metavariables** (§3.1; `Exp.const`,
   `Consts`, `Statement`). The paper flags the variables of e-nodes replaceable or
   not, the statement's variables being non-replaceable; the Lean makes the
   statement's variables constants, with the declared dependencies the conditions
   need, so no flag exists and nothing can bind them. The statement may also contain
   variables (metavariables, decision 7), which the paper has not; so every theorem
   is about `st.subst σ`, and `generality`/`completeness` quantify over the instance
   `σ`.
4. **Unification is two-sided and unique up to renaming** (§2.2; `Unification.lean`).
   **Judge.** The paper defines "e₁ unifies with e₂" as `e₂ = θ(e₁)`, one-sided
   ("non-symmetric … if a unifier exists, it is unique"), and uses that definition at
   both places the algorithm unifies: forking an e-node `e` with the assertions "which
   propositions unify with `e`" (§3.1), and closing an e-node by a premise `pᵢ` that
   "unifies with `e` (note, that here variables in `e` are also non-replaceable!)"
   (§3.2). The Lean unifies two-sidedly at both places: `tryAssertion` takes
   `U.mgu [(expr, A.concl.rename base)]`, `leafEntries` takes `U.mgu [(e, st.hyps[h]!)]`,
   with `Solves σ [(a, b)] ↔ σ(a) = σ(b)`; a most general unifier is unique only up to
   renaming (`mostGeneral` gives `IsInstance`), which is why generality and the keyed
   correspondence speak of instances each way (`SameOn`) until the oriented postulate
   restores uniqueness (`oriented_unique`). The two readings are not equivalent on the
   nodes below the root: an inner e-node carries the fresh (replaceable) variables of
   the assertions above it. With `e = ?x → ?y` (`?x`, `?y` fresh from above) and an
   assertion `⊢ a → a`, no `θ` has `θ(a → a) = ?x → ?y`, so the one-sided rule makes no
   node, while a proof with `?x = ?y = p` exists; the Lean's `mgu` binds `?x` to `?y`
   and makes the node. Likewise at a leaf: `e = a → ?z` against the premise `a → b`.
   The Lean's choice follows Russell as `DESIGN.md` reads it ("Where the code does
   something else than the source", change 2: in `ruDoUnifyIndex` a variable of
   either side is bound, the more general to the more special) and is what
   `completeness` proves; whether the paper's wording intends one-sided
   matching at these two places, or means two-sided unification with the
   *statement's* variables fixed, is for the paper's author to say. If the former,
   the paper's Theorem 3 needs the Lean's rule.
5. **Leaves name their hypothesis; congruence compares it** (§2.3; `PTree.hyp`,
   `PTree.Congruent`). The paper's leaf is an e-node that "coincides with some
   premise"; the Lean's leaf is `hyp h e` with `e = st.hyps[h]!` (`Shape.hyp`), and
   two trees are congruent only with the same `h` at corresponding leaves, where the
   paper has "no restrictions on e-nodes". Generality and completeness are stated
   with this stronger congruence (`generality` assumes it, `completeness` provides
   it). Why: `Matches` needs to know which hypothesis a leaf used
   (`matches_of_congruent`).
6. **Step substitutions live on the binders** (§2.3; `PTree.subst`, `Shape.step`).
   Component-wise application in the paper gives the a-node `(a, δ ∘ θ)`; the Lean
   gives `(a, (δ ∘ θ).restrict (binders db a))` and `Shape.step` asks
   `θ.dom ⊆ A.vars`. So `PTree.IsInstance` and `Congruent` are about normalized
   trees; `stepConds_restrict` shows the conditions do not see the difference. Why:
   equality of trees in `sim` and `proofOf_subst` needs a canonical substitution per
   step (`THEORY.md`, milestone 4: "step substitutions stay on the binders").
7. **"Proof" always closes its leaves; a proof of the statement is closed up to
   dummies** (§2.3; `Shape`, `IsProof`). The paper separates "proof" (every
   transition is an instance of its assertion) from "proof of `s`" (root `p₀`, leaves
   premises); Theorem 1 is about the former. The Lean has no open proof tree: `Shape`
   already requires every leaf to be a hypothesis of the statement, so
   `soundness_valid` says more than Theorem 1 (the leaves are hypotheses of
   `st.subst E.sub`). And `IsProof` requires every variable of the tree to be a name
   of a sort that admits dummies, which the paper does not ask (it has no notion of
   dummy); `soundness` therefore has the hypothesis `∀ v ∈ allVars, st.dummies
   v.ty.sort` and the closing (item 22).
8. **Monotonicity needs more and gives less** (Lemma 1; `Shape.subst`). The Lean
   lemma needs `db.WF` (the binders cover the assertion, so restriction to them is
   harmless) and a *typed* `δ`; and it is about `Shape` only. The conditions are not
   monotone — `δ` may make a name occur — and are handled the other way round:
   `holds_of_instance` (a condition holding under an instance holds under the
   original), which is what completeness needs.
9. **The conditions on bound variables are in** (the paper's last page sets them
   aside). Everywhere: `Assertion.pairs`, `Cond`, `stepConds`, `ANode.conds`,
   `Entry.conds`, the filter in `anodeEntries`, `CondsHold` in `Valid`, `holds_closing`,
   `holds_of_instance`; and they are what the engine lemmas and the keyed engine are
   mostly about. The paper's remark "the only thing necessary to track … are these
   restrictions, which are not difficult to check" is `DESIGN.md`'s rule and
   `holds_of_instance` (§2, "Conditions").
10. **Fresh variables by arithmetic** (§3.1; `baseOf`, `renamed`, `Exp.rename`). The
    paper replaces the free variables of an assertion by fresh ones; the Lean renames
    the binders of the `j`-th a-node by `freshBase + j·stride + id`, so that a
    variable tells its node (`nodeOf`, `binderOf` in `Generality.lean:399`), which the
    global substitution `build` of generality relies on.
11. **Breadth-first rounds and an attempt log** (§3.1; `run`, `State.tried`). The
    paper's PVT grows by "steps of expansion" in no fixed order ("at some moment");
    the Lean expands every unexpanded e-node once per round. The log `tried`
    (`(i, a, B)`: node, assertion, base) exists only so that the completeness proof
    can know that an expanded node tried every assertion at a known base
    (`StateInv.tried_spec`, `expanded_tried`, `tried_of_lt`).
12. **`s(e)` has no wrapper node and is recomputed** (§3.2). The paper puts
    `T₀(T₁) = T₁ / (θ, e)` into `s(e)` for every `T₁ ∈ s(a)`, `a ≺ e`, and builds the
    sets incrementally as new SPTs appear. The Lean's `sptE` is the leaf entries plus
    the a-children's entries themselves, a function of the state and a depth
    (`fuel`); `rootEntries` uses the number of e-nodes as depth (`fuel_le`). The
    incremental update is not modelled; `sptE_mono` (more fuel, more entries) is
    what replaces it in the completeness proof.
13. **No substitution inside an SPT; `π(T)` takes the answer** (§3.2; `SptTree`,
    `Entry`, `proofOf`). The paper labels every SPT node with a substitution and
    applies `δ` "through the whole trees `Tᵢ`" when joining; the Lean's `SptTree`
    holds node numbers only, `Entry.sub` is the answer at the root, and the proof tree
    is `proofOf db s θ T` with `θ` applied at every node (so `π(T)` in the paper is
    `proofOf db s E.sub E.tree`). The substitutions of inner SPT nodes can be
    recomputed (`treeSub`, `theory/Main.lean`) but are not stored.
14. **The node's unifier is a member of the join** (§3.2; `anodeEntries`). The known
    correction: the paper's `θ = com(θ(T₁), …, θ(Tₙ))` joins the children's answers
    only; the Lean joins `a.sub :: tup.map (·.sub)`. `THEORY.md` ("The model") gives
    the example: a goal `?g` proved by `¬¬x' / x'` — the child's answer binds `x'`, and
    only `θ_a` says `?g ↦ ¬¬x'`. The paper's correctness proof uses the node's
    unifier `η` in the witness `θ₀ ∘ η` without it being in `θ₀`; the Lean's
    `stepSub db a θ = θ ∘ a.sub ∘ rename` is that witness with `θ` absorbing `a.sub`
    (`Absorbs.node`). Russell composes the node's substitution with the join
    (`ruAddProof`, `russell-flow/src/ru/prover/core/proofs.flow:219`,
    `ruCompose(ruPropSubsForced(prop).first, unif.sub)`), which `THEORY.md`
    (milestone 6) found is the join only when nothing below binds what the unifier
    binds; the production engine now joins.
15. **The join is not the paper's `mgu(Ξ)`** (§3.2; `Unification.join`,
    `joinAll_spec`). **Judge.** The paper's unifier of `Ξ` is a `δ` with
    `δ ∘ θᵢ = δ ∘ θⱼ`, most general among such, and the answer is `com(Ξ) = mgu(Ξ) ∘ θᵢ`.
    The Lean defines the answer directly as the most general unifier of the union of
    the equational forms `v = θᵢ(v)`, i.e. the most general typed `J` with `J ∘ θᵢ = J`
    for every `i` (absorption; `solves_eqs_iff`, `joinAll_spec`), and never defines
    `δ`. Such a `J` is a paper-unifier with `com = J`; conversely, the paper's `com`
    absorbs every `θᵢ` only if `com ∘ θᵢ = com`, i.e. `δ ∘ θ₁ ∘ θᵢ = δ ∘ θ₁`, which the
    paper's definition does not give without idempotence of the members and some
    disjointness. The Lean asks the members to be idempotent (`joinAll_mostGeneral`'s
    `∀ σ ∈ θs, σ.Idem`; the entries' answers are, `EntryInv.idem`) and the
    competitors to be typed. Whether the two notions agree for the substitutions that
    arise (idempotent, with the fresh variables apart) is not stated anywhere; the
    draft's Definition 2.6 and Lemma 2.7 are the Lean's reference, not the paper.
16. **Theorem 1: invariants instead of induction on the SPT, and more in the
    conclusion** (`soundness_valid`, `soundness`). The conclusion adds: the witness is
    typed and on the binders, the leaves are hypotheses of the instance, the
    conditions hold, and (after closing) the tree is a proof of the statement in
    MM0's sense. The proof is an invariant of the state (`StateInv`, 16 fields) and of
    an entry (`EntryInv`), preserved by every operation of the engine
    (`Preserve.lean`), plus `valid_of_inv`; the paper's induction on the depth of `T`
    is `shape_of_inv`'s induction on `SptTree.At`.
17. **Theorem 2: the root entry has an answer; the proof is of an instance; one
    global substitution** (`generality`). The paper says the root of `T` is
    `(∅, p₀)` "because all variables in `p₀` are fixed". The Lean's root entry has
    `E.sub`, which binds the fresh variables of the tree and the metavariables of
    the statement; on the constants it does nothing. The theorem is for a proof `π`
    of `st.subst σ` with `σ` typed; with no metavariables this is the paper's. The
    paper's "taking copies of the subtrees with disjoint variables, we can assume all
    `εᵢ` the same" is replaced by the single `build` (`Generality.lean:450`) over the
    blocks of item 10, whose well-definedness is `anodes_nodup`.
18. **Theorem 3: an explicit bound, and a proof** (`completeness'`). The paper proves
    completeness in four lines; the Lean needs `n = π.height + 1` rounds and
    `Completeness.lean`'s 980 lines: the growth of the state (`State.Le`), what a round
    expands, when an a-node was made (`anode_round`), the variant `treeOf` of a proof,
    and `treeOf_at`, whose key step is that a missing node would mean the recorded
    attempt had no unifier while `override` (the step's substitution written at the
    fresh binders) is one. The conditions, absent from the paper, need
    `holds_of_instance` in `entry_exists`.
19. **Name types get names** (`Subst.Typed`). Beyond `Ty.fits`, a typed substitution
    gives a variable of a name type a variable or a constant, never an application
    (`Exp.IsName`): MM0's bound variables stand for variables only (`DESIGN.md`,
    condition 1). The paper's typing has no such clause.
20. **The unifier is idempotent** (`Unification.idem`). The paper does not say; the
    Lean needs it for absorption (`Subst.comp_eq_of_instance`: an instance of an
    idempotent substitution absorbs it) throughout.
21. **Most general among typed solutions** (`Unification.mostGeneral`). The paper's
    unifier is most general among all; the Lean's among typed ones, and
    `none_iff` says `mgu E = none` exactly when no typed solution exists. Every `σ`,
    `ρ` the theorems quantify over is typed.
22. **Sorts without dummies are outside the model** (`IsProof`, decision 8). `IsProof`
    demands every leftover variable to be a name of a sort with `st.dummies = true`;
    MM0 forbids dummies of `strict`/`free` sorts, where the production engine tries a
    term or a variable of the theorem instead. The Lean theorems say nothing about
    those (`soundness`'s hypothesis `hd`); the paper has no such notion at all.
23. **Corollary 1 is not stated.** Computable enumerability of provability would
    follow from `run`/`rootEntries` being computable and `completeness`, but no
    declaration says so.
24. **Additions the paper has not** (see §2): the conditions and their three
    judgments, the closing, the unifier with its proof, the engine lemmas
    (restriction, key, settled), the keyed engine and oriented unifiers, and
    definitions with MM0's conversion judgment and its two translations. None of
    these changes the paper's theorems; items 9, 14 and 15 are where they touch them.

## 4. The lemma dependency graphs

For each of the three theorems: every theorem its proof rests on, transitively,
restricted to the theory's own declarations (Mathlib and core are left out), with
definitions, structure fields' projections and constructors not counted as lemmas.
"Lemmas" below means `theorem` declarations; a structure field used as a lemma
(`StateInv.up_lt`) counts. The pictures are in `docs/correspondence/`:

| Theorem | lemmas in the closure | of them in the "backbone": a docstring, a name in `THEORY.md`, or a name in the sketches above | pictures |
|---|---:|---:|---|
| `soundness` | 141 | 54 | [backbone](correspondence/soundness_backbone.svg), [full](correspondence/soundness_full.svg) |
| `generality` | 133 | 49 | [backbone](correspondence/generality_backbone.svg), [full](correspondence/generality_full.svg) |
| `completeness` | 194 | 69 | [backbone](correspondence/completeness_backbone.svg), [full](correspondence/completeness_full.svg) |

In a backbone picture an edge `A → B` means the proof of `A` uses `B` directly or
through lemmas that are not in the backbone (plumbing: `getElem!` arithmetic,
`List` facts, the projections of invariants); nodes are grouped by file. The three
closures share their lower half: the model (`Subst.apply_comp`, `comp_assoc`), the
invariants of `Spt.lean`, and all of `Preserve.lean` (39 lemmas, `run_inv` and
`sptE_inv` with their preservation chain). What differs is above: the closing for
soundness, `Generality.lean` for generality, and `Completeness.lean` on top of
`Generality.lean` for completeness.

### Which lemmas carry weight

Fan-in is the number of lemmas in the three closures that use the lemma directly;
"own closure" is the number of lemmas its own proof rests on — how much of the
development a change to it would touch.

| lemma | file | fan-in | own closure | role |
|---|---|---:|---:|---|
| `Subst.apply_comp` | Subst | 12 | 4 | `(θ ∘ η)(e) = θ(η(e))`; every witness computation |
| `StateInv.anodes` | Spt | 16 | 0 | every a-node has `ANodeInv`; the entry point to every fact about a node |
| `ANodeInv.children`, `.assertion` | Spt | 8 each | 0 | what the children of a node are; which assertion |
| `StateInv.up_lt` | Spt | 6 | 0 | the node above is earlier: the chains of generality, `anodes_nodup` |
| `Subst.comp_eq_of_instance` | General | 5 | 7 | an instance of an idempotent substitution absorbs it; the bridge from `mostGeneral` to `Absorbs` |
| `Unification.mostGeneral` | Unification | 5 | 0 | the postulate's one strong clause; used by `sim`, `treeOf_at`, `entry_mostGeneral`, `entry_exists`, `joinAll_mostGeneral` |
| `run_inv` / `sptE_inv` | Preserve | 4 each | 66 / 30 | the invariants hold after any run / for every entry |
| `anodeEntries_inv` | Preserve | 1 | 26 | the join step keeps `EntryInv` (absorption, conditions) |
| `valid_of_inv` | Spt | 1 | 36 | invariants ⟹ valid proof; Theorem 1's induction |
| `close_isProof` | Closing | 1 | 44 | the closing is a proof of the statement |
| `joinAll_mostGeneral` | General | 2 | 13 | the join is most general among absorbing substitutions; both Theorem 2 and 3 |
| `sim` | Generality | 2 | 26 | a proof along a variant is `proofOf ρ T` and `ρ` absorbs `T` |
| `entry_mostGeneral` | Generality | 3 | 36 | an entry's answer is most general among what absorbs its tree |
| `anodes_nodup` | Generality | 2 | 17 | a tree never visits an a-node twice (well-definedness of `build`) |
| `treeOf_at` | Completeness | 1 | 126 | the variant of a proof is in the graph after `height + 1` rounds |
| `entry_exists` | Completeness | 1 | 46 | an absorbed tree with holding conditions has an entry |
| `holds_of_instance` | General | 1 | 9 | the discard rule for conditions |
| `tried_of_lt`, `anode_round` | Completeness | 1 each | 39 / 33 | what the rounds guarantee |

### `soundness`

```
soundness
├─ soundness_valid
│  ├─ run_inv ← expandAll_inv ← expandNode_inv ← { tryAssertion_inv ← { addNode_inv, recordAt_inv } ,
│  │                                                 mark_inv ← StateInv.mono ← ANodeInv.mono } ; init_inv
│  │     (addNode_inv alone uses 37 lemmas: the Unification fields, addNode_* facts, mem_vars_rename, Subst.vars_apply)
│  ├─ sptE_inv ← anodeEntries_inv ← { joinAll_absorbs ← Subst.solves_eqs_iff, joinAll_typed, joinAll_idem,
│  │                                   Absorbs.of_comp, Cond.apply_comp, mem_tuples }
│  └─ valid_of_inv ← { shape_of_inv ← { stepSub_apply, stepSub_typed, Subst.apply_comp, ANodeInv.unifies/children },
│                      conds_proofOf ← stepSub_f_of_mem, EntryInv.{absorbs, at_, conds, holds, typed} }
└─ close_isProof ← { Shape.subst ← { Subst.Typed.comp, Subst.restrict_apply, Assertion.WF.* },
                     holds_closing ← { vars_closing_apply, consts_closing_apply, Consts.app_not_mem_names },
                     allVars_close, conds_name, closing_typed, PTree.conds_subst, cond_mem_exprs }
```

Plumbing in the closure (not pictured in the backbone): Term 4, Subst 10,
Unification 4 (the structure's fields), Deduction 16 (`PTree.*_subst`,
`Assertion.WF.*`), Spt 27 (the invariants' fields, `getElem!_of_getElem?`),
Preserve 25 (`addNode_*`, `tryAssertion_cases`, `foldl_inv`), Closing 2.

### `generality`

```
generality ← generality'
├─ run_inv, sptE_inv                       (as for soundness)
├─ matches_of_congruent                    (congruence ⟹ Matches; no lemmas)
├─ assign_keys, assign_typed, anodes_lt    (the assignment's keys are the tree's a-nodes)
├─ anodes_nodup ← { sibling_disjoint ← { mem_chain_of_at ← chain_eq ← StateInv.up_lt, ANodeInv.children_eq },
│                   le_of_mem_enodes, parent_mem_enodes, nodup_flatMap_index }
├─ build_typed, build_f_lt, build_f_renamed ← look_of_nodup   (the global substitution)
├─ sim ← { Unification.mostGeneral, Subst.comp_eq_of_instance, ANodeInv.is_mgu, StateInv.base_eq,
│          apply_congr_vars, apply_rename_eq, stepSub_f_of_mem, Subst.ext }
├─ entry_mostGeneral ← { joinAll_mostGeneral ← { Subst.comp_eq_of_instance, Subst.solves_eqs_iff, joinAll_idem },
│                        Unification.mostGeneral, sptE_inv, mem_tuples, mem_aChildren }
└─ proofOf_subst ← { stepSub_comp, Subst.apply_comp }
```

Plumbing: Term 1, Subst 7, Unification 5, Deduction 4, Spt 26, Preserve 25,
Generality 16 (`chain_*`, `look_*`, `assignList_*`, `anc_fuel`).

### `completeness`

```
completeness ← completeness'
├─ treeOf_at ← { tried_of_lt ← { expandAll_tried, run_expanded_iff ← expandAll_expanded_iff ← expanded_tryAssertion,
│                                  run_zero_unexpanded, State.Le.tried },
│                children_lt_of_parent ← { anode_round ← anodes_foldl_expandNode ← anodes_tryAssertion,
│                                          run_expanded_iff, run_le_of_le ← State.Le.trans },
│                override_solves, override_typed, override_f_lt, override_f_renamed,
│                StateInv.tried_spec, tried_fresh, ANodeInv.is_mgu, Unification.mostGeneral,
│                Subst.comp_eq_of_instance, findNode_some(_of_mem), treeOfList_*, PTree.height_child, run_inv }
├─ sim, anodes_nodup, assign_keys, build_*   (as for generality)
├─ conds_proofOf                             (the variant's conditions are π's)
├─ entry_exists ← { entry_mostGeneral, joinAll_mostGeneral, joinAll_absorbs, joinAll_idem,
│                   holds_of_instance ← mem_names_apply ← { Subst.vars_apply, Subst.consts_apply },
│                   Subst.comp_eq_of_instance, sptE_inv, mem_tuples_of_index, mem_condsList_of_index, SptTree.fuel_child }
├─ fuel_le ← { ANodeInv.children_eq, SptTree.fuelList_le }
├─ sptE_mono ← mem_tuples_of_index
├─ congruent_of_matches
└─ entry_mostGeneral, proofOf_subst, init_inv, run_inv
```

Plumbing: as generality plus Completeness 38 (`State.Le.*` fields and the
`le_*` growth lemmas, `expanded_*`, `anodes_*`, `override_f_*`, `treeOfList_*`).

### The theorems beyond the three

Closure sizes, for orientation: `soundness_defs` 211 (adds `ToD.lean` 63),
`completeness_defs` 287 (adds `ToD` 28, `OfD` 56), `keyed_soundness` 248 (adds
`Engine` 43, `KeyedExact` 46, `KeyedCorr` 13, `Oriented` 6), `keyed_completeness`
324, `Unify.postulate` 59 (`Unify.lean` 42). Their graphs are not drawn; the
generator (`theory/tools/correspondence.py`) draws them when asked.

## 5. Reading order

The files in the order their imports allow and the theory builds up; within a file,
declarations come in the order written. The full list — every declaration with a
docstring, every structure and inductive, and every theorem `THEORY.md` names, with
its line and its first sentence (433 of 1,025 declarations) — is
[correspondence/reading-order.md](correspondence/reading-order.md). The short form:

1. **`Term.lean`** — `Ty`, `Ty.fits`, `Var`, `Exp`, `Exp.ty`, `Exp.vars`, `Exp.rename`,
   `Consts`, `Consts.names`, `Signature`. (Paper §2.1.)
2. **`Subst.lean`** — `Subst`, `apply`, `comp`, `apply_comp`, `Typed`, `IsInstance`,
   `Idem`, `eqs`, `restrict`; `ty_apply`, `vars_apply`, `consts_apply`. (§2.2.)
3. **`Unification.lean`** — `Problem`, `Solves`, `Unification` (the postulate),
   `join`, `joinAll`. (§2.2, §3.2.)
4. **`Deduction.lean`** — `Assertion`, `Database`, `Statement`, `SatPair`, `Cond`,
   `stepConds`, `PTree`, `subst`, `conds`, `Shape`, `Shape.subst` (Lemma 1),
   `CondsHold`, `Valid`, `IsProof`, `Var.dummy`, `closing`, `close`, `IsInstance`,
   `Congruent`. (§2.3.)
5. **`Search.lean`** — `ENode`, `ANode`, `SptTree`, `Entry`, `State`, `init`,
   `tryAssertion`, `expandNode`, `expandAll`, `run`, `leafEntries`, `tuples`,
   `anodeEntries`, `sptE`, `rootEntries`, `stepSub`, `proofOf`, `Entry.proof`.
   (§3.1, §3.2.) Read the header comment: the θ_a correction.
6. **`Spt.lean`** — `solves_eqs_iff`, `joinAll_absorbs`, `SptTree.At`, `Absorbs`,
   `EntryInv`, `ANodeInv`, `StateInv`, `stepSub_apply`, `shape_of_inv`,
   `conds_proofOf`, `valid_of_inv`. (Theorem 1, the invariant.)
7. **`Preserve.lean`** — `StateInv.mono`, `addNode_inv`, `recordAt_inv`,
   `tryAssertion_inv`, `mark_inv`, `expandNode_inv`, `expandAll_inv`, `init_inv`,
   `run_inv`, `anodeEntries_inv`, `sptE_inv`. (Theorem 1, preservation.)
8. **`Closing.lean`** — `holds_closing`, `allVars_close`, `conds_name`,
   `close_isProof`. (Decision 8.)
9. **`General.lean`** — `comp_eq_of_instance`, `joinAll_mostGeneral`,
   `mem_names_apply`, `holds_of_instance`, `stepSub_comp`, `proofOf_subst`.
10. **`Generality.lean`** — `chain`, `SptTree.enodes`/`anodes`, `sibling_disjoint`,
    `anodes_nodup`, `Matches`, `assign`, `nodeOf`, `build`, `sim`,
    `entry_mostGeneral`, `generality'`. (Theorem 2.)
11. **`Completeness.lean`** — `State.Le`, `run_le_of_le`, `expandAll_expanded_iff`,
    `tried_of_lt`, `anode_round`, `children_lt_of_parent`, `PTree.height`,
    `SptTree.fuel`, `fuel_le`, `override`, `treeOf`, `treeOf_at`, `sptE_mono`,
    `entry_exists`, `completeness'`. (Theorem 3.)
12. **`Unify.lean`** — `Unify.go`, `mgu`, `Inv`, `go_sound`, `go_complete`,
    `postulate`. (The postulate discharged.)
13. **`Engine.lean`** — `Mentions`, `joinAll_spec`, `ApartBelow`, `extend`,
    `joinAll_restrict_*`, `joinAll_key*`, `settled*`, `visible`, `InBlock`,
    `entry_mentions`, `spt_restrict`, `spt_key`, `spt_settled`. (The engine lemmas.)
14. **`Keyed.lean`**, **`KeyedLemmas.lean`**, **`KeyedCorr.lean`** — `KEntry`,
    `judgeK`, `anodeK`, `keyedE`; `SameOn`, `joinAll_inst`, `joinAll_sameOn`; `KInv`,
    `keyedE_inv`, `Member`, `restrict_chain`, `keyed_sound_np`, `keyed_complete_np`.
15. **`Oriented.lean`**, **`KeyedExact.lean`** — `Var.before`, `Subst.Oriented`,
    `oriented_unique`, `postulate_oriented`; `joinAll_restrict_eq`, `KEq`,
    `isPending`, `Joined`, `keyed_sound_ex`, `keyed_complete_ex`.
16. **`Defs.lean`**, **`Rules.lean`**, **`ToD.lean`**, **`OfD.lean`** — `Def`, `CTree`,
    `CValid`, `DTree`, `IsProofD`; `Language`, `Rules.*`, `withConv`, `toC`, `toD`;
    `cert_valid`, `proof_valid`, `toD_isProof`; `CTree.toTree`, `DTree.toP`,
    `toP_isProof`.
17. **`Theorems.lean`** — the statements: `soundness_valid`, `soundness`,
    `generality`, `completeness`, `soundness_defs`, `completeness_defs`,
    `keyed_soundness(_np, _postulate)`, `keyed_completeness(_np, _postulate)`.

`Theory.lean` imports the files in a different order (`Defs`, `Rules`, `ToD`, `OfD`
before `Closing` and `Search`); the order above is the one that puts each file after
everything it imports and keeps the first variant together.

## Regenerating

```
cd theory
lake env lean tools/Extract.lean          # writes tools/out/decls.jsonl, tools/out/modules.jsonl
python3 -I tools/correspondence.py        # writes docs/correspondence/*.svg, reading-order.md, graph-report.txt (needs graphviz)
```

The prose of this file is not generated; when a declaration moves, the line numbers
quoted above go stale and `graph-report.txt` has the fresh ones.
