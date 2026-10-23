# Ramsey: the engine inside Lean 4 — the startup plan (2026-10-23)

Ramsey is the third system of the route Russell → Whitehead → Ramsey (the ARGO talk of
2026-10-08): the proof variant tree and the substitution proof trees, running over Lean 4's
own terms, inside Lean's metaprogramming API, with Lean's decision procedures as oracles at
the leaves. This file is the plan for its first weeks: what it is for, given what
Whitehead measured; what it is made of; and the order of building.

## What it is for

The talk's bet was that an LLM agent would spend fewer tokens by proposing statements and
letting the engine prove the fragments between them. Whitehead's agent bench refuted it:
an agent clicking the engine's nodes proved 26 of 30 against 30 of 30 for an agent
writing MM1, at five times the cost, and the engine as a gap filler closed 12 of 53 holes
(`EXPERIMENTS.md`). So Ramsey is not an LLM's workbench. What a Russell-style engine has
that Lean's automation lacks is a complete, bounded, library-wide search; answer
substitutions merged across sibling goals; and a tree it can show. Each maps to a use that
does not depend on an LLM, in the order of their value:

1. **Proof repair.** What breaks under library changes is the mechanical fragments between
   the `have`s — the short chains the engine is good at. A tactic that re-proves a broken
   step from the lemmas the old proof cited, complete within a depth bound.
2. **Witnesses by joining.** `apply`, `use` and Aesop are weak where metavariables are
   shared between goals; the SPT join is the systematic solution. A tactic for existential
   and instance goals that finds the witness by merging answer sets across the goals.
3. **Proof restructuring.** A tactic proof's term is a certificate whose subterms prove
   propositions: cut points for free. Re-prove each from the previous ones with named
   lemmas within depth k, and keep the tactic where the engine fails; first target, `simp`
   proofs into `rw`/`calc` chains. Isabelle's structured Isar reconstruction is the
   precedent; Lean has `simp?` and `says`, which name the lemmas but not the chain.
4. **Lemma mining.** Whitehead found 664,589 distinct recurring subproofs in set.mm, each
   with its most general lemma; the same over Mathlib proposes missing lemmas.
5. **A native hammer without translation**, between `exact?` (one step) and LeanHammer
   (external ATP plus reconstruction); and complete trees as data for the ML community.

## What Lean already has of the engine

The join is more feasible than the difference of foundations suggests, because the
engine's objects exist in Lean under other names:

| Russell / Whitehead | Lean 4 |
|---|---|
| expression with metavariables | `Expr` with `?m`, in `MetaM` |
| assertion, premises and conclusion | a constant whose type is a Π-telescope: `forallMetaTelescope` gives premises as new goals and the conclusion |
| unification, most general unifier | `isDefEq` under a transparency: one assignment, not a most general unifier; syntactic at `reducible` on most goals |
| substitution | the metavariable assignment (`MetavarContext`) |
| the index of conclusions | `DiscrTree` in core (`exact?`, `apply?`, `simp` use it) |
| bound variables, dependencies | binders in the goal's local context; `intro` as a rule |
| definitions and unfolding | definitional equality inside `isDefEq`; `unfold`/`delta` as rules |
| conversion rules | none needed: `isDefEq` decides them, as an oracle |
| hypotheses of the theorem | the local context's `fvar`s |
| the task's sorts | universes, one more kind of metavariable; typeclass instances, an oracle |

What none of `exact?`, `solve_by_elim` and Aesop do is keep all variants, merge answer
sets across sibling goals, and chain forward. That is the engine's contribution, and it
needs no new foundation.

## What changes, and what the theorems become

- **The unifier returns an assignment, not a most general unifier.** The 2017 paper's
  completeness rests on the uniqueness of unifiers; `isDefEq` is a procedure with a
  transparency setting. Completeness becomes *relative*: to the assignments `isDefEq`
  returns under the chosen transparency, and to the oracles at the leaves. Whitehead's
  theory package (`THEORY.md`) proved soundness, generality and completeness for MM0 with
  a unification *postulate* discharged for first-order terms; for Ramsey the postulate is
  the specification of the unifier, kept as a postulate, and the theorems are proved
  modulo it. The Lean-tailored statement of the three theorems is the spec, as the talk
  says.
- **Cost.** `isDefEq` is milliseconds where MM0's unifier is microseconds, and the engine
  makes a thousand variants a goal. Whitehead's lessons apply directly: the discrimination
  tree as the first filter; rank before instantiating (the cheap stage over all
  candidates, the full model over its first hundred); a value as a capped tie-breaker;
  the honest measure over all variants; negatives drawn evenly.
- **Goals carry a context.** A node is a local context and a type, not a bare
  expression; `intro` for Π-goals is a rule like the others, and the engine's "constants
  of the theorem" are the `fvar`s. Where Whitehead's bound-variable discipline was
  dependency pairs, Ramsey's is the local context and `isDefEq`'s occurs check.
- **Oracles at the leaves**, not expansions: instance resolution, `decide`, `omega`,
  `simp` with a given set, `rfl` up to a transparency. A leaf closed by an oracle carries
  the oracle's proof term; the engine's proof is the tree with the oracle terms at the
  leaves. This is Whitehead's "a procedure is a guide, replayed by `follow`" with the
  replay replaced by the term, since Lean checks terms.

## The first weeks, in order

1. **The toy theory.** A Lean file with `And`, `Or`, `Not`, `Exists` over a few atoms and
   twenty lemmas; no Mathlib. The engine over it: `Expr` goals, candidates from a
   `DiscrTree` of the lemmas' conclusions, `isDefEq` at `reducible`, the PVT with all
   variants kept, the SPT join of assignments across sibling goals (compatibility of two
   assignments = `isDefEq` on the values they share), breadth-first rounds, a proof term
   assembled from the tree and checked by `exact`. A week. This is where the unclarity
   about the foundations resolves: either the join of assignments works as the join of
   substitutions, or the place where it does not is found.
2. **The two measurements** on the toy theory and then on a Mathlib slice (`Logic`,
   `Order.Basic`): the effective branching factor (variants a goal, and where the known
   step comes), and the depth reached at 1 s. Whitehead's numbers are the baseline: a
   median of 1,076 variants, the known step first at 23%, depth 2–4 at 5 s.
3. **The first use: witnesses by joining**, as a tactic `ramsey_use` on existential goals
   from a Mathlib slice, judged by proofs found against `use`/`exists`/Aesop on the same
   goals. The join is the engine's distinctive piece, and the tactic is small.
4. **Proof repair, as a bench first.** Take a Mathlib commit that broke proofs, the
   broken `have` steps with the lemmas their old proofs cited, and measure what the
   engine re-proves within depth 6. The bench decides whether the tactic is worth
   building.
5. **The spec.** The Lean-tailored statements of soundness, generality and completeness
   modulo the unifier and the oracles, as a Lean file in Ramsey's own theory package,
   with Whitehead's `THEORY.md` as the template. Proved later; stated early, since the
   statements fix what "relative" means.
6. **Guidance, only when the engine is there**: the prior per theorem (the lemmas the
   proofs of similar theorems use), the contexts of use per lemma, the cheap and the full
   rank, trained on Mathlib's proof terms as Whitehead's were on set.mm's proofs. The
   recipe transfers whole; the models do not.

## What stays in Whitehead

Whitehead remains the bench and the laboratory: the measurements, the recipe, the
theory package and the verified checker. Its MM0-specific work — front-ends, features of
the current kind, speed, the number of negatives — is finished (`STATUS.md`). What is
left there is the contexts-of-use experiment (`DESIGN.md`, "Contexts per assertion"), the
value retrained on the current ranker's trees, and the two carried gaps of phase 3
(shared conversions in the replay reader; checking a proof found for a task with
metavariables).
