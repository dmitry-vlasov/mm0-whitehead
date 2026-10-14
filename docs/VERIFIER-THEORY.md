# The verification of the verifier

Started on 2026-10-14. The aim: a verifier of `.mmb` proof files that is proved correct
against the formal semantics of MM0 — the one of `examples/mm0.mm0` of the MM0
repository, mirrored in Lean in `mm0-lean/mm0/mm0.lean` — and the fast verifier of this
project (`Whitehead/Verify`) tested against it statement by statement, the pattern of
`THEORY.md`, decision 15. The code is in the package `theory/` (Lean 4 with Mathlib):
the ported semantics in `theory/Spec/`, the machine and the proofs in
`theory/Verifier/`.

## The sources, and a finding

The MM0 repository has two Lean 3 files for the semantics:

- `mm0.lean` (236 lines): environments, well-formedness (`env.ok`), conversion and
  proof (`proof`), and the relation between a specification and a proof file
  (`env.extend`, `env.proof`). It is complete, and it is the Lean form of `mm0.mm0`.
  **It is the judge.**
- `mm0b.lean` (169 lines): the stack machine of `.mmb` proof streams, as relations
  (`step_proof`, `unify`, `proof`). It is a sketch, the README's "scratch files": the
  `term` command pops its arguments without comparing their types with the term's
  binders, the `thm` command has no check of the theorem's disjointness conditions,
  `initial_state` is an inductive with no constructor, and the `unfold` rule is
  labelled `cong`. No theorem relates it to `mm0.lean`. So the machine semantics must be
  completed by us — following `mm0b.lean`'s shape, `mm0-c/mmb.md` section 6 as we
  understood it (`MMB-NOTES.md`, section 6), and the checks the implementations make —
  and the content of the work is the theorem that the completed machine is sound for
  the logic. The checks the machine needs beyond `mm0b.lean` are exactly those whose
  absence would break that theorem, which is how they are justified.

Four points of `mm0.lean` to keep in mind when reading the port. `safe_subst`, the
disjointness conditions of a theorem step, reads the binders `u` and `v` and the
dependency of `v` on `u` in the context of the proof being checked, where the binders
of the theorem being applied are meant: `mm0.mm0`'s `VerifyProofThm` has the same text
against its own comment ("the disjoint variable conditions of the theorem are honored
by the substitution"), `mm0.md` states the rule over the theorem's binders, and the
three implementations check the theorem's binders; against the text as written the
machine could not be proved sound, so the port corrects it (the second deviation): the
binders and their dependencies are read in the theorem's context, the substituted
expression's variables in the proof's. `conv'` has no
transitivity rule, where the primary specification has the certificate `CTrans`
(`mm0.mm0`, `VerifyConvTrans`); the `Unfold` command of a proof file replaces an
obligation on an application by one on its unfolding, which `conv'.unfold` alone
cannot justify (it concludes the unfolding from the application, not the converse);
so the port adds `conv'.trans`, its one deviation, as the judge is the primary
specification. `env.extend.defn_def` builds on `E2` on both sides where `E1` was
presumably meant (ported as written; see milestone V6). `sexpr.ok_bi'` is defined but
not used (ported as written).

## Conventions

- The port is literal: the same names (snake case, as the original, so that the two
  files can be read side by side), the same order, Lean 3's `list.nth` as `[i]?`,
  `inth` as `getD`, `list.forall₂` as `List.Forall₂`, `set` as `Set`. Nothing but
  `conv'.trans` and the correction of `safe_subst` is changed in `Spec/Mm0.lean`; whatever the proofs need about the
  semantics is in separate files.
- What stays trusted at the end: Lean's kernel, the fidelity of the port (400 lines,
  reviewed side by side), the `.mm0` front end (lexer, parser, elaborator: the text
  grammar has no formalization, and a proof against our own grammar would only move the
  trust), and, unless milestone V5b is done, the byte decoder.

## Milestones

V1. The port of `mm0.lean` to Lean 4 (`Spec/Mm0.lean`), reviewed side by side.
V2. The machine semantics (`Verifier/Machine.lean`): `mm0b.lean`'s relations completed
    by the checks of section 6 of `MMB-NOTES.md` — the type of an application from the
    term's declaration and the arguments' types, bound arguments as variables of the
    right sort, the dependencies of a regular argument within the term's declared
    ones, dummies fresh, the theorem's disjointness conditions at `Thm` and the def's
    at `Unfold`, hypotheses and the final unification — over decoded commands, as the
    reader produces them. Each check cites the rule of the notes it implements; the
    gaps of `mm0b.lean` are recorded in `MMB-NOTES.md`, section 9.
V3. Soundness of the machine for the logic: a proof stream the machine accepts for a
    theorem gives `mm0.proof` of the theorem's statement in its context, and a proof
    file whose every statement the machine accepts gives `mm0.env.proof'` of the
    environment it declares. The core theorem.
V4. The reference verifier: an executable `check` over decoded statements, proved sound
    and complete for the machine relation; with V3, a verified checker of `.mmb` proofs.
V5. The differential test: the reference verifier against `Whitehead/Verify`
    (`checkProofs`) statement by statement, on the corpus and on the mutants of
    `tests/mutate`; what it finds is fixed or recorded. (V5b, optional: the byte
    decoder against the encoder, decode after encode the identity.)
V6. The match with the specification: `matchSpec` of `Whitehead/Verify/Spec.lean`
    accepts only when `env.extend` holds between the specification's environment and
    the proof file's.
