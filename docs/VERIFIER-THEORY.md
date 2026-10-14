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

Five points of `mm0.lean` to keep in mind when reading the port. `sexpr.free'`, the
free variables of an application, joins its two cases — a variable free in a regular
argument and not captured by a bound argument the binder depends on; a variable
substituted for a bound binder the return type depends on — with a conjunction, where
`mm0.mm0`'s `FreeApp` has the disjunction and the rule's sense (and `mmb.md`'s
formula, `MMB-NOTES.md` section 6) is the union; the port corrects it (the third
deviation). `safe_subst`, the
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
  `conv'.trans` and the corrections of `safe_subst` and `sexpr.free'` is changed in
  `Spec/Mm0.lean`; whatever the proofs need about the
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
    environment it declares. The core theorem. **Reached on 2026-10-14**:
    `Verifier/FileSound.lean`, `file_sound : FileOk f → ∃ E, toEnv f = some E ∧
    env.proof' E`, with only `propext`, `Classical.choice` and `Quot.sound`. The
    argument, file by file:
    - `Translate`: the machine's data as the semantics' — bound-variable numbers to
      variables, binders, nodes to expressions, unify streams decoded to statements
      and def values, a file to an `env`.
    - `Store`, `StoreStep`, `NewNodes`, `AppDef`, `StepStore`, `Load`, `CtxOk`: the
      type word of a node means what it says — its sort is the expression's, its bound
      flag marks bound variables, its dependency set is the bound variables the
      expression has (`has_var`, in a theorem) or has free (`free`, in a definition) —
      through every command; the loaded binders are a well-formed context.
    - `UnifyLemma`, `UnifyUse`: a stream the unifier accepts decodes to an expression
      whose instance under the heap is the node's (strong induction on the decoder's
      fuel; a saved term being read is undecoded and above every node of its
      segment); its three uses — `Unfold` and the end of a def, `Thm`, the end of a
      theorem.
    - `Disjoint`: the machine's disjointness checks at `Thm` give `safe_subst`.
    - `World`, `StepSound`, `RunSound`: the stack invariant, judged in the world of
      the statement's end (its final store, context with all dummies, hypotheses): an
      element is valid assuming the obligations above it, since `Conv` pushes a proof
      whose validity rests on the obligation it pushes above it. Every command keeps
      it; `Cong` and `Unfold` discharge obligations by the congruence and unfolding
      rules, the latter needing the def's value well-typed (`EnvHas.defs_ok`, from the
      def's own statement) so that the obligation's sort is the term's.
    - `StmtSound`, `FileSound`: a theorem proves its decoded statement in its context
      with its dummies (`env.proof'.thm`); a term or def establishes its declaration's
      well-formedness and its value's typing; the statements in order build the
      environment.
    Two strengthenings of the machine were made in the course (both what the format
    and the implementations do): a hypothesis of a theorem's stream comes with an
    empty unify stack, and the def-mode dependency formula indexes arguments by
    bound-variable number. What the theorem does not yet say: that the environment is
    well-formed (`env.ok`: the definitions' free-variable condition, the terms'
    result sorts not pure, and so on) — the machine checks these, and the facts are
    proved on the way (`TermFacts`), but not assembled into `env.ok`; that is
    milestone V3b.
V3b. Well-formedness: a file the machine accepts declares an `env.ok` environment.
    **Reached on 2026-10-14**: `file_valid : FileOk f → ∃ E, toEnv f = some E ∧
    env.ok E ∧ env.proof' E`, and with the matcher `spec_valid : … → ∃ E', env.ok E' ∧
    env.extend S E' ∧ env.proof' E'`, which is `mm0.mm0`'s top-level `ValidEnv S` but
    for `Env S`, the specification's own well-formedness (the front end's). Standard
    axioms only. The pieces: `term_ok` (a fresh number, well-formed binders and
    return type, a result sort not pure); `axiom_ok` (the statement and hypotheses
    well-typed in the binders' context at provable sorts, the hypotheses' sorts kept
    through the run, `HypsProvable`); and `defn_ok`, whose free-variable condition is
    the substance (`WF.lean`, `term_stmt_wf`). A def's value is the one its stream
    decodes, over its binders and the stream's own dummies; the node the machine
    checked is that value renamed into the body's context. Free variables are carried
    along an injective renaming that keeps the binders (`Free.lean`, `free_rename`),
    and the renaming is injective because of `UDummy`'s freshness check — the dummies'
    nodes are fresh against the arguments and against each other, which the unify
    lemma now carries (`DummyNodes`) and which, with the meaning of the type words,
    makes their variables distinct from each other and from the binders. A free
    variable of a well-typed expression is bound (`free_bound`), so it has a number,
    the node's dependencies contain it, and the machine bounds those by the return
    type's.
V4. The reference verifier: an executable `check` over decoded statements, proved sound
    and complete for the machine relation; with V3, a verified checker of `.mmb` proofs.
V4 is **reached on 2026-10-14**: `Verifier/Check.lean`, `checkFile`, with every
    function proved sound for its relation, and `checkFile_correct : checkFile f = true
    → ∃ E, toEnv f = some E ∧ env.proof' E`, a verified checker of decoded `.mmb`
    files (standard axioms only). It is not fast — lists and finite sets — but it
    checks the set.mm translation in 39 s.
V5. The differential test: the reference verifier against `Whitehead/Verify`
    (`checkProofs`) statement by statement, on the corpus and on the mutants of
    `tests/mutate`; what it finds is fixed or recorded. (V5b, optional: the byte
    decoder against the encoder, decode after encode the identity.) **Reached on
    2026-10-14**: `lake exe verify-diff` (`theory/VDiff.lean`; the conversion of the
    reader's output, `Verifier/OfMmb.lean`, is trusted). Results: the 49 verifier
    fixtures agree, each rejection at the same statement; every corpus file agrees
    (set.mm translation, peano, peano_hex, hol, set, mm0, x86, compiler,
    hello_mmc accepted by both; hello_assembler rejected by both at its `Sorry`);
    the mutant campaign of phase 2 — 31,800 mutants of six files, at its counts and
    seeds — agrees on all 24,168 that the reader reads (2,723 accepted by both). It
    found three things. A modelling error in the machine: `Hyp` pushed the proof onto
    the stack, where the format only puts it on the heap, so every valid theorem with
    hypotheses was rejected (fixed in the machine, the step function and the proof).
    A fault in the conversion: a `LocalDef` statement on an entry that is not a def
    was converted to a term statement (point 7 of `MMB-NOTES.md` section 9; fixed).
    And a format check outside the machine: the term table's sort byte must equal
    the return type's (point 9), which the machine never reads; the conversion checks
    it, as it checks that every stream decodes. A rejection by the conversion counts
    as agreeing with any rejection of the fast verifier: the reader decides it and is
    trusted.
V6. The match with the specification: `matchSpec` of `Whitehead/Verify/Spec.lean`
    accepts only when `env.extend` holds between the specification's environment and
    the proof file's. **Reached on 2026-10-14** in the form of milestones V4 and V5:
    a reference matcher (`Verifier/Extend.lean`, `extendRev`) proved sound for
    `env.extend`, and the end-to-end theorem `spec_proved : checkFile f = true →
    toEnv f = some E → extendRev S.reverse E.reverse L = true → env.proof S` (standard
    axioms only). `env.extend.defn_def` is corrected in the port to `mm0.mm0`'s
    `EnvExtendDef` (the fourth deviation: the original builds the abstract def on the
    later environment). The specification is converted by `Verifier/OfMm0.lean`
    (trusted, like the front end it reads), with three choices of names and order the
    semantics does not depend on: term ids are the proof file's numbers, a def's
    dummies are numbered by first occurrence, a theorem's hypotheses are listed last
    first, as the stream has them. `lake exe verify-diff x.mm0 x.mmb [--mutants N]`
    compares `extendRev` with `matchSpec`: both accept every corpus pair (set.mm
    translation, peano, peano_hex, hol, set, mm0, x86, hello_mmc, compiler), and they
    agree on all 652 mutants of hol, set and peano that both proof checks accept (479
    matched by both, 173 rejected by both).
    What `spec_proved` gives is `EnvExtend` and `EnvFull` of `mm0.mm0`'s top-level
    `ValidEnv spec := Env spec ∧ ∃ e, Env e ∧ EnvExtend spec e ∧ EnvFull e`; `Env e`,
    the well-formedness of the proof file's environment, is milestone V3b, and
    `Env spec` is the front end's (trusted).

## The prover's soundness (2026-10-14)

The prover's proofs are made sound by verified checking of what it writes, not by a
proof about the prover. `lake exe certify <file.mmb> [<spec.mm0>]` (`theory/Certify.lean`)
runs the verified checker on a proof file, and the verified matcher against a
specification: accepted, the file's environment is well-formed and proved
(`file_valid`) and the specification is valid up to its own well-formedness
(`spec_valid`). `scripts/prove-certified.sh replay|search <in.mmb> <out.mmb> [<spec.mm0>]`
runs the prover with `-o` and then `certify` on the file written. The main package
cannot call the checker itself: the theory package needs Mathlib, which the main
package must not depend on.

Checked on 2026-10-14: the replay of peano (2,650 proofs reconstructed) and of the
first 2,000 theorems of the set.mm translation (1,974 reconstructed) are certified
against their specifications (0.2 s and 37 s); the search on the logic fixture (15 of
16 proved) is certified; a fixture with a wrong proof is rejected.

What this does not cover: a proof the prover reports but does not write (without `-o`),
and a proof found for a task with metavariables, which proves an instance of the
theorem and is neither written nor checked (`STATUS.md`, "Next steps"). Trusted as for
the verifier: Lean's kernel and compiler, the port of the semantics, the byte reader,
the `.mm0` front end, and the two conversions.
