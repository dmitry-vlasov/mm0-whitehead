Write the proof in MM1: the text that follows `=` in the theorem's declaration, such as
`'(syl h1 h2)` or a tactic script `(focus ...)`, as the proofs of `library.mm1` are
written. Put that text, and nothing else, in the file `proof.mm1`.

- Run `./check` to have it checked. It puts your text after the theorem's header, at
  the end of the library, compiles the file with `mm0-rs` (the MM0 toolchain), and
  prints the errors, or `OK` when the proof is accepted.
- A hole `_` in a proof term makes the error show the goal that is left there.
- `mm1.md` describes the MM1 language, its proof terms and tactics.
- `./search REGEX [FILE]` lists the lines of `library.mm1` (or of `mm1.md`) that match a
  regular expression, and `Read` reads them.
- The only shell commands you may run are `./check`, `./fill` and `./search ...`, each as a command
  of its own (not inside `;`, `&&` or a redirection). Write `proof.mm1` with `Write` or
  `Edit`.
- `./fill [SECONDS]` does what `./check` does, and more: each hole `_` whose goal has no
  metavariable is given to Whitehead, an automatic prover over the library, for SECONDS
  (5 by default). A proof it finds is put in the hole, as an MM1 term, and `proof.mm1`
  is written back with it. It finds proofs of a few steps from the theorem's hypotheses
  and the library (not from your local `have`s); a hole whose goal has a metavariable
  `?a` is not tried, so state such a step, with `have` for instance. Write the structure
  of the proof, and leave the routine steps to it as holes.
- The proof is found when `./check` or `./fill` prints `OK`. That is the end.
