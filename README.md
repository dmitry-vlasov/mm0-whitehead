# mm0-whitehead

Tooling for [Metamath Zero](https://github.com/digama0/mm0) in Lean 4: readers for the
`.mm0` and `.mmb` formats, an independent verifier, and an automated prover ported from
the Russell prover. The plan and its phases are in [CLAUDE.md](CLAUDE.md); the current
state is in [docs/STATUS.md](docs/STATUS.md).

## Build and test

    lake build                           # builds .lake/build/bin/mm0-whitehead
    lake test                            # the self-contained tests
    MM0_REPO=/path/to/mm0 lake test      # also runs over the .mm0 files of the MM0 repository

The Lean toolchain is pinned in `lean-toolchain`. There are no dependencies beyond core
Lean.

## Usage

    mm0-whitehead verify file.mm0 file.mmb   # the proof file is valid and proves the specification
    mm0-whitehead verify file.mmb            # the proofs alone, without a specification
    mm0-whitehead dump file.mm0              # print the parsed statements, normalized
    mm0-whitehead dump file.mmb              # print the statements and proofs of a proof file
    mm0-whitehead join file.mm0              # a specification with every import included
    mm0-whitehead bench file ...             # time the .mm0 front end or the .mmb reader

    mm0-whitehead prove replay file.mmb -o out.mmb   # reconstruct every proof from the assertions it uses
    mm0-whitehead prove search file.mmb --ms 1000    # prove every theorem from scratch
                                                     #   --strategy bfs (backward), forward, or both
    mm0-whitehead prove db file.mmb                  # what the prover reads from a proof file

`verify` exits with 0 if the file is accepted; otherwise it prints the first error with
its file offset and statement.

`prove replay` forgets every expression of a proof, keeps only which assertions it uses
and how they nest, and lets the engine find the rest by unification; `prove search` is
given no proof at all. Both take `--from A --to B` (numbers of theorems) and `--verbose`,
check every proof they find with the verifier, and with `-o` write the file with the new
proofs. The engine is a port of the Russell prover; see [docs/DESIGN.md](docs/DESIGN.md),
"The prover".

A variable of a theorem is a free variable: the proof holds for every value of it.
`prove search --meta 0,2` marks the binders 0 and 2 of the theorems in the range as
metavariables instead: the prover finds values for them, and `--verbose` prints what it
found. This marking is a stub — MM0 has no syntax for it — and such a proof, which proves
an instance of the theorem, is not written or checked.

## Reference tools and test corpus

The tests compare against `mm0-rs`, the reference implementation, and the acceptance
tests run on proof files that have to be built first. Neither is kept in this repository:

    scripts/build-oracles.sh [--with-hs] /path/to/mm0    # mm0-rs, mm0-c, mm0-hs -> .tools/bin
    SET_MM=/path/to/set.mm scripts/build-corpus.sh /path/to/mm0    # pairs -> .tools/corpus

`mm0-rs` needs a recent stable Rust; `--with-hs` builds `mm0-hs`, which is needed only
for the set.mm translation and takes about ten minutes.

With both in place, the verifier can be compared with `mm0-rs` on mutated proof files:

    lake exe mutate file.mmb --count 3000 --seed 1    # one campaign
    scripts/mutation-campaign.sh                      # those of the acceptance test, about a minute

## Documents

- [docs/MMB-NOTES.md](docs/MMB-NOTES.md) — the `.mmb` format as we understand it, and where
  the formal semantics, `mm0-rs` and mm0-c differ
- [docs/DESIGN.md](docs/DESIGN.md) — how the code is built and why
- [docs/STATUS.md](docs/STATUS.md) — what passes, what is open
