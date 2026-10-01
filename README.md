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

`verify` exits with 0 if the file is accepted; otherwise it prints the first error with
its file offset and statement. `prove` is not implemented yet.

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
