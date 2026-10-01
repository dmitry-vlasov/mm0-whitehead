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

    mm0-whitehead dump file.mm0          # print the parsed statements, normalized
    mm0-whitehead bench file.mm0 ...     # time the parser

`dump` for `.mmb` files, `verify` and `prove` are not implemented yet.

## The reference verifier

Differential testing uses `mm0-c` from the MM0 repository as the oracle:

    scripts/build-oracles.sh /path/to/mm0     # builds .tools/bin/mm0-c and mm0-c-np

## Documents

- [docs/MMB-NOTES.md](docs/MMB-NOTES.md) — the `.mmb` format as we understand it, and where
  the spec and `mm0-c` disagree
- [docs/DESIGN.md](docs/DESIGN.md) — how the code is built and why
- [docs/STATUS.md](docs/STATUS.md) — what passes, what is open
