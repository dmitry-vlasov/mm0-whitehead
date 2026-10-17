# The agent bench

An agent with Whitehead against an agent writing MM1, on the same theorems of
`peano.mm1` (`docs/DESIGN.md`, "The agent bench"). Needs the corpus
(`scripts/build-corpus.sh`), `mm0-rs` in `.tools/bin`, the `claude` CLI, and
`MM0_REPO`.

    # the library with its theorems renamed, so that the agents cannot recall the proofs
    python3 bench/agents/rename.py $MM0_REPO/examples/peano.mm1 .tools/corpus/peano.mm0 OUT
    # both agents on every task of tasks.json
    BENCH_LIBRARY=OUT bench/agents/ladder.sh RUNS
    # the table
    python3 bench/agents/bench.py summary RUNS/*-whitehead RUNS/*-mm1

- `bench.py`: prepares, runs and scores one agent on one theorem (its docstring).
- `prompts/`: what the agents are told.
- `mm1.py`: the top-level statements of an `.mm1` file.
- `spec.py`: an attempt at a full `.mm0` from an `.mm1` file; not used, since MM1 lets a
  binder go without its type.
- `results/`: the scores of the runs reported in `DESIGN.md`.
