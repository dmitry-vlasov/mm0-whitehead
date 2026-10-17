You have the MCP server `whitehead`: an interactive and automatic prover over the same
library, which builds the proof for you from the steps you choose and the tactics you
run. It uses only the assertions before `{name}`, as you may.

- Start a session on the theorem with `start` (theorem `{name}`). The server's
  instructions and its tool `language` explain the rest: the tree of goals and their
  variants, the filters that narrow the variants, choosing variants, intermediate
  goals, and the tactics that `run` takes (for instance `guided`, the strongest
  automatic one, or `bfs`).
- Statements are written in the notation of the library.
- `./search REGEX` lists the lines of `library.mm1` that match a regular expression, and
  `Read` reads it.
- The only shell command you may run is `./search ...`, as a command of its own.
- The proof is found when the session says `proved`. Then call `proof` on the session:
  it shows the proof, checked by the server's verifier. That call is the end.
