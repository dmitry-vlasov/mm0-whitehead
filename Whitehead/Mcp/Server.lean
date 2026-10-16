/-
The MCP front-end (`docs/DESIGN.md`, "Phase 4", "Front-ends"): a server of the Model
Context Protocol over stdio, for an AI agent, with the tools of `Mcp/Tools.lean`.

The transport is that of MCP over stdio: JSON-RPC 2.0 messages, one per line, read from
stdin and written to stdout, which carries nothing else. The server answers
`initialize`, `ping`, `tools/list` and `tools/call`; a notification needs no answer. An
error of a tool, such as a choice that is not a variant, is a result with `isError`, for
the agent to read; an error of the protocol is a JSON-RPC error. With a log, every
message in and out is written to it, one per line: the trace of the session.
-/
import Whitehead.Mcp.Tools

namespace Whitehead.Mcp

/-- The versions of the protocol that the server speaks, the latest first. -/
def protocolVersions : Array String := #["2025-06-18", "2025-03-26", "2024-11-05"]

def instructions : String :=
  "Whitehead proves theorems of a Metamath Zero proof file from the assertions before them. \
   Start a session for a theorem (`start`); its goal is node 0. A goal node has variants: \
   the assertions that could conclude it, each with the new goals it would make. There are \
   often thousands: narrow them with a filter (`variants`; see `language`), tightening it \
   until a few are left and loosening it when none are, then `choose` some. The engine does \
   all the unification: a variable it made is printed `?` and a number, and you never give \
   a value for one. Between the choices, let tactics expand the tree (`run`, such as \
   `limited(bfs, depth=3)`). Offer an intermediate goal you believe is true and useful \
   (`goal`); once proved it is used wherever it fits. With `forward`, you can also choose \
   facts and deduce from them (`facts`, `deduce`). When `proved` is true, `proof` gives \
   the proof, checked by the verifier. Statements are in the notation of the \
   specification; in a filter's pattern and in an intermediate goal, `_` is a hole."

def rpcResult (id result : Json) : Json :=
  .obj #[("jsonrpc", "2.0"), ("id", id), ("result", result)]

def rpcError (id : Json) (code : Int) (msg : String) : Json :=
  .obj #[("jsonrpc", "2.0"), ("id", id), ("error", .obj #[("code", .int code), ("message", Json.str msg)])]

def toolResult (text : String) (isError : Bool) : Json :=
  .obj #[("content", .arr #[.obj #[("type", "text"), ("text", Json.str text)]]), ("isError", .bool isError)]

def toolsJson : Json :=
  .obj #[("tools", .arr (tools.map fun t =>
    .obj #[("name", Json.str t.name), ("description", Json.str t.description), ("inputSchema", t.input)]))]

/-- One message: the answer, or `none` for a notification. The sessions are in `st`; the
state is taken out of it while a tool runs, so that the tree is not held twice. -/
def handle (c : Ctx) (st : IO.Ref State) (msg : Json) : IO (Option Json) := do
  match msg with
  | .obj _ => pure ()
  | _ => return some (rpcError .null (-32600) "a message is a JSON object")
  let some id := msg.get? "id" | return none
  let some method := (msg.get? "method").bind (·.str?)
    | return some (rpcError id (-32600) "a request needs a `method`")
  let params := (msg.get? "params").getD (.obj #[])
  match method with
  | "initialize" =>
    let asked := ((params.get? "protocolVersion").bind (·.str?)).getD ""
    let version := if protocolVersions.contains asked then asked else protocolVersions[0]!
    return some (rpcResult id (.obj #[("protocolVersion", Json.str version),
      ("capabilities", .obj #[("tools", .obj #[("listChanged", .bool false)])]),
      ("serverInfo", .obj #[("name", "whitehead"), ("version", "0.1.0")]),
      ("instructions", Json.str instructions)]))
  | "ping" => return some (rpcResult id (.obj #[]))
  | "tools/list" => return some (rpcResult id toolsJson)
  | "tools/call" =>
    let some name := (params.get? "name").bind (·.str?)
      | return some (rpcError id (-32602) "`tools/call` needs the `name` of a tool")
    let args := (params.get? "arguments").getD (.obj #[])
    let s ← st.modifyGet fun s => (s, {})
    match ← ((call c name args).run s).run with
    | .ok (result, s') =>
      st.set s'
      return some (rpcResult id (toolResult result.compress false))
    | .error e =>
      st.set s
      return some (rpcResult id (toolResult e true))
  | _ => return some (rpcError id (-32601) s!"unknown method `{method}`")

/-- Serves the agent on stdin and stdout until stdin ends. -/
partial def serve (c : Ctx) (log : Option IO.FS.Handle := none) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let st ← IO.mkRef ({} : State)
  let trace (dir text : String) : IO Unit := do
    if let some h := log then
      h.putStrLn s!"{dir} {text}"
      h.flush
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAsciiEnd.toString
    if line.isEmpty then continue
    trace "<-" line
    let answer ← match Json.parse line with
      | .error e => pure (some (rpcError .null (-32700) s!"not JSON, at character {e.pos}: {e.msg}"))
      | .ok msg => handle c st msg
    if let some a := answer then
      let text := a.compress
      stdout.putStrLn text
      stdout.flush
      trace "->" text

end Whitehead.Mcp
