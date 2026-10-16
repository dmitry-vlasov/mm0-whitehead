#!/usr/bin/env python3
"""A bridge to the MCP server of Whitehead, for a shell: one server stays up behind a port of
127.0.0.1, and each `call` sends it one tool call and prints the result. For an agent
that has a shell but no MCP client, and for trying the server by hand.

    scripts/mcp-bridge.py serve <file.mm0> <file.mmb> --port P [--log FILE] [--anonymous]
    scripts/mcp-bridge.py call <tool> '<arguments as JSON>' --port P
    scripts/mcp-bridge.py stop --port P

`serve` starts `mm0-whitehead mcp`, initializes it, and answers on the port until it is
stopped; only this machine can connect. `call` prints the tool's result: its JSON, or
its error after `error:`, and exits 1 on an error.
"""
import json
import os
import socket
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BINARY = os.path.join(ROOT, ".lake", "build", "bin", "mm0-whitehead")


def option(args, name, default=None):
    if name in args:
        i = args.index(name)
        value = args[i + 1]
        del args[i:i + 2]
        return value
    return default


def serve(mm0, mmb, port, log, anonymous):
    command = [BINARY, "mcp", mm0, mmb] + (["--log", log] if log else []) + (["--anonymous"] if anonymous else [])
    server = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    next_id = 1

    def request(method, params):
        nonlocal next_id
        msg = {"jsonrpc": "2.0", "id": next_id, "method": method, "params": params}
        next_id += 1
        server.stdin.write(json.dumps(msg) + "\n")
        server.stdin.flush()
        line = server.stdout.readline()
        if not line:
            raise RuntimeError("the server ended")
        return json.loads(line)

    request("initialize", {"protocolVersion": "2025-06-18", "capabilities": {},
                           "clientInfo": {"name": "mcp-bridge", "version": "1"}})
    server.stdin.write(json.dumps({"jsonrpc": "2.0", "method": "notifications/initialized"}) + "\n")
    server.stdin.flush()
    listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    listener.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    listener.bind(("127.0.0.1", port))
    listener.listen(1)
    print(f"serving {mm0} on 127.0.0.1:{port}", flush=True)
    try:
        while True:
            conn, _ = listener.accept()
            with conn:
                data = b""
                while not data.endswith(b"\n"):
                    chunk = conn.recv(65536)
                    if not chunk:
                        break
                    data += chunk
                call = json.loads(data.decode())
                if call.get("stop"):
                    conn.sendall(b'{"stopped": true}\n')
                    break
                answer = request("tools/call", {"name": call["tool"], "arguments": call["arguments"]})
                conn.sendall((json.dumps(answer) + "\n").encode())
    finally:
        listener.close()
        server.stdin.close()
        server.wait()


def send(port, payload):
    conn = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    conn.connect(("127.0.0.1", port))
    conn.sendall((json.dumps(payload) + "\n").encode())
    data = b""
    while not data.endswith(b"\n"):
        chunk = conn.recv(65536)
        if not chunk:
            break
        data += chunk
    conn.close()
    return json.loads(data.decode())


def main():
    args = sys.argv[1:]
    port = option(args, "--port")
    log = option(args, "--log")
    anonymous = "--anonymous" in args
    if anonymous:
        args.remove("--anonymous")
    if not args or port is None:
        print(__doc__, file=sys.stderr)
        return 2
    port = int(port)
    if args[0] == "serve" and len(args) == 3:
        serve(args[1], args[2], port, log, anonymous)
        return 0
    if args[0] == "stop":
        send(port, {"stop": True})
        return 0
    if args[0] == "call" and len(args) in (2, 3):
        arguments = json.loads(args[2]) if len(args) == 3 else {}
        answer = send(port, {"tool": args[1], "arguments": arguments})
        if "error" in answer:
            print("error: " + answer["error"]["message"])
            return 1
        result = answer["result"]
        text = result["content"][0]["text"]
        if result.get("isError"):
            print("error: " + text)
            return 1
        print(json.dumps(json.loads(text), indent=1, ensure_ascii=False))
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main())
