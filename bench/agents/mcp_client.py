"""A minimal client of the MCP server of Whitehead, over stdio, for the bench's own checks."""
import json
import subprocess


class Client:
    def __init__(self, command, cwd=None):
        self.p = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, cwd=cwd)
        self.n = 0
        self.request('initialize', {'protocolVersion': '2025-06-18', 'capabilities': {},
                                    'clientInfo': {'name': 'bench', 'version': '1'}})
        self.p.stdin.write(json.dumps({'jsonrpc': '2.0', 'method': 'notifications/initialized'}) + '\n')
        self.p.stdin.flush()

    def request(self, method, params):
        self.n += 1
        self.p.stdin.write(json.dumps({'jsonrpc': '2.0', 'id': self.n, 'method': method, 'params': params}) + '\n')
        self.p.stdin.flush()
        return json.loads(self.p.stdout.readline())

    def call(self, tool, args):
        r = self.request('tools/call', {'name': tool, 'arguments': args})['result']
        out = json.loads(r['content'][0]['text']) if r['content'][0]['text'].startswith('{') else r['content'][0]['text']
        return ('error', out) if r.get('isError') else out

    def close(self):
        self.p.stdin.close()
        self.p.wait()
