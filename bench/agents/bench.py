#!/usr/bin/env python3
"""The agent bench: an agent with Whitehead against an agent with MM1, on the same theorems.

Each run is one agent, `claude -p` with its own directory, tools and limits, on one
theorem of `peano.mm1`:

- `whitehead`: the MCP server of Whitehead on peano (`mcp`, with the definitions of
  `tactics/` and `--export`), and Read, Grep, Glob on its directory;
- `mm1`: Read, Grep, Glob, Write, Edit on its directory, and `./check`, which compiles
  its proof with `mm0-rs`.

Both see `library.mm1`, the library up to the theorem. What is measured:

- the agent: tokens (input, cache writes, cache reads, output), cost, turns, wall time,
  tool calls;
- the machine: for `whitehead`, the server's CPU time and largest resident memory
  (`/usr/bin/time`) and the time its tools report; for `mm1`, the same of every
  `./check`;
- whether the proof is accepted, by `mm0-rs` in both cases: the `.mmb` with Whitehead's
  proof put in, or the `.mm1` with the agent's proof.

    bench.py prepare <theorem> <whitehead|mm1> <dir>
    bench.py run <theorem> <whitehead|mm1> <dir> [--model M] [--effort E] [--turns N]
             [--budget USD] [--timeout S]
    bench.py score <dir>
    bench.py summary <dir>...       a table of scored runs
"""
import json
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mm1  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(HERE))
BIN = os.path.join(ROOT, '.lake', 'build', 'bin', 'mm0-whitehead')
MM0RS = os.path.join(ROOT, '.tools', 'bin', 'mm0-rs')
CORPUS = os.path.join(ROOT, '.tools', 'corpus')
TACTICS = os.path.join(ROOT, 'tactics')
MM0_REPO = os.environ.get('MM0_REPO', '/home/dmitry/tools/mm0')
MM1_DOC = os.path.join(MM0_REPO, 'mm0-hs', 'mm1.md')
# BENCH_LIBRARY: a directory made by rename.py, the library with its theorems renamed
# (peano.mm1, peano.mm0, peano.mmb, names.json); otherwise the library as it is
LIBDIR = os.environ.get('BENCH_LIBRARY')
if LIBDIR:
    LIBRARY = os.path.join(LIBDIR, 'peano.mm1')
    SPEC, MMB = os.path.join(LIBDIR, 'peano.mm0'), os.path.join(LIBDIR, 'peano.mmb')
    NAMES = json.load(open(os.path.join(LIBDIR, 'names.json')))
else:
    LIBRARY = os.path.join(MM0_REPO, 'examples', 'peano.mm1')
    SPEC, MMB = os.path.join(CORPUS, 'peano.mm0'), os.path.join(CORPUS, 'peano.mmb')
    NAMES = {}

ABOUT = {
    False: "The library is Mario Carneiro's `peano.mm1`: propositional and predicate logic, then\n"
           "Peano arithmetic, sets, lists and more, in the MM1 language of Metamath Zero.",
    True: "The library covers propositional and predicate logic, then Peano arithmetic, sets,\n"
          "lists and more, in the MM1 language of Metamath Zero. Its theorems are named `L` and\n"
          "a number, in the order of the file.",
}

# the server may not take more than this much virtual memory (KB)
SERVER_VMEM = 48_000_000

# List prices, $ per million tokens: input, output, cache reads (the claude-api reference
# of 2026-10-06). A cache write costs 1.25 times the input for 5 minutes, 2 times for an
# hour. The CLI's own `total_cost_usd`, kept as `cli_cost_usd`, is not used: Claude Code
# 2.1.148 priced claude-sonnet-5-5 at $5 / $6.25 / $0.50 / $25 (input, cache writes,
# reads, output), which reproduces every run of 2026-10-17 to $0.001. Its
# --max-budget-usd is in those dollars too.
PRICES = {
    'claude-sonnet-5-5': (2.0, 10.0, 0.20),
    'claude-opus-5-5': (4.0, 20.0, 0.20),
    'claude-haiku-5-5': (0.10, 0.50, 0.01),
    'claude-haiku-4-5-20251001': (1.0, 5.0, 0.10),
}


def list_cost(model_usage, main, split):
    """The cost of a run at list prices, from the CLI's usage by model; `split` is the
    main model's cache writes by lifetime. Returns the cost and the models without a
    price."""
    total, unknown = 0.0, []
    for m, u in model_usage.items():
        if m not in PRICES:
            unknown.append(m)
            continue
        inp, out, read = PRICES[m]
        writes = u.get('cacheCreationInputTokens', 0)
        hour = min(writes, split.get('ephemeral_1h_input_tokens', 0)) if m == main else 0
        total += (u.get('inputTokens', 0) * inp + u.get('outputTokens', 0) * out
                  + u.get('cacheReadInputTokens', 0) * read + hour * 2 * inp + (writes - hour) * 1.25 * inp) / 1e6
    return round(total, 6), unknown


def theorem(name):
    name = NAMES.get(name, name)
    text = open(LIBRARY).read()
    ths = mm1.theorems(text)
    if name not in ths:
        sys.exit(f'{name}: not a theorem of {LIBRARY}')
    a, s, e, b = ths[name]
    return text[:a], text[s:e].rstrip(), text[e:b]


CHECK = r'''#!/usr/bin/env python3
"""Checks proof.mm1: the theorem's header, the proof, at the end of the library, compiled
with mm0-rs. Prints OK, or the errors. Every check is logged with what it cost."""
import json, os, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
HEADER = {header!r}
MM0RS = {mm0rs!r}
proof = open(os.path.join(HERE, 'proof.mm1')).read().strip() if os.path.exists(os.path.join(HERE, 'proof.mm1')) else ''
def log(entry):
    with open(os.path.join(HERE, '.check', 'log.jsonl'), 'a') as f:
        f.write(json.dumps(entry) + '\n')
os.makedirs(os.path.join(HERE, '.check'), exist_ok=True)
if not proof:
    print('proof.mm1 is empty: write the proof there, the text after `=`')
    sys.exit(1)
if ';' in proof or 'check-proofs' in proof:
    print('proof.mm1 must hold the proof only, without `;`')
    sys.exit(1)
src = open(os.path.join(HERE, 'library.mm1')).read()
target = os.path.join(HERE, '.check', 'target.mm1')
with open(target, 'w') as f:
    f.write(src + '\ndo {{ (check-proofs #t) }};\n' + HEADER + ' =\n' + proof + ';\n')
tf = os.path.join(HERE, '.check', 'time')
t0 = time.time()
r = subprocess.run(['/usr/bin/time', '-f', '%e %U %S %M', '-o', tf, MM0RS, 'compile', '-n', target],
                   capture_output=True, text=True)
elapsed, user, system, rss = open(tf).read().split()[-4:]
out = re.sub(r'\x1b\[[0-9;]*m', '', r.stdout + r.stderr)
ok = r.returncode == 0 and 'error' not in out and 'sorry' not in out
log({{'t': t0, 'ok': ok, 'exit': r.returncode, 'elapsed': float(elapsed), 'user': float(user),
     'sys': float(system), 'maxrss_kb': int(rss)}})
if ok:
    print('OK: the proof is accepted')
else:
    lines = [l for l in out.splitlines() if not re.match(r'^(elab|elabbed) ', l) and not re.match(r'^\d+ sorts, ', l)]
    print('\n'.join(lines).strip() or 'not accepted')
    sys.exit(1)
'''

SEARCH = r'''#!/usr/bin/env python3
"""./search REGEX [FILE]: the lines of FILE (library.mm1 by default; also {files}) that
match the regular expression REGEX (Python syntax), with their numbers; at most 100."""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
FILES = {files!r}
if len(sys.argv) < 2 or len(sys.argv) > 3 or (len(sys.argv) == 3 and sys.argv[2] not in FILES):
    print(__doc__.strip())
    sys.exit(2)
try:
    rx = re.compile(sys.argv[1])
except re.error as e:
    print(f'not a regular expression: {{e}}')
    sys.exit(2)
name = sys.argv[2] if len(sys.argv) == 3 else 'library.mm1'
hits = [(i + 1, l.rstrip('\n')) for i, l in enumerate(open(os.path.join(HERE, name))) if rx.search(l)]
for n, l in hits[:100]:
    print(f'{{n}}: {{l}}')
if len(hits) > 100:
    print(f'... {{len(hits)}} lines match; the first 100 are shown')
if not hits:
    print('no line matches')
'''

SERVER = '''#!/bin/sh
# The MCP server of Whitehead for this run, with what it costs measured.
ulimit -v {vmem}
exec /usr/bin/time -v -o {dir}/server.time {bin} mcp {spec} {mmb} --tactics {tactics} --log {dir}/trace.jsonl --export {dir}/found
'''


def prepare(original, agent, d):
    os.makedirs(d, exist_ok=True)
    name = NAMES.get(original, original)
    prefix, header, _ = theorem(original)
    with open(os.path.join(d, 'library.mm1'), 'w') as f:
        f.write(prefix)
    method = open(os.path.join(HERE, 'prompts', f'{agent}.md')).read().replace('{name}', name)
    prompt = open(os.path.join(HERE, 'prompts', 'common.md')).read()
    prompt = prompt.replace('{about}', ABOUT[bool(NAMES)]).replace('{name}', name).replace('{header}', header)
    prompt = prompt.replace('{method}', method.strip())
    with open(os.path.join(d, 'prompt.md'), 'w') as f:
        f.write(prompt)
    search = os.path.join(d, 'search')
    with open(search, 'w') as f:
        f.write(SEARCH.format(files=['library.mm1', 'mm1.md'] if agent == 'mm1' else ['library.mm1']))
    os.chmod(search, 0o755)
    if agent == 'mm1':
        check = os.path.join(d, 'check')
        with open(check, 'w') as f:
            f.write(CHECK.format(header=header, mm0rs=MM0RS))
        os.chmod(check, 0o755)
        shutil.copy(MM1_DOC, os.path.join(d, 'mm1.md'))
    elif agent == 'whitehead':
        server = os.path.join(d, 'server.sh')
        with open(server, 'w') as f:
            f.write(SERVER.format(vmem=SERVER_VMEM, dir=d, bin=BIN, spec=SPEC, mmb=MMB, tactics=TACTICS))
        os.chmod(server, 0o755)
        with open(os.path.join(d, 'mcp.json'), 'w') as f:
            json.dump({'mcpServers': {'whitehead': {'command': server, 'args': []}}}, f)
    else:
        sys.exit(f'unknown agent {agent}')
    with open(os.path.join(d, 'run.json'), 'w') as f:
        json.dump({'theorem': original, 'name': name, 'agent': agent, 'library': LIBDIR or 'original'}, f)


def option(args, key, default):
    if key in args:
        i = args.index(key)
        v = args[i + 1]
        del args[i:i + 2]
        return v
    return default


def check_dir(d):
    """An agent's directory must be outside /home, which its rules deny, and have no
    CLAUDE.md or .claude above it, which the CLI would load into the agent."""
    if os.path.realpath(d).startswith('/home/'):
        sys.exit(f'{d}: under /home, which the agents may not read; use a directory such as one under /tmp')
    p = os.path.dirname(os.path.realpath(d))
    while True:
        for x in ('CLAUDE.md', '.claude'):
            if os.path.exists(os.path.join(p, x)):
                sys.exit(f'{d}: {os.path.join(p, x)} is above it, and the CLI would load it into the agent')
        if p == '/':
            break
        p = os.path.dirname(p)


def run(name, agent, d, args):
    check_dir(d)
    model = option(args, '--model', 'claude-sonnet-5-5')
    effort = option(args, '--effort', 'high')
    turns = option(args, '--turns', '150')
    budget = option(args, '--budget', '5')
    timeout = int(option(args, '--timeout', '2400'))
    prepare(name, agent, d)
    prompt = open(os.path.join(d, 'prompt.md')).read()
    common = ['claude', '-p', prompt, '--model', model, '--effort', effort, '--output-format', 'stream-json',
              '--verbose', '--no-session-persistence', '--setting-sources', 'project', '--disable-slash-commands',
              '--strict-mcp-config', '--permission-mode', 'dontAsk', '--max-turns', turns,
              '--max-budget-usd', budget, '--disallowedTools', 'Read(//home/**)', 'Edit(//home/**)',
              'Write(//home/**)', 'WebFetch', 'WebSearch']
    if agent == 'whitehead':
        cmd = common + ['--mcp-config', os.path.join(d, 'mcp.json'), '--tools', 'Read,Bash',
                        '--allowedTools', 'mcp__whitehead', 'Read', 'Bash(./search:*)']
    else:
        cmd = common + ['--tools', 'Read,Write,Edit,Bash',
                        '--allowedTools', 'Read', 'Write', 'Edit', 'Bash(./check)', 'Bash(./check:*)', 'Bash(./search:*)']
    meta = json.load(open(os.path.join(d, 'run.json')))
    meta.update({'model': model, 'effort': effort, 'turns_limit': int(turns), 'budget_usd': float(budget),
                 'timeout_s': timeout, 'started': time.time()})
    with open(os.path.join(d, 'transcript.jsonl'), 'w') as out, open(os.path.join(d, 'stderr.txt'), 'w') as err:
        t0 = time.time()
        try:
            p = subprocess.run(cmd, cwd=d, stdout=out, stderr=err, timeout=timeout)
            meta['exit'] = p.returncode
        except subprocess.TimeoutExpired:
            meta['exit'] = 'timeout'
        meta['wall_s'] = time.time() - t0
    with open(os.path.join(d, 'run.json'), 'w') as f:
        json.dump(meta, f, indent=1)
    s = score(d)
    print(json.dumps(s))


def parse_time_v(path):
    """The figures of `/usr/bin/time -v`."""
    out = {}
    if not os.path.exists(path):
        return out
    for line in open(path):
        k, _, v = line.strip().rpartition(': ')
        if k == 'User time (seconds)':
            out['user_s'] = float(v)
        elif k == 'System time (seconds)':
            out['sys_s'] = float(v)
        elif k == 'Maximum resident set size (kbytes)':
            out['maxrss_kb'] = int(v)
        elif k.startswith('Elapsed (wall clock) time'):
            parts = [float(x) for x in v.split(':')]
            out['elapsed_s'] = sum(x * 60 ** i for i, x in enumerate(reversed(parts)))
    return out


def score(d):
    meta = json.load(open(os.path.join(d, 'run.json')))
    name, agent = meta['theorem'], meta['agent']
    s = {'theorem': name, 'agent': agent, 'model': meta.get('model'), 'effort': meta.get('effort'),
         'exit': meta.get('exit'), 'wall_s': round(meta.get('wall_s', 0), 1)}
    # the agent, from the transcript
    result, usage_by_id, tools = None, {}, {}
    for line in open(os.path.join(d, 'transcript.jsonl')):
        try:
            ev = json.loads(line)
        except ValueError:
            continue
        if ev.get('type') == 'result':
            result = ev
        elif ev.get('type') == 'assistant':
            msg = ev.get('message', {})
            if msg.get('id') and msg.get('usage'):
                usage_by_id[msg['id']] = msg['usage']
            for c in msg.get('content', []):
                if c.get('type') == 'tool_use':
                    tools[c['name']] = tools.get(c['name'], 0) + 1
    keys = ['input_tokens', 'cache_creation_input_tokens', 'cache_read_input_tokens', 'output_tokens']
    if result:
        u = result.get('usage', {})
        s.update({k: u.get(k, 0) for k in keys})
        cost, unknown = list_cost(result.get('modelUsage', {}), meta.get('model'), u.get('cache_creation', {}))
        s.update({'cost_usd': cost, 'cli_cost_usd': result.get('total_cost_usd'), 'unpriced_models': unknown,
                  'turns': result.get('num_turns'),
                  'duration_s': round(result.get('duration_ms', 0) / 1000, 1),
                  'api_s': round(result.get('duration_api_ms', 0) / 1000, 1),
                  'ending': result.get('subtype'), 'final': (result.get('result') or '')[-300:]})
    else:
        s.update({k: sum(u.get(k, 0) for u in usage_by_id.values()) for k in keys})
        main = {'inputTokens': s['input_tokens'], 'outputTokens': s['output_tokens'],
                'cacheReadInputTokens': s['cache_read_input_tokens'],
                'cacheCreationInputTokens': s['cache_creation_input_tokens']}
        hour = sum(u.get('cache_creation', {}).get('ephemeral_1h_input_tokens', 0) for u in usage_by_id.values())
        cost, unknown = list_cost({meta.get('model'): main}, meta.get('model'), {'ephemeral_1h_input_tokens': hour})
        s.update({'ending': 'no result (killed)', 'cost_usd': cost, 'unpriced_models': unknown})
    s['tokens'] = sum(s.get(k, 0) for k in keys)
    s['tool_calls'] = tools
    # the machine, and whether the proof is accepted by mm0-rs
    if agent == 'whitehead':
        s['machine'] = parse_time_v(os.path.join(d, 'server.time'))
        ms = 0
        trace = os.path.join(d, 'trace.jsonl')
        if os.path.exists(trace):
            for line in open(trace):
                for m in re.finditer(r'\\"ms\\": ?(\d+)', line):
                    ms += int(m.group(1))
        s['machine']['tool_ms'] = ms
        found = os.path.join(d, 'found', f"{meta.get('name', name)}.mmb")
        if os.path.exists(found):
            r = subprocess.run([MM0RS, 'compile', '-q', found], capture_output=True, text=True)
            s['accepted'] = r.returncode == 0
        else:
            s['accepted'] = False
    else:
        log = os.path.join(d, '.check', 'log.jsonl')
        entries = [json.loads(l) for l in open(log)] if os.path.exists(log) else []
        s['machine'] = {'checks': len(entries), 'user_s': round(sum(e['user'] for e in entries), 2),
                        'sys_s': round(sum(e['sys'] for e in entries), 2),
                        'elapsed_s': round(sum(e['elapsed'] for e in entries), 2),
                        'maxrss_kb': max((e['maxrss_kb'] for e in entries), default=0)}
        r = subprocess.run([os.path.join(d, 'check')], cwd=d, capture_output=True, text=True)
        s['accepted'] = r.returncode == 0 and r.stdout.startswith('OK')
        # the check run here is not the agent's
        if os.path.exists(log):
            lines = open(log).read().splitlines()
            with open(log, 'w') as f:
                f.write('\n'.join(lines[:len(entries)]) + ('\n' if entries else ''))
    with open(os.path.join(d, 'score.json'), 'w') as f:
        json.dump(s, f, indent=1)
    return s


def summary(dirs):
    rows = []
    for d in dirs:
        p = os.path.join(d, 'score.json')
        if os.path.exists(p):
            rows.append(json.load(open(p)))
    print('| theorem | agent | proved | tokens | of them output | cost $ | turns | agent s | machine CPU s | machine MB |')
    print('|---|---|---|---|---|---|---|---|---|---|')
    for s in rows:
        m = s.get('machine', {})
        cpu = m.get('user_s', 0) + m.get('sys_s', 0)
        print(f"| {s['theorem']} | {s['agent']} | {'yes' if s.get('accepted') else 'no'} | {s.get('tokens', 0):,} | "
              f"{s.get('output_tokens', 0):,} | {s.get('cost_usd') or 0:.2f} | {s.get('turns')} | {s.get('duration_s')} | "
              f"{cpu:.1f} | {m.get('maxrss_kb', 0) // 1024} |")


def main():
    args = sys.argv[1:]
    if not args:
        sys.exit(__doc__)
    cmd = args.pop(0)
    if cmd == 'prepare':
        prepare(args[0], args[1], os.path.abspath(args[2]))
    elif cmd == 'run':
        run(args[0], args[1], os.path.abspath(args[2]), args[3:])
    elif cmd == 'score':
        print(json.dumps(score(os.path.abspath(args[0])), indent=1))
    elif cmd == 'summary':
        summary(args)
    else:
        sys.exit(__doc__)


if __name__ == '__main__':
    main()
