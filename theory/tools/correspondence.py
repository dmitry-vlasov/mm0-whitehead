"""The generated parts of docs/CORRESPONDENCE.md, from tools/out/decls.jsonl (tools/Extract.lean):

  docs/correspondence/<theorem>_backbone.svg, _full.svg   -- the lemma dependency graphs (graphviz `dot`)
  docs/correspondence/reading-order.md                    -- the declarations by file, in reading order
  docs/correspondence/graph-report.txt                    -- closures, fan-in, edges, plumbing, as text

Run from anywhere: python3 -I theory/tools/correspondence.py [more theorem names]
"""
import collections, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
THEORY = os.path.dirname(HERE)
ROOT = os.path.dirname(THEORY)
OUT = os.path.join(HERE, 'out')
DOCS = os.path.join(ROOT, 'docs', 'correspondence')

def read_objects(path):
    dec = json.JSONDecoder(); s = open(path).read(); i = 0; out = []
    while True:
        while i < len(s) and s[i].isspace(): i += 1
        if i >= len(s): break
        o, i = dec.raw_decode(s, i); out.append(o)
    return out

def is_noise(d):
    n = d['name']; last = n.split('.')[-1]
    if re.match(r'(below|brecOn|rec|ibelow|binductionOn)_\d+$', last) or last == 'default': return True
    if d['line'] == 0 and d['kind'] in ('def', 'abbrev', 'theorem') and \
       any(t in n for t in ('match_', '.go', 'proof_', 'eq_', 'brecOn', 'below', '.elim', '.decEq', '.repr')): return True
    return False

D = {d['name']: d for d in read_objects(os.path.join(OUT, 'decls.jsonl')) if not is_noise(d)}
IMPORTS = {m['module']: m['imports'] for m in read_objects(os.path.join(OUT, 'modules.jsonl'))}

# the reading order: each file after everything it imports, the first variant together
ORDER = ["Theory.Term", "Theory.Subst", "Theory.Unification", "Theory.Deduction", "Theory.Search", "Theory.Spt",
         "Theory.Preserve", "Theory.Closing", "Theory.General", "Theory.Generality", "Theory.Completeness",
         "Theory.Unify", "Theory.Engine", "Theory.Keyed", "Theory.KeyedLemmas", "Theory.KeyedCorr",
         "Theory.Oriented", "Theory.KeyedExact", "Theory.Defs", "Theory.Rules", "Theory.ToD", "Theory.OfD",
         "Theory.Theorems"]
for m in IMPORTS:
    if m not in ORDER: ORDER.append(m)
pos = {m: i for i, m in enumerate(ORDER)}
for m, imps in IMPORTS.items():
    for i in imps:
        assert pos[i] < pos[m], f"reading order violates import {m} <- {i}"

def owner(n):
    d = D.get(n)
    if d and d['kind'] == 'constructor':
        p = n.rsplit('.', 1)[0]
        if p in D: return p
    return n
THMS = {n for n, d in D.items() if d['kind'] == 'theorem'}
def vdeps(n): return {owner(x) for x in D[n]['valueDeps'] if owner(x) in D and owner(x) != n}
def closure(root):
    seen = set(); stack = [root]
    while stack:
        x = stack.pop()
        if x in seen: continue
        seen.add(x)
        stack.extend(y for y in vdeps(x) if y in THMS and y not in seen)
    seen.discard(root); return seen
def short(n): return n[len('Theory.'):] if n.startswith('Theory.') else n
def loc(n): d = D[n]; return f"{d['module'].split('.', 1)[1]}.lean:{d['line']}"
def firstsent(doc):
    if not doc: return ''
    doc = ' '.join(doc.split()); m = re.match(r'(.+?[.!?])(\s|$)', doc)
    return m.group(1) if m else doc

NAMED = set()  # the names THEORY.md mentions in backticks
for line in open(os.path.join(ROOT, 'docs', 'THEORY.md')):
    NAMED.update(re.findall(r"`([A-Za-z_][A-Za-z0-9_.']*)`", line))
# the lemmas the sketches of CORRESPONDENCE.md name beyond those: in the backbone pictures too
BACKBONE = set("""soundness_valid generality' completeness' run_inv sptE_inv anodeEntries_inv init_inv expandAll_inv
 expandNode_inv tryAssertion_inv addNode_inv recordAt_inv mark_inv valid_of_inv shape_of_inv conds_proofOf joinAll_absorbs
 joinAll_typed joinAll_idem Subst.solves_eqs_iff Absorbs.of_comp stepSub_apply stepSub_typed Shape.subst close_isProof
 conds_name holds_closing allVars_close entry_mostGeneral joinAll_mostGeneral sim anodes_nodup sibling_disjoint
 matches_of_congruent assign_keys build_typed build_f_renamed build_f_lt proofOf_subst stepSub_comp
 Subst.comp_eq_of_instance mem_names_apply holds_of_instance treeOf_at entry_exists fuel_le tried_of_lt anode_round
 children_lt_of_parent expandAll_expanded_iff run_expanded_iff override_solves sptE_mono congruent_of_matches
 run_le_of_le State.Le.trans mem_chain_of_at chain_eq le_of_mem_enodes StateInv.mono ANodeInv.mono closing_typed
 vars_closing_apply consts_closing_apply Subst.vars_apply Subst.consts_apply Subst.ty_apply Subst.Typed.comp
 conds_subst exprs_subst stepConds_restrict Subst.restrict_apply Subst.apply_comp Subst.comp_assoc""".split())
def is_backbone(x):
    s = short(x); return bool(D[x]['doc']) or s in NAMED or s.split('.')[-1] in NAMED or s in BACKBONE

def backbone_edges(root, C):
    nodes = {x for x in C if is_backbone(x)} | {root}; edges = set(); allowed = C | {root}
    for x in nodes:
        seen = set(); stack = list(vdeps(x) & allowed)
        while stack:
            y = stack.pop()
            if y in seen: continue
            seen.add(y)
            if y in nodes:
                if y != x: edges.add((x, y))
            else: stack.extend(vdeps(y) & allowed)
    return nodes, edges

PALETTE = ["#e8f0fe", "#e6f4ea", "#fef7e0", "#fce8e6", "#f3e8fd", "#e0f7fa", "#fff3e0", "#ede7f6", "#e0f2f1",
           "#f1f8e9", "#fbe9e7", "#f5f5f5"]
def write_dot(path, root, nodes, edges, title):
    bymod = collections.defaultdict(list)
    for x in nodes: bymod[D[x]['module']].append(x)
    L = ["digraph G {", 'rankdir=BT; node [shape=box, style="rounded,filled", fontname="Helvetica", fontsize=10];'
         ' edge [color="#777777", arrowsize=0.6];', f'labelloc=t; label="{title}"; fontname="Helvetica";']
    for m in ORDER:
        if m not in bymod: continue
        L.append(f'subgraph "cluster_{m}" {{ label="{m.split(".", 1)[1]}.lean"; style="rounded"; color="#bbbbbb";'
                 f' bgcolor="{PALETTE[pos[m] % len(PALETTE)]}";')
        for x in sorted(bymod[m], key=lambda x: D[x]['line']):
            mark = 'penwidth=2.5, color="#c62828"' if x == root else ''
            L.append(f'  "{x}" [label="{short(x)}" fillcolor="white" {mark}];')
        L.append('}')
    L += [f'  "{a}" -> "{b}";' for a, b in sorted(edges)] + ['}']
    open(path, 'w').write('\n'.join(L))

def graphs(roots):
    os.makedirs(DOCS, exist_ok=True); report = []
    for root in roots:
        name = short(root).replace("'", "_"); C = closure(root)
        nodes, edges = backbone_edges(root, C); allnodes = C | {root}
        alledges = {(x, y) for x in allnodes for y in vdeps(x) if y in allnodes}
        write_dot(os.path.join(DOCS, f'{name}_backbone.dot'), root, nodes, edges,
                  f'{short(root)}: the lemmas with a docstring or a name in THEORY.md or in the sketches of CORRESPONDENCE.md ({len(nodes)} of {len(C) + 1});'
                  ' an edge points at a lemma the proof uses, directly or through unnamed plumbing')
        write_dot(os.path.join(DOCS, f'{name}_full.dot'), root, allnodes, alledges,
                  f'{short(root)}: every theorem its proof rests on ({len(allnodes)}), by file')
        for kind in ('backbone', 'full'):
            dot = os.path.join(DOCS, f'{name}_{kind}.dot')
            r = subprocess.run(['dot', '-Tsvg', dot, '-o', os.path.join(DOCS, f'{name}_{kind}.svg')],
                               capture_output=True, text=True)
            if r.returncode: print(name, kind, r.stderr[:300], file=sys.stderr)
            os.remove(dot)
        fan = collections.Counter(y for x in allnodes for y in vdeps(x) if y in allnodes)
        report.append(f"## {short(root)}  (closure {len(C)} theorems, backbone {len(nodes) - 1})")
        report.append("direct deps: " + ", ".join(short(y) for y in sorted(vdeps(root) & THMS)))
        report.append("\nbackbone nodes (fan-in within closure | own theorem closure | file:line):")
        for x in sorted(nodes - {root}, key=lambda x: (-fan[x], pos[D[x]['module']], D[x]['line'])):
            report.append(f"  {fan[x]:3d} | {len(closure(x)):3d} | {loc(x):24s} {short(x)}")
        report.append("\nbackbone edges:")
        byx = collections.defaultdict(list)
        for a, b in edges: byx[a].append(b)
        for a in sorted(byx, key=lambda x: (pos[D[x]['module']], D[x]['line'])):
            report.append(f"  {short(a)} -> {', '.join(sorted(short(b) for b in byx[a]))}")
        report.append("\nlemmas in the closure that are not in the backbone (plumbing), by file:")
        plumb = collections.defaultdict(list)
        for x in C - nodes: plumb[D[x]['module']].append(short(x))
        for m in ORDER:
            if m in plumb: report.append(f"  {m.split('.', 1)[1]}: {len(plumb[m])}: {', '.join(sorted(plumb[m]))}")
        report.append("")
    open(os.path.join(DOCS, 'graph-report.txt'), 'w').write('\n'.join(report))

def header(m):
    s = open(os.path.join(THEORY, m.replace('.', '/') + '.lean')).read()
    return ' '.join(s[2:s.find('-/')].split()) if s.startswith('/-') else ''

def reading_order():
    out = ["# The declarations of `theory/Theory`, in reading order", "",
           "Generated by `theory/tools/correspondence.py` from `tools/Extract.lean`'s output: every",
           "structure and inductive, every definition with a docstring, every theorem with a docstring",
           "or a name in `docs/THEORY.md`, by file in the order of `docs/CORRESPONDENCE.md`, §5, and",
           "within a file by line. The first sentence of the docstring stands for the declaration.", ""]
    total = 0
    for m in ORDER:
        rows = sorted((d for d in D.values() if d['module'] == m), key=lambda d: d['line'])
        sel = []
        for d in rows:
            s = short(d['name']); last = s.split('.')[-1]; named = s in NAMED or last in NAMED
            if d['kind'] == 'opaque' or (d['kind'] == 'instance' and not d['doc']): continue
            if d['kind'] in ('structure', 'inductive', 'class') or (d['doc'] and d['kind'] != 'theorem') or \
               (d['kind'] == 'theorem' and (d['doc'] or named)) or named:
                sel.append(d)
        total += len(sel)
        out.append(f"### `{m.replace('.', '/')}.lean` ({len(rows)} declarations, {len(sel)} listed)\n")
        h = header(m)
        if h: out.append(h + "\n")
        out += ["| line | declaration | kind | what it is |", "|---:|---|---|---|"]
        out += [f"| {d['line']} | `{short(d['name'])}` | {d['kind']} | {firstsent(d['doc']).replace('|', '\\|')} |" for d in sel]
        out.append("")
    open(os.path.join(DOCS, 'reading-order.md'), 'w').write('\n'.join(out))
    print(f"reading order: {total} of {len(D)} declarations")

if __name__ == '__main__':
    roots = ["Theory.soundness", "Theory.generality", "Theory.completeness"] + \
            ['Theory.' + a if not a.startswith('Theory.') else a for a in sys.argv[1:]]
    graphs(roots); reading_order()
    print("written to", DOCS)
