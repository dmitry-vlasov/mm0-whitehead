#!/usr/bin/env python3
"""The library with its theorems renamed, so that an agent cannot recall their proofs.

The agents of the bench know `peano.mm1`: on its own names, an agent writes the proof of
a theorem from memory (round 1 of 2026-10-17). Here every theorem is renamed `L` and its
number, in the order of the file, wherever its name occurs: in proofs, in `do` blocks,
in comments; not inside formulas or strings. Sorts, terms, definitions, notations and
axioms keep their names: they are the language the statements are written in.

    rename.py <file.mm1> <spec.mm0> <outdir>

writes `<outdir>/peano.mm1`, `<outdir>/peano.mm0` (the specification, renamed the same
way), `<outdir>/names.json` (old name -> new name) and compiles the renamed file to
`<outdir>/peano.mmb` with mm0-rs. A name that Lisp code builds from a string, which the
renaming cannot follow, shows as an error of that compilation.
"""
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mm1  # noqa: E402

# a name of MM1; a `'` before one is the quote of Lisp
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_.]*")


def rename_text(text, names):
    """`text` with each identifier that `names` maps renamed, outside formulas `$ ... $` and
    strings."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '-' and text.startswith('--', i):
            # a comment, to the end of the line: its words are renamed, a `$` in it is text
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(re.sub(r"(?<![A-Za-z0-9_.-])[A-Za-z_][A-Za-z0-9_.]*(?![A-Za-z0-9_.-])",
                              lambda m: names.get(m.group(0), m.group(0)), text[i:j]))
            i = j
        elif c == '$':
            j = text.find('$', i + 1)
            j = n if j < 0 else j + 1
            out.append(text[i:j])
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            out.append(text[i:j + 1])
            i = j + 1
        elif c.isalpha() or c == '_':
            m = IDENT.match(text, i)
            word = m.group(0)
            # a symbol of Lisp may go on with characters such as `-`, `!`, `?`: the word
            # is renamed only when it ends there
            k = m.end()
            if k < n and text[k] in '-!?*<>=+/':
                j = k
                while j < n and (text[j].isalnum() or text[j] in "_.-!?*<>=+/"):
                    j += 1
                out.append(text[i:j])
                i = j
                continue
            if i > 0 and (text[i - 1].isalnum() or text[i - 1] in "_.-"):
                out.append(word)
            else:
                out.append(names.get(word, word))
            i = k
        else:
            out.append(c)
            i += 1
    return ''.join(out)


def main():
    mm1_path, spec_path, outdir = sys.argv[1:4]
    os.makedirs(outdir, exist_ok=True)
    text = open(mm1_path).read()
    order = list(mm1.theorems(text))
    names = {name: f'L{k + 1:04d}' for k, name in enumerate(order)}
    renamed = rename_text(text, names)
    with open(os.path.join(outdir, 'peano.mm1'), 'w') as f:
        f.write(renamed)
    with open(os.path.join(outdir, 'peano.mm0'), 'w') as f:
        f.write(rename_text(open(spec_path).read(), names))
    with open(os.path.join(outdir, 'names.json'), 'w') as f:
        json.dump(names, f, indent=0)
    mm0rs = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))),
                         '.tools', 'bin', 'mm0-rs')
    r = subprocess.run([mm0rs, 'compile', os.path.join(outdir, 'peano.mm1'), os.path.join(outdir, 'peano.mmb')],
                       capture_output=True, text=True)
    out = re.sub(r'\x1b\[[0-9;]*m', '', r.stdout + r.stderr)
    errors = [l for l in out.splitlines() if l.startswith('error')]
    print(f'{len(names)} theorems renamed; mm0-rs: exit {r.returncode}, {len(errors)} errors')
    for l in errors[:20]:
        print(' ', l)
    if r.returncode:
        print(out[-3000:])


if __name__ == '__main__':
    main()
