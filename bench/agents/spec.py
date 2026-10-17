"""The full specification of an MM1 file: every statement but its proofs, as `.mm0`.

A `do` block and the annotations are dropped, so are `pub` and `local`, an `abstract`
def loses its value, and a theorem keeps its header only. The `.mmb` that the MM1 file compiles to then proves it, theorem for theorem, so
that a server reading it knows every theorem's binders and notation (the `.mm0` of the
repository lists the `pub` theorems only).

    python3 spec.py file.mm1 > full.mm0
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mm1  # noqa: E402

LEAD = re.compile(r'(?:pub|local|abstract)\s+')


def full_spec(text):
    out = []
    for a, b in mm1.statements(text):
        s = mm1.code_start(text, a, b)
        if text.startswith('do', s) and not text[s + 2:s + 3].isalnum() and text[s + 2:s + 3] != '_':
            continue
        body = text[s:b]
        abstract = False
        while m := LEAD.match(body):
            abstract = abstract or m.group(0).startswith('abstract')
            body = body[m.end():]
        if abstract and body.startswith('def'):
            # an abstract def is a def without its value in the specification
            e = mm1.header_end(body, 0, len(body))
            if e is not None:
                body = body[:e].rstrip() + ';'
        if body.startswith('theorem'):
            e = mm1.header_end(body, 0, len(body))
            if e is not None:
                body = body[:e].rstrip() + ';'
        out.append(body)
    return '\n'.join(out) + '\n'


if __name__ == '__main__':
    sys.stdout.write(full_spec(open(sys.argv[1]).read()))
