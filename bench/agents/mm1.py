"""MM1 files cut into their top-level statements, for the tasks of the agent bench.

A statement ends at a `;` outside parentheses, brackets, braces, formulas `$ ... $`,
strings and `--` comments. A theorem is a statement whose first word, after `pub` or
`local`, is `theorem`; its header is the text before its proof, the `=` at the top level.
"""
import re


def statements(text):
    """The top-level statements of `text`: (start, end) offsets, each ending after its `;`,
    with the comments and blank lines before it included."""
    out = []
    i, n = 0, len(text)
    start = 0
    depth = 0
    while i < n:
        c = text[i]
        if c == '-' and text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c == '$':
            j = text.find('$', i + 1)
            i = n if j < 0 else j + 1
            continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            i = j + 1
            continue
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif c == ';' and depth == 0:
            out.append((start, i + 1))
            start = i + 1
        i += 1
    return out


def skip_sexpr(text, i, b):
    """The offset after the s-expression at `i`: a parenthesized one, or a word."""
    if i < b and text[i] in '([{':
        depth = 0
        while i < b:
            c = text[i]
            if c == '"':
                j = i + 1
                while j < b and text[j] != '"':
                    j += 2 if text[j] == '\\' else 1
                i = j + 1
                continue
            if c == '$':
                j = text.find('$', i + 1)
                i = b if j < 0 else j + 1
                continue
            if c in '([{':
                depth += 1
            elif c in ')]}':
                depth -= 1
                if depth == 0:
                    return i + 1
            i += 1
        return b
    while i < b and not text[i].isspace() and text[i] not in '()[]{}':
        i += 1
    return i


def code_start(text, a, b):
    """The offset of the first character of statement [a, b) that is not a comment, blank
    or annotation (`@` and an s-expression): where its keywords start."""
    i = a
    while i < b:
        if text[i].isspace():
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = b if j < 0 else j + 1
        elif text[i] == '@':
            i = skip_sexpr(text, i + 1, b)
        else:
            return i
    return b


HEAD = re.compile(r'(?:(?:pub|local)\s+)*theorem\s+([A-Za-z0-9_.\']+)')


def header_end(text, a, b):
    """The offset of the `=` that starts the proof of the theorem at [a, b), at the top
    level and outside formulas; None if it has no proof (a theorem declared without one)."""
    i, depth = a, 0
    while i < b:
        c = text[i]
        if c == '-' and text.startswith('--', i):
            j = text.find('\n', i)
            i = b if j < 0 else j + 1
            continue
        if c == '$':
            j = text.find('$', i + 1)
            i = b if j < 0 else j + 1
            continue
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif c == '=' and depth == 0:
            return i
        i += 1
    return None


def theorems(text):
    """The theorems of `text`: name -> (statement start, code start, header end, end)."""
    out = {}
    for a, b in statements(text):
        s = code_start(text, a, b)
        m = HEAD.match(text, s)
        if not m:
            continue
        e = header_end(text, s, b)
        if e is None:
            continue
        out[m.group(1)] = (a, s, e, b)
    return out
