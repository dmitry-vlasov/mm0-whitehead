#!/usr/bin/env python3
"""A hand assembler for small .mmb files, used by the gen.py scripts in the
subdirectories. It writes exactly what it is told, valid or not: the fixtures
it produces include deliberately wrong files.

The layout is the one of docs/MMB-NOTES.md, sections 2 to 5 and 7.
"""

import struct

# Sort modifiers (mmb.md, "Sort Table").
PURE, STRICT, PROVABLE, FREE = 1, 2, 4, 8

# Statement opcodes.
STMT_AXIOM, STMT_SORT, STMT_TERM, STMT_THM = 0x02, 0x04, 0x05, 0x06
STMT_LOCAL_DEF, STMT_LOCAL_THM = 0x0D, 0x0E
# Proof opcodes.
TERM, TERM_SAVE, REF, DUMMY, THM, THM_SAVE, HYP = 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16
CONV, REFL, SYMM, CONG, UNFOLD, CONV_CUT, CONV_SAVE, SAVE, SORRY = (
    0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1E, 0x1F, 0x20)
# Unify opcodes.
UTERM, UTERM_SAVE, UREF, UDUMMY, UHYP = 0x30, 0x31, 0x32, 0x33, 0x36


def cmd(op, data=0):
    """One (cmd, data) pair in the shortest encoding."""
    if data == 0:
        return bytes([op])
    if data < 1 << 8:
        return bytes([op | 0x40, data])
    if data < 1 << 16:
        return bytes([op | 0x80]) + struct.pack('<H', data)
    return bytes([op | 0xC0]) + struct.pack('<I', data)


END = cmd(0)


def bound(sort, bit):
    """arg for the `bit`-th bound variable."""
    return (1 << 63) | (sort << 56) | (1 << bit)


def reg(sort, deps=0):
    """arg for a regular variable; `deps` is a bitset of bound variables."""
    return (sort << 56) | deps


def stmt(op, body=b''):
    """A statement: opcode, then the length of the whole statement as data."""
    # Statements here are short, so the 1-byte data form always fits.
    n = 2 + len(body)
    assert n < 256
    return bytes([op | 0x40, n]) + body


def align8(buf):
    return buf + bytes(-len(buf) % 8)


def assemble(sorts, terms, thms, stmts, names=None):
    """sorts: [mods]; terms: [(args, ret, is_def, unify|None[, table sort])];
    thms: [(args, unify)]; stmts: [bytes] in declaration order. The optional
    fifth element of a term overrides the sort stored in the term table, which
    otherwise is the sort of `ret`.

    names, if given, adds an index with the Name, VarN and HypN tables:
    {'sorts': [str], 'terms': [str], 'thms': [str], 'term_vars': [[str]],
     'thm_vars': [[str]], 'thm_hyps': [[str]]}."""
    header_len = 40
    out = align8(bytes(header_len) + bytes(sorts))
    p_terms = len(out)
    out += bytes(8 * len(terms))
    p_thms = len(out)
    out += bytes(8 * len(thms))

    term_rows, thm_rows = [], []
    for args, ret, is_def, unify, *table_sort in terms:
        out = align8(out)
        sort = table_sort[0] if table_sort else (ret >> 56) & 0x7F
        term_rows.append((len(args), sort | (0x80 if is_def else 0), len(out)))
        out += b''.join(struct.pack('<Q', a) for a in args + [ret])
        if is_def:
            out += unify
    for args, unify in thms:
        out = align8(out)
        thm_rows.append((len(args), len(out)))
        out += b''.join(struct.pack('<Q', a) for a in args)
        out += unify

    p_proof = len(out)
    # Where each statement starts, by the table it consumes an entry of.
    decl_pos = {'sort': [], 'term': [], 'thm': []}
    for st in stmts:
        op = st[0] & 0x3F
        kind = 'sort' if op == STMT_SORT else 'term' if op & 0x07 == STMT_TERM else 'thm'
        decl_pos[kind].append(len(out))
        out += st
    # The final END must start at least 5 bytes before the end of the file.
    out += END + bytes(4)

    p_index = 0
    if names is not None:
        out = bytearray(align8(out))

        def cstr(text):
            p = len(out)
            out.extend(text.encode() + b'\0')
            return p

        def str_list(strs):
            ptrs = [cstr(x) for x in strs]
            while len(out) % 8:
                out.append(0)
            p = len(out)
            out.extend(struct.pack('<Q', len(ptrs)) + b''.join(struct.pack('<Q', q) for q in ptrs))
            return p

        name_ptrs = [cstr(x) for x in names['sorts'] + names['terms'] + names['thms']]
        var_lists = [str_list(v) for v in names['term_vars'] + names['thm_vars']]
        hyp_lists = [str_list(h) for h in names['thm_hyps']]
        while len(out) % 8:
            out.append(0)
        p_names = len(out)
        positions = decl_pos['sort'] + decl_pos['term'] + decl_pos['thm']
        for pos, ptr in zip(positions, name_ptrs):
            out.extend(struct.pack('<QQ', pos, ptr))
        p_vars = len(out)
        out.extend(b''.join(struct.pack('<Q', q) for q in var_lists))
        p_hyps = len(out)
        out.extend(b''.join(struct.pack('<Q', q) for q in hyp_lists))
        p_index = len(out)
        out.extend(struct.pack('<Q', 3))
        for ty, ptr in ((b'Name', p_names), (b'VarN', p_vars), (b'HypN', p_hyps)):
            out.extend(struct.pack('<4sIQ', ty, 0, ptr))

    out = bytearray(out)
    struct.pack_into('<4sBBHIIIIIIQ', out, 0, b'MM0B', 1, len(sorts), 0,
                     len(terms), len(thms), p_terms, p_thms, p_proof, 0, p_index)
    for i, (n, sort, p) in enumerate(term_rows):
        struct.pack_into('<HBBI', out, p_terms + 8 * i, n, sort, 0, p)
    for i, (n, p) in enumerate(thm_rows):
        struct.pack_into('<HHI', out, p_thms + 8 * i, n, 0, p)
    return bytes(out)
