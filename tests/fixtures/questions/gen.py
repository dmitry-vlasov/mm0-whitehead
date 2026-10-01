#!/usr/bin/env python3
"""Hand-assembles the tiny .mmb files in this directory.

Each file isolates one point where the written spec (mm0.md, mm0-c/mmb.md, the
Lean formalization mm0-lean/mm0/mm0.lean) and the reference verifier mm0-c may
disagree. They are evidence for the open questions in docs/MMB-NOTES.md, and
they become differential-test cases once the questions are answered.

Usage: ./gen.py            (rewrites the .mmb files next to this script)

To try one by hand:
    mm0-c bound_arg_vars.mmb < bound_arg_vars.mm0 ; echo $?
"""

import struct
from pathlib import Path

HERE = Path(__file__).resolve().parent

# Sort modifiers (mmb.md, "Sort Table").
PURE, STRICT, PROVABLE, FREE = 1, 2, 4, 8

# Statement opcodes.
STMT_AXIOM, STMT_SORT, STMT_TERM, STMT_THM = 0x02, 0x04, 0x05, 0x06
# Proof opcodes.
TERM, TERM_SAVE, REF, DUMMY, THM, HYP = 0x10, 0x11, 0x12, 0x13, 0x14, 0x16
CONV, REFL, UNFOLD = 0x17, 0x18, 0x1B
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


def assemble(sorts, terms, thms, stmts):
    """sorts: [mods]; terms: [(args, ret, is_def, unify|None)];
    thms: [(args, unify)]; stmts: [bytes] in declaration order."""
    header_len = 40
    out = align8(bytes(header_len) + bytes(sorts))
    p_terms = len(out)
    out += bytes(8 * len(terms))
    p_thms = len(out)
    out += bytes(8 * len(thms))

    term_rows, thm_rows = [], []
    for args, ret, is_def, unify in terms:
        out = align8(out)
        term_rows.append((len(args), (ret >> 56) & 0x7F | (0x80 if is_def else 0), len(out)))
        out += b''.join(struct.pack('<Q', a) for a in args + [ret])
        if is_def:
            out += unify
    for args, unify in thms:
        out = align8(out)
        thm_rows.append((len(args), len(out)))
        out += b''.join(struct.pack('<Q', a) for a in args)
        out += unify

    p_proof = len(out)
    # The final END must start at least 5 bytes before the end of the file.
    out += b''.join(stmts) + END + bytes(4)

    out = bytearray(out)
    struct.pack_into('<4sBBHIIIIIIQ', out, 0, b'MM0B', 1, len(sorts), 0,
                     len(terms), len(thms), p_terms, p_thms, p_proof, 0, 0)
    for i, (n, sort, p) in enumerate(term_rows):
        struct.pack_into('<HBBI', out, p_terms + 8 * i, n, sort, 0, p)
    for i, (n, p) in enumerate(thm_rows):
        struct.pack_into('<HHI', out, p_thms + 8 * i, n, 0, p)
    return bytes(out)


WFF, SET = 0, 1
SORTS = [PROVABLE, 0]


def ax5_instance(pred_args, pred_ret):
    """sorts wff, set; al, <pred>, imp; ax5; and a theorem applying ax5 with
    ph := (<pred> x).  Only the binder of <pred> differs between files."""
    AL, PRED, IMP = 0, 1, 2
    terms = [
        ([bound(SET, 0), reg(WFF, 1)], reg(WFF), False, None),   # al {x} (ph: wff x): wff
        (pred_args, pred_ret, False, None),                       # <pred>
        ([reg(WFF), reg(WFF)], reg(WFF), False, None),            # imp (a b: wff): wff
    ]
    thms = [
        # ax5 {x: set} (ph: wff): $ imp ph (al x ph) $
        ([bound(SET, 0), reg(WFF)],
         cmd(UTERM, IMP) + cmd(UREF, 1) + cmd(UTERM, AL) + cmd(UREF, 0) + cmd(UREF, 1) + END),
        # bad {x: set}: $ imp (<pred> x) (al x (<pred> x)) $
        ([bound(SET, 0)],
         cmd(UTERM, IMP) + cmd(UTERM_SAVE, PRED) + cmd(UREF, 0)
         + cmd(UTERM, AL) + cmd(UREF, 0) + cmd(UREF, 1) + END),
    ]
    stmts = [
        stmt(STMT_SORT), stmt(STMT_SORT),
        stmt(STMT_TERM), stmt(STMT_TERM), stmt(STMT_TERM),
        stmt(STMT_AXIOM,
             cmd(REF, 1) + cmd(REF, 0) + cmd(REF, 1) + cmd(TERM, AL) + cmd(TERM, IMP) + END),
        stmt(STMT_THM,
             cmd(REF, 0)                               # x                    (ax5 arg 0)
             + cmd(REF, 0) + cmd(TERM_SAVE, PRED)      # (<pred> x) = heap[1] (ax5 arg 1)
             + cmd(REF, 1) + cmd(REF, 0) + cmd(REF, 1) + cmd(TERM, AL) + cmd(TERM, IMP)
             + cmd(THM, 0) + END),
    ]
    return assemble(SORTS, terms, thms, stmts)


MM0 = """delimiter $ ( $ $ ) $;
provable sort wff;
sort set;
term al {{x: set}} (ph: wff x): wff;
term {pred};
term imp (a b: wff): wff;
axiom ax5 {{x: set}} (ph: wff): $ imp ph (al x ph) $;
theorem bad {{x: set}}: $ imp ({name} x) (al x ({name} x)) $;
"""

def one_assert(kind, body, extra_terms=(), extra_stmts=()):
    """provable sort wff; term tru: wff; then one axiom or theorem stating
    $ tru $ with the given body. `extra_terms`/`extra_stmts` go in between."""
    terms = [([], reg(0), False, None)] + list(extra_terms)
    thms = [([], cmd(UTERM, 0) + END)]
    stmts = [stmt(STMT_SORT), stmt(STMT_TERM)] + list(extra_stmts) + [stmt(kind, body)]
    return assemble([PROVABLE], terms, thms, stmts)


TRIV_MM0 = """provable sort wff;
term tru: wff;
theorem triv: $ tru $;
"""

SORRY, STMT_LOCAL_DEF = 0x20, 0x0D

FILES = {
    # D1. ph := (foo x) where x sits in a *bound* argument position of foo and
    # foo's result is declared to depend on it. mm0.md and mm0.lean count x among
    # the variables of (foo x); mm0-c's Term rule adds nothing for a bound argument.
    'bound_arg_vars': (ax5_instance([bound(SET, 0)], reg(WFF, 1)),
                       MM0.format(pred='foo {x: set}: wff x', name='foo')),
    # D1 control: the same proof with x in a *regular* argument position. Every
    # reading rejects this one (disjoint variable violation).
    'regular_arg_vars': (ax5_instance([reg(SET)], reg(WFF)),
                         MM0.format(pred='p (x: set): wff', name='p')),
    # D6. Sorry on an expression: tru, Sorry  ==>  |- tru.
    'sorry_expr': (one_assert(STMT_THM, cmd(TERM, 0) + cmd(SORRY) + END), TRIV_MM0),
    # D6. Sorry on an obligation: tru, |- tru', Conv  ==>  |- tru, tru =?= tru';
    # then Sorry should discharge the obligation according to mmb.md.
    'sorry_conv': (one_assert(STMT_THM, cmd(TERM, 0) + cmd(TERM, 0) + cmd(SORRY) + cmd(CONV)
                              + cmd(SORRY) + END), TRIV_MM0),
    # D8. A LocalDef statement whose table entry is not a def: a term `hidden: wff`
    # that the .mm0 file never mentions.
    'local_term': (one_assert(STMT_AXIOM, cmd(TERM, 0) + END,
                              extra_terms=[([], reg(0), False, None)],
                              extra_stmts=[stmt(STMT_LOCAL_DEF)]),
                   TRIV_MM0.replace('theorem triv', 'axiom ax')),
}

if __name__ == '__main__':
    for name, (mmb, mm0) in FILES.items():
        (HERE / f'{name}.mmb').write_bytes(mmb)
        (HERE / f'{name}.mm0').write_text(mm0)
        print(f'wrote {name}.mmb ({len(mmb)} bytes), {name}.mm0')
