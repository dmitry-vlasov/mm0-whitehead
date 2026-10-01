#!/usr/bin/env python3
"""Hand-assembles small.mmb and small.mm0: a valid proof file that is small enough
to check by eye and still has one of everything the reader must decode: an index
with names, a definition with a dummy variable, hypotheses, a local theorem, and a
proof by conversion (Conv, Unfold, Refl).

Both mm0-rs (mm0-rs compile small.mmb) and mm0-c (mm0-c small.mmb < small.mm0)
accept it. The reader tests decode it and compare its dump with small.dump.

Usage: ./gen.py            (rewrites small.mmb and small.mm0 next to this script)
"""

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from mmbasm import *  # noqa: E402,F401

WFF, SET = 0, 1
IMP, AL, DBL, ALLSELF = 0, 1, 2, 3
MP, AX1, T, T2, LOC = 0, 1, 2, 3, 4

MM0 = """delimiter $ ( $ $ ) $;
provable sort wff;
sort set;
term imp (a b: wff): wff;
term al {x: set} (ph: wff x): wff;
def dbl (a: wff): wff = $ imp a a $;
def allself (ph: wff) {.y: set}: wff = $ al y ph $;
axiom mp (a b: wff): $ a $ > $ imp a b $ > $ b $;
axiom ax1 (a: wff): $ imp a a $;
theorem t (a: wff): $ dbl a $;
theorem t2 (a b: wff) (h1: $ a $) (h2: $ imp a b $): $ b $;
"""

terms = [
    # imp (a b: wff): wff
    ([reg(WFF), reg(WFF)], reg(WFF), False, None),
    # al {x: set} (ph: wff x): wff
    ([bound(SET, 0), reg(WFF, 1)], reg(WFF), False, None),
    # def dbl (a: wff): wff = imp a a
    ([reg(WFF)], reg(WFF), True, cmd(UTERM, IMP) + cmd(UREF, 0) + cmd(UREF, 0) + END),
    # def allself (ph: wff) {.y: set}: wff = al y ph
    ([reg(WFF)], reg(WFF), True, cmd(UTERM, AL) + cmd(UDUMMY, SET) + cmd(UREF, 0) + END),
]

thms = [
    # mp (a b: wff): $ a $ > $ imp a b $ > $ b $   -- conclusion, then hypotheses reversed
    ([reg(WFF), reg(WFF)],
     cmd(UREF, 1)
     + cmd(UHYP) + cmd(UTERM, IMP) + cmd(UREF, 0) + cmd(UREF, 1)
     + cmd(UHYP) + cmd(UREF, 0) + END),
    # ax1 (a: wff): $ imp a a $
    ([reg(WFF)], cmd(UTERM, IMP) + cmd(UREF, 0) + cmd(UREF, 0) + END),
    # t (a: wff): $ dbl a $
    ([reg(WFF)], cmd(UTERM, DBL) + cmd(UREF, 0) + END),
    # t2 (a b: wff): $ a $ > $ imp a b $ > $ b $
    ([reg(WFF), reg(WFF)],
     cmd(UREF, 1)
     + cmd(UHYP) + cmd(UTERM, IMP) + cmd(UREF, 0) + cmd(UREF, 1)
     + cmd(UHYP) + cmd(UREF, 0) + END),
    # local theorem loc (a: wff): $ imp a a $
    ([reg(WFF)], cmd(UTERM, IMP) + cmd(UREF, 0) + cmd(UREF, 0) + END),
]

stmts = [
    stmt(STMT_SORT), stmt(STMT_SORT),
    stmt(STMT_TERM), stmt(STMT_TERM),
    # dbl: the value imp a a
    stmt(STMT_TERM, cmd(REF, 0) + cmd(REF, 0) + cmd(TERM, IMP) + END),
    # allself: Dummy puts y on the stack and on the heap (heap[1])
    stmt(STMT_TERM, cmd(DUMMY, SET) + cmd(REF, 0) + cmd(TERM, AL) + END),
    # mp: a, Hyp; imp a b, Hyp; then the conclusion b
    stmt(STMT_AXIOM,
         cmd(REF, 0) + cmd(HYP)
         + cmd(REF, 0) + cmd(REF, 1) + cmd(TERM, IMP) + cmd(HYP)
         + cmd(REF, 1) + END),
    # ax1: imp a a
    stmt(STMT_AXIOM, cmd(REF, 0) + cmd(REF, 0) + cmd(TERM, IMP) + END),
    # t: |- dbl a, from |- imp a a by unfolding dbl
    stmt(STMT_THM,
         cmd(REF, 0) + cmd(TERM, DBL)                      # dbl a
         + cmd(REF, 0)                                     # a                  (ax1 argument)
         + cmd(REF, 0) + cmd(REF, 0) + cmd(TERM_SAVE, IMP)  # imp a a = heap[1]  (the claim)
         + cmd(THM, AX1)                                   # dbl a, |- imp a a
         + cmd(CONV)                                       # |- dbl a, dbl a =?= imp a a
         + cmd(REF, 1)                                     # ..., imp a a
         + cmd(UNFOLD)                                     # |- dbl a, imp a a =?= imp a a
         + cmd(REFL)                                       # |- dbl a
         + END),
    # t2: the hypotheses become heap[2] and heap[3]; then mp
    stmt(STMT_THM,
         cmd(REF, 0) + cmd(HYP)                                    # heap[2] = |- a
         + cmd(REF, 0) + cmd(REF, 1) + cmd(TERM, IMP) + cmd(HYP)   # heap[3] = |- imp a b
         + cmd(REF, 2) + cmd(REF, 3)                               # the two subproofs
         + cmd(REF, 0) + cmd(REF, 1)                               # a, b      (mp arguments)
         + cmd(REF, 1)                                             # b         (the claim)
         + cmd(THM, MP) + END),
    # loc: a local theorem, |- imp a a by ax1, saved and then unused
    stmt(STMT_LOCAL_THM,
         cmd(REF, 0) + cmd(REF, 0) + cmd(REF, 0) + cmd(TERM, IMP) + cmd(THM_SAVE, AX1) + END),
]

names = {
    'sorts': ['wff', 'set'],
    'terms': ['imp', 'al', 'dbl', 'allself'],
    'thms': ['mp', 'ax1', 't', 't2', 'loc'],
    'term_vars': [['a', 'b'], ['x', 'ph'], ['a'], ['ph', 'y']],
    'thm_vars': [['a', 'b'], ['a'], ['a'], ['a', 'b'], ['a']],
    'thm_hyps': [['h1', 'h2'], [], [], ['h1', 'h2'], []],
}

if __name__ == '__main__':
    mmb = assemble([PROVABLE, 0], terms, thms, stmts, names)
    (HERE / 'small.mmb').write_bytes(mmb)
    (HERE / 'small.mm0').write_text(MM0)
    print(f'wrote small.mmb ({len(mmb)} bytes), small.mm0')
