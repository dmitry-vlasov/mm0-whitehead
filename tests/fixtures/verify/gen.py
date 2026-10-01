#!/usr/bin/env python3
"""Hand-assembles one small proof file per rule of the verifier.

Every file is a common base theory plus one more statement, which either is valid or
breaks exactly one rule. The table CASES gives, for each file, what our verifier must
say (OK, or a fragment of the error message) and what the two other implementations
say (A accept, R reject): mm0-rs as `mm0-rs compile x.mmb`, mm0-c as `mm0-c-np x.mmb`.

    ./gen.py              writes the .mmb files and cases.tsv
    ./gen.py --observe    also runs mm0-rs and mm0-c-np from .tools/bin and reports
                          every verdict that differs from the table

cases.tsv is read by tests/Tests/Verify/Cases.lean, which checks our verdict always and
the other two when the tools are built. Where the three do not agree, the last column
names the point of docs/MMB-NOTES.md section 9 that explains it.
"""

import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from mmbasm import *  # noqa: E402,F401

WFF, SET, ST, PU, FR = 0, 1, 2, 3, 4
SORTS = [PROVABLE, 0, STRICT, PURE, FREE]

IMP, AL, DBL, ALLSELF, TWO = 0, 1, 2, 3, 4
NEW_TERM = 5
MP, AX1, AX5, AX2B = 0, 1, 2, 3
NEW_THM = 4


def R(i): return cmd(REF, i)
def T(t): return cmd(TERM, t)
def TS(t): return cmd(TERM_SAVE, t)
def UR(i): return cmd(UREF, i)
def UT(t): return cmd(UTERM, t)
def UTS(t): return cmd(UTERM_SAVE, t)


BASE_TERMS = [
    # imp (a b: wff): wff
    ([reg(WFF), reg(WFF)], reg(WFF), False, None),
    # al {x: set} (ph: wff x): wff
    ([bound(SET, 0), reg(WFF, 1)], reg(WFF), False, None),
    # def dbl (a: wff): wff = imp a a
    ([reg(WFF)], reg(WFF), True, UT(IMP) + UR(0) + UR(0) + END),
    # def allself (ph: wff) {.y: set}: wff = al y ph
    ([reg(WFF)], reg(WFF), True, UT(AL) + cmd(UDUMMY, SET) + UR(0) + END),
    # def two (ph: wff) {.y .z: set}: wff = al y (al z ph)
    ([reg(WFF)], reg(WFF), True,
     UT(AL) + cmd(UDUMMY, SET) + UT(AL) + cmd(UDUMMY, SET) + UR(0) + END),
]

BASE_THMS = [
    # mp (a b: wff): $ a $ > $ imp a b $ > $ b $
    ([reg(WFF), reg(WFF)],
     UR(1) + cmd(UHYP) + UT(IMP) + UR(0) + UR(1) + cmd(UHYP) + UR(0) + END),
    # ax1 (a: wff): $ imp a a $
    ([reg(WFF)], UT(IMP) + UR(0) + UR(0) + END),
    # ax5 {x: set} (ph: wff): $ imp ph (al x ph) $
    ([bound(SET, 0), reg(WFF)], UT(IMP) + UR(1) + UT(AL) + UR(0) + UR(1) + END),
    # ax2b {x y: set} (ph: wff x y): $ imp ph ph $
    ([bound(SET, 0), bound(SET, 1), reg(WFF, 3)], UT(IMP) + UR(2) + UR(2) + END),
]

BASE_STMTS = [
    stmt(STMT_SORT), stmt(STMT_SORT), stmt(STMT_SORT), stmt(STMT_SORT), stmt(STMT_SORT),
    stmt(STMT_TERM), stmt(STMT_TERM),
    stmt(STMT_TERM, R(0) + R(0) + T(IMP) + END),
    stmt(STMT_TERM, cmd(DUMMY, SET) + R(0) + T(AL) + END),
    stmt(STMT_TERM, cmd(DUMMY, SET) + cmd(DUMMY, SET) + R(0) + T(AL) + T(AL) + END),
    stmt(STMT_AXIOM,
         R(0) + cmd(HYP) + R(0) + R(1) + T(IMP) + cmd(HYP) + R(1) + END),
    stmt(STMT_AXIOM, R(0) + R(0) + T(IMP) + END),
    stmt(STMT_AXIOM, R(1) + R(0) + R(1) + T(AL) + T(IMP) + END),
    stmt(STMT_AXIOM, R(2) + R(2) + T(IMP) + END),
]


def build(terms=(), thms=(), stmts=()):
    return assemble(SORTS, BASE_TERMS + list(terms), BASE_THMS + list(thms),
                    BASE_STMTS + list(stmts))


def thm(args, unify, body, kind=STMT_THM):
    """The base plus one axiom or theorem (number NEW_THM)."""
    return build(thms=[(args, unify + END)], stmts=[stmt(kind, body + END)])


def term(args, ret, unify=None, body=None):
    """The base plus one term, or one def if it has a unify stream (number NEW_TERM)."""
    if unify is None:
        return build(terms=[(args, ret, False, None)], stmts=[stmt(STMT_TERM)])
    return build(terms=[(args, ret, True, unify + END)], stmts=[stmt(STMT_TERM, body + END)])


A = [reg(WFF)]          # (a: wff)
X_PH = [bound(SET, 0), reg(WFF, 1)]   # {x: set} (ph: wff x)

# D = dbl a (heap 1), I = imp a a (heap 2), the claim imp D D, a proof of imp I I,
# Conv, Cong, and the first obligation D =?= I proved by unfolding and saved (heap 3).
CONV_PREFIX = (
    R(0) + TS(DBL) + R(1) + T(IMP)
    + R(0) + R(0) + T(IMP) + cmd(SAVE)
    + R(2) + R(2) + T(IMP) + cmd(THM, AX1)
    + cmd(CONV) + cmd(CONG)
    + cmd(CONV_CUT) + R(2) + cmd(UNFOLD) + cmd(REFL) + cmd(CONV_SAVE))

OK = 'OK'

# name, bytes, ours, mm0-rs, mm0-c, note
CASES = [
    ('base', build(), OK, 'A', 'A', ''),

    # ---- valid proofs
    # imp (dbl a) (dbl a) from imp (imp a a) (imp a a): every conversion command
    ('conv_all',
     thm(A, UT(IMP) + UTS(DBL) + UR(0) + UR(1),
         CONV_PREFIX + cmd(SYMM) + cmd(SYMM) + R(3)),
     OK, 'A', 'A', ''),
    # (ph: wff) (h: ph): allself ph, through a dummy: ax5 with x := y, mp, unfold
    ('dummy_thm',
     thm(A, UT(ALLSELF) + UR(0) + cmd(UHYP) + UR(0),
         R(0) + cmd(HYP)
         + R(0) + T(ALLSELF)
         + R(1)
         + cmd(DUMMY, SET) + R(0)
         + R(0) + R(2) + R(0) + TS(AL) + T(IMP)
         + cmd(THM, AX5)
         + R(0) + R(3) + R(3) + cmd(THM, MP)
         + cmd(CONV) + R(3) + cmd(UNFOLD) + cmd(REFL)),
     OK, 'A', 'A', ''),

    # ---- the stack machine
    ('stack_underflow', thm(A, UR(0), T(IMP)), 'stack underflow', 'R', 'R', ''),
    ('ref_range', thm(A, UR(0), R(9)), 'heap entry 9 does not exist', 'R', 'R', ''),
    ('term_forward', term(A, reg(WFF), UR(0), R(0) + T(NEW_TERM)),
     'not declared before this statement', 'A', 'R', 'point 8'),
    ('thm_forward', thm(A, UR(0), R(0) + R(0) + cmd(THM, NEW_THM)),
     'not declared before this statement', 'R', 'R', ''),
    ('term_arg_sort', thm([reg(SET), reg(WFF)], UR(1), R(0) + R(1) + T(IMP)),
     'Term: argument 0 has sort 1', 'R', 'R', ''),
    ('bound_position', thm([reg(SET), reg(WFF)], UR(1), R(0) + R(1) + T(AL)),
     'must be a bound variable', 'R', 'R', ''),
    ('dummy_strict', thm(A, UR(0), cmd(DUMMY, ST)), 'strict or free', 'R', 'R', ''),
    ('dummy_free', thm(A, UR(0), cmd(DUMMY, FR)), 'strict or free', 'R', 'R', ''),
    ('dummy_sort_range', thm(A, UR(0), cmd(DUMMY, 9)), 'sort 9 is not declared', 'R', 'R', ''),
    ('hyp_not_provable', thm([reg(SET)], UR(0), R(0) + cmd(HYP)), 'provable sort', 'R', 'R', ''),
    ('thm_in_def', term(A, reg(WFF), UR(0), R(0) + R(0) + cmd(THM, AX1)),
     'Thm in a definition', 'A', 'R', 'point 8'),
    ('hyp_in_def', term(A, reg(WFF), UR(0), R(0) + cmd(HYP)),
     'Hyp in a definition', 'A', 'R', 'point 8'),
    ('thm_arg_sort', thm([reg(SET), reg(WFF)], UT(IMP) + UR(1) + UR(1),
                         R(0) + R(1) + R(1) + T(IMP) + cmd(THM, AX1)),
     'Thm: argument 0 has sort 1', 'R', 'R', ''),
    ('thm_missing_subproof', thm([reg(WFF), reg(WFF)], UR(1),
                                 R(0) + R(1) + R(1) + cmd(THM, MP)),
     'subproof is missing', 'R', 'R', ''),
    ('conv_no_proof', thm(A, UR(0), R(0) + R(0) + cmd(CONV)), 'expected a proof', 'R', 'R', ''),

    # ---- conversions
    # the unfolded side is built a second time instead of being saved: the two
    # `imp a a` are equal as trees and are different nodes
    ('refl_not_identical',
     thm(A, UT(DBL) + UR(0),
         R(0) + T(DBL)
         + R(0) + R(0) + R(0) + T(IMP) + cmd(THM, AX1)
         + cmd(CONV)
         + R(0) + R(0) + T(IMP) + cmd(UNFOLD) + cmd(REFL)),
     'not the same expression', 'R', 'R', ''),
    ('cong_mismatch',
     thm(X_PH, UT(AL) + UR(0) + UR(1),
         R(0) + R(1) + T(AL)
         + R(1) + R(1) + R(1) + T(IMP) + cmd(THM, AX1)
         + cmd(CONV) + cmd(CONG)),
     'not applications of the same term', 'R', 'R', ''),
    ('unfold_nondef',
     thm(A, UT(IMP) + UR(0) + UR(0),
         R(0) + R(0) + T(IMP)
         + R(0) + R(0) + R(0) + T(IMP) + cmd(THM, AX1)
         + cmd(CONV) + R(0) + cmd(UNFOLD)),
     'is not a definition', 'R', 'R', ''),
    ('unfold_wrong',
     thm(A, UT(DBL) + UR(0),
         R(0) + T(DBL)
         + R(0) + R(0) + R(0) + T(IMP) + cmd(THM, AX1)
         + cmd(CONV) + R(0) + cmd(UNFOLD)),
     'unify failure', 'R', 'R', ''),
    ('save_coconv',
     thm(A, UT(DBL) + UR(0),
         R(0) + T(DBL)
         + R(0) + R(0) + R(0) + T(IMP) + cmd(THM, AX1)
         + cmd(CONV) + cmd(SAVE)),
     'cannot be saved', 'R', 'R', ''),
    ('convref_mismatch',
     thm(A, UT(IMP) + UTS(DBL) + UR(0) + UR(1), CONV_PREFIX + cmd(SYMM) + R(3)),
     'not the obligation on the stack', 'R', 'R', ''),

    # ---- disjoint variables
    ('dv_bound_twice',
     thm(X_PH, UT(IMP) + UR(1) + UR(1),
         R(0) + R(0) + R(1) + R(1) + R(1) + T(IMP) + cmd(THM, AX2B)),
     'occurs in an earlier argument', 'R', 'R', ''),
    ('dv_regular',
     thm(X_PH, UT(IMP) + UR(1) + UT(AL) + UR(0) + UR(1),
         R(0) + R(1) + R(1) + R(0) + R(1) + T(AL) + T(IMP) + cmd(THM, AX5)),
     'not declared to depend on', 'R', 'R', ''),
    # unfolding allself with its dummy taken to be x, which ph depends on
    ('udummy_in_args',
     thm(X_PH, UT(ALLSELF) + UR(1) + cmd(UHYP) + UT(AL) + UR(0) + UR(1),
         R(0) + R(1) + TS(AL) + cmd(HYP)
         + R(1) + T(ALLSELF) + R(3) + cmd(CONV)
         + R(2) + cmd(UNFOLD)),
     'also occurs in the arguments or is another dummy', 'R', 'R', ''),
    # unfolding two with both dummies taken to be the same variable
    ('udummy_twice',
     thm(A, UT(TWO) + UR(0) + cmd(UHYP) + UR(0),
         R(0) + cmd(HYP)
         + R(0) + T(TWO) + R(1) + cmd(CONV)
         + cmd(DUMMY, SET) + R(2) + R(0) + T(AL) + T(AL) + cmd(UNFOLD)),
     'also occurs in the arguments or is another dummy', 'R', 'R', ''),

    # ---- definitions
    ('def_free_var', term(X_PH, reg(WFF), UR(1), R(1)),
     'free variables that the return type does not declare', 'R', 'R', ''),
    ('def_sort', term([bound(SET, 0)], reg(WFF), UR(0), R(0)),
     'the value has sort 1', 'R', 'R', ''),
    ('def_unify_mismatch', term(A, reg(WFF), UR(0), R(0) + R(0) + T(IMP)),
     'unify failure', 'A', 'R', 'point 8'),
    ('def_two_on_stack', term(A, reg(WFF), UR(0), R(0) + R(0)),
     'exactly one expression', 'A', 'R', 'point 8'),

    # ---- binders
    ('binder_strict_bound', term([bound(ST, 0)], reg(WFF)), 'strict sort', 'R', 'R', ''),
    ('binder_bound_deps', term([(1 << 63) | (SET << 56) | 2], reg(WFF)),
     'exactly its own bit', 'A', 'R', 'point 11'),
    ('binder_deps_later', term([reg(WFF, 1), bound(SET, 0)], reg(WFF)),
     'not declared before it', 'R', 'R', ''),
    ('ret_bound', term([], (1 << 63) | (WFF << 56)), 'marked as a bound variable', 'R', 'R', ''),
    ('ret_deps', term([], reg(WFF, 1)), 'the return type depends', 'R', 'R', ''),
    ('pure_result', term([], reg(PU)), 'pure sort', 'R', 'R', ''),
    ('many_bound', term([bound(SET, i) for i in range(55)] + [(1 << 63) | (SET << 56) | (1 << 55)],
                        reg(WFF)),
     'more than 55 bound variables', 'A', 'R', 'point 10'),
    ('sort_forward',
     assemble([PROVABLE, 0], [([reg(1)], reg(0), False, None)], [],
              [stmt(STMT_SORT), stmt(STMT_TERM), stmt(STMT_SORT)]),
     'sort 1 is not declared before this statement', 'R', 'R', ''),

    # ---- the end of a statement
    ('axiom_two_on_stack', thm(A, UR(0), R(0) + R(0), STMT_AXIOM),
     'exactly one element', 'A', 'R', 'point 8'),
    ('axiom_with_proof', thm(A, UT(IMP) + UR(0) + UR(0),
                             R(0) + R(0) + R(0) + T(IMP) + cmd(THM, AX1), STMT_AXIOM),
     'must leave its statement, an expression', 'A', 'R', 'point 8'),
    ('thm_with_expr', thm(A, UT(IMP) + UR(0) + UR(0), R(0) + R(0) + T(IMP)),
     'must leave a proof', 'R', 'R', ''),
    ('concl_not_provable', thm([reg(SET)], UR(0), R(0), STMT_AXIOM),
     'provable sort', 'R', 'R', ''),
    # proves `a` from the hypothesis `a`, for a statement that has no hypothesis
    ('hyp_extra', thm(A, UR(0), R(0) + cmd(HYP) + R(1)),
     'more hypotheses than the statement', 'R', 'R', ''),
    ('hyp_missing', thm(A, UR(0) + cmd(UHYP) + UR(0), R(0), STMT_AXIOM),
     'more hypotheses than the proof declares', 'A', 'R', 'point 8'),
    # proves imp I I with I = imp a a, for the statement imp a a
    ('concl_mismatch',
     thm(A, UT(IMP) + UR(0) + UR(0),
         R(0) + R(0) + TS(IMP) + R(1) + R(1) + T(IMP) + cmd(THM, AX1)),
     'unify failure', 'R', 'R', ''),
    ('counters', build(terms=[(A, reg(WFF), False, None)]),
     'the header has', 'A', 'R', 'point 20'),
]


def observe(name):
    tools = HERE.parent.parent.parent / '.tools' / 'bin'
    path = HERE / f'{name}.mmb'
    rs = subprocess.run([tools / 'mm0-rs', 'compile', '-q', path], capture_output=True)
    c = subprocess.run([tools / 'mm0-c-np', path], stdin=subprocess.DEVNULL, capture_output=True)
    return ('A' if rs.returncode == 0 else 'R'), ('A' if c.returncode == 0 else 'R')


if __name__ == '__main__':
    lines = []
    for name, mmb, ours, rs, c, note in CASES:
        (HERE / f'{name}.mmb').write_bytes(mmb)
        lines.append('\t'.join([name, ours, rs, c, note]))
    (HERE / 'cases.tsv').write_text('\n'.join(lines) + '\n')
    print(f'wrote {len(CASES)} files and cases.tsv')
    if '--observe' in sys.argv:
        bad = 0
        for name, _, _, rs, c, _ in CASES:
            got = observe(name)
            if got != (rs, c):
                bad += 1
                print(f'  {name}: table says mm0-rs {rs}, mm0-c {c}; observed mm0-rs {got[0]}, mm0-c {got[1]}')
        print('all oracle verdicts are as in the table' if bad == 0
              else f'{bad} cases differ from the table')
