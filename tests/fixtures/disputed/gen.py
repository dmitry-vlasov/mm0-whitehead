#!/usr/bin/env python3
"""Hand-assembles the tiny .mmb files in this directory.

Each file isolates one point where the sources disagree: the formal semantics
(mm0.md, examples/mm0.mm0, mm0-lean/mm0/*.lean), the written format description
(mm0-c/mmb.md), the reference implementation mm0-rs, and mm0-c. They are the
evidence for section 9 of docs/MMB-NOTES.md, which says what each implementation
does with each file and what our verifier must do.

Usage: ./gen.py            (rewrites the .mmb and .mm0 files next to this script)

To try one by hand:
    mm0-rs compile bound_arg_vars.mmb ; echo $?
    mm0-c bound_arg_vars.mmb < bound_arg_vars.mm0 ; echo $?
"""

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
from mmbasm import *  # noqa: E402,F401  (the assembler shared by all fixture scripts)


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
    # An axiom whose proof stream builds `tru` while its unify stream, which is
    # what a later `Thm` uses, says `fls`.
    'axiom_body_mismatch': (
        assemble([PROVABLE],
                 [([], reg(0), False, None), ([], reg(0), False, None)],
                 [([], cmd(UTERM, 1) + END)],
                 [stmt(STMT_SORT), stmt(STMT_TERM), stmt(STMT_TERM),
                  stmt(STMT_AXIOM, cmd(TERM, 0) + END)]),
        'provable sort wff;\nterm tru: wff;\nterm fls: wff;\naxiom ax: $ fls $;\n'),
    # A term whose table entry says sort 1 while its return type says sort 0.
    'ret_sort_mismatch': (
        assemble([PROVABLE, 0], [([], reg(0), False, None, 1)], [],
                 [stmt(STMT_SORT), stmt(STMT_SORT), stmt(STMT_TERM)]),
        'provable sort wff;\nsort set;\nterm t: wff;\n'),
}

if __name__ == '__main__':
    for name, (mmb, mm0) in FILES.items():
        (HERE / f'{name}.mmb').write_bytes(mmb)
        (HERE / f'{name}.mm0').write_text(mm0)
        print(f'wrote {name}.mmb ({len(mmb)} bytes), {name}.mm0')
