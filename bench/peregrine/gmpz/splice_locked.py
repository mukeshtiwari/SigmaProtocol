#!/usr/bin/env python3
"""Replace axioms in a Peregrine λ□ program (S-expression) by definitions.

usage: splice_locked.py PROGRAM.ast IMPLS.ast OUT.ast

mathcomp's HB.lock turns a definition X into an axiom X.body for extraction.
IMPLS.ast is the extraction of demo/extraction/LockedImpls.v, which defines
X_impl as the right-hand side of X.unlock.  For each pair in SPLICE, the body
of X_impl becomes the body of the axiom X.body; declarations X_impl depends
on that PROGRAM lacks are inserted next to it.  SSProve's real-number axiom R
is only used inside distributions, which the interpreter never evaluates; it
becomes a box.
"""
import sys

def tokenize(s):
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c.isspace():
            i += 1
        elif c in '()':
            yield c
            i += 1
        elif c == '"':
            j = i + 1
            while s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            yield s[i:j + 1]
            i = j + 1
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in '()':
                j += 1
            yield s[i:j]
            i = j

def parse(s):
    stack = [[]]
    for t in tokenize(s):
        if t == '(':
            stack.append([])
        elif t == ')':
            x = stack.pop()
            stack[-1].append(x)
        else:
            stack[-1].append(t)
    return stack[0][0]

def dump(x, out):
    if isinstance(x, list):
        out.append('(')
        for k, y in enumerate(x):
            if k:
                out.append(' ')
            dump(y, out)
        out.append(')')
    else:
        out.append(x)

def kn_str(kn):
    out = []
    dump(kn, out)
    return ''.join(out)

def env_of(prog):
    # (Untyped ENV MAIN?)
    assert prog[0] == 'Untyped', prog[0]
    return prog[1]

def refs(x, acc):
    """Kernames a term refers to: constants and inductives."""
    if isinstance(x, list):
        if len(x) == 2 and x[0] == 'tConst':
            acc.add(kn_str(x[1]))
        elif len(x) == 3 and x[0] == 'inductive':
            acc.add(kn_str(x[1]))
        for y in x:
            refs(y, acc)
    return acc

def topo_sort(env):
    """Order the environment newest first with every declaration after the
    declarations that refer to it (dependencies are older)."""
    by_kn = {kn_str(d[0]): d for d in env}
    order, state = [], {}
    sys.setrecursionlimit(100000)
    def visit(k):
        if state.get(k) == 2 or k not in by_kn:
            return
        if state.get(k) == 1:
            return  # cycle through a mutual block; keep the current order
        state[k] = 1
        for r in sorted(refs(by_kn[k][1], set())):
            if r != k:
                visit(r)
        state[k] = 2
        order.append(by_kn[k])
    for d in reversed(env):
        visit(kn_str(d[0]))
    return list(reversed(order))

SPLICE = {
    '((MPdot (MPfile ("bigop" "boot" "mathcomp")) "bigop") "body")': 'bigop_impl',
    '((MPdot (MPdot (MPdot (MPfile ("fintype" "boot" "mathcomp")) "FiniteNES") "Finite") "enum") "body")': 'enum_impl',
    '((MPdot (MPfile ("fintype" "boot" "mathcomp")) "card") "body")': 'card_impl',
    '((MPdot (MPfile ("fintype" "boot" "mathcomp")) "enum_rank_in") "body")': 'enum_rank_in_impl',
}
BOX = {'((MPfile ("Axioms" "Crypt" "SSProve")) "R")'}

def main(prog_f, impl_f, out_f):
    prog = parse(open(prog_f).read())
    impl = parse(open(impl_f).read())
    penv, ienv = env_of(prog), env_of(impl)
    present = {kn_str(d[0]) for d in penv}
    impl_by_name = {d[0][-1].strip('"'): d for d in ienv if 'LockedImpls' in kn_str(d[0])}
    # declarations of IMPLS missing from PROGRAM, in IMPLS order (newest first), excluding the *_impl themselves
    missing = [d for d in ienv if kn_str(d[0]) not in present and 'LockedImpls' not in kn_str(d[0])]
    new_env, inserted = [], False
    for d in penv:
        k = kn_str(d[0])
        if k in SPLICE:
            src = impl_by_name[SPLICE[k]]
            d = [d[0], ['ConstantDecl', ['constant_body', src[1][1][1]]]]
            new_env.append(d)
            if not inserted:
                new_env.extend(missing)
                inserted = True
            continue
        if k in BOX:
            d = [d[0], ['ConstantDecl', ['constant_body', ['Some', 'tBox']]]]
        new_env.append(d)
    prog[1] = topo_sort(new_env)
    out = []
    dump(prog, out)
    open(out_f, 'w').write(''.join(out))
    print('spliced', len(SPLICE), 'locked bodies; inserted', len(missing), 'declarations')

if __name__ == '__main__':
    main(*sys.argv[1:4])
