#!/usr/bin/env python3
"""Check that a remapped Peregrine λ□ program no longer computes on the
representation of scalars and points.

usage: check_abstract.py PROG.ast PREFIX...

Computes the declarations reachable from the main term of PROG.ast and fails
if one of them has a body (or is an inductive) and its dotted name starts
with one of the PREFIXes, e.g. Stdlib.Zmod (the integers modulo l and p),
Fiat (the curve arithmetic) and Curve.Ed25519 (the operations of Zl and Ed
that were not remapped).  Remapped constants have no body and pass.

Run it with run_deep.py, which sets GMPZ's scripts on the path through the
environment variable GMPZ.
"""
import os, sys
sys.path.insert(0, os.environ['GMPZ'])
from splice_locked import parse, kn_str, env_of, refs
from remap_const import dotted


def main(prog_f, *prefixes):
    prog = parse(open(prog_f).read())
    env = env_of(prog)
    by_kn = {kn_str(d[0]): d for d in env}
    names = {kn_str(d[0]): dotted(d[0][0]) + '.' + d[0][1].strip('"') for d in env}
    seen, todo = set(), sorted(refs(prog[2:], set()))
    while todo:
        k = todo.pop()
        if k in seen or k not in by_kn:
            continue
        seen.add(k)
        todo.extend(refs(by_kn[k][1], set()) - {k})
    bad = []
    for k in sorted(seen):
        d = by_kn[k]
        has_body = d[1][0] != 'ConstantDecl' or d[1][1][1] not in ('None', ['Some', 'tBox'])
        if has_body and any(names[k].startswith(p) for p in prefixes):
            bad.append(names[k])
    print('check_abstract: %d reachable declarations' % len(seen))
    if bad:
        sys.exit('check_abstract: the program still computes with\n  ' + '\n  '.join(bad))


if __name__ == '__main__':
    main(*sys.argv[1:])
