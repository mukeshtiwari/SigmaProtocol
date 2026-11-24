#!/usr/bin/env python3
"""Remap constants of a Peregrine λ□ program to C functions.

usage: remap_const.py PROG.ast PROG.attrs OUT.ast OUT.attrs HEADER NAME=CFUN/ARITY...

NAME is the full dotted name of a constant, e.g.
Curve.Ed25519.Ed25519.Ed.fast_smul (file path, then the modules).  Its body
is removed, so that Peregrine's dead-code elimination drops the code only it
used, and the attribute file maps it to the C function CFUN of ARITY
arguments declared in HEADER; CFUN takes the thread_info first (it may
allocate in the CertiRocq heap and call the collector), unless the
specification ends in /pure (NAME=CFUN/ARITY/pure): then CFUN takes only the
arguments and must not allocate.  A NAME preceded by ? is remapped if the
program has it and skipped otherwise; any other missing NAME is an error.  This is the
mechanism by which splice_gmp_z.py maps the operations of Z to GMP; it is
trusted in the same way: nothing checks that CFUN computes the constant.

Run it with run_deep.py, like the other scripts of the GMP remapping (GMPZ),
whose splice_locked.py it imports from the directory in the environment
variable GMPZ.
"""
import os, sys
sys.path.insert(0, os.environ['GMPZ'])
from splice_locked import parse, dump, kn_str, env_of

def dotted(mp):
    if mp[0] == 'MPfile':
        return '.'.join(s.strip('"') for s in reversed(mp[1]))
    if mp[0] == 'MPdot':
        return dotted(mp[1]) + '.' + mp[2].strip('"')
    raise ValueError(mp)

def main(prog_f, attrs_f, out_f, out_attrs_f, header, *specs):
    want = {}
    optional = set()
    for s in specs:
        name, _, rhs = s.partition('=')
        if name.startswith('?'):
            name = name[1:]
            optional.add(name)
        cfun, arity, *flags = rhs.split('/')
        want[name] = (cfun, int(arity), 'pure' not in flags)
    prog = parse(open(prog_f).read())
    env = env_of(prog)
    remaps, found = [], set()
    for i, d in enumerate(env):
        name = dotted(d[0][0]) + '.' + d[0][1].strip('"')
        if name in want and d[1][0] == 'ConstantDecl':
            env[i] = [d[0], ['ConstantDecl', ['constant_body', 'None']]]
            cfun, arity, gc = want[name]
            remaps.append('(%s (remapped_constant (Some "%s") %d %s false "%s"))'
                          % (kn_str(d[0]), header, arity, 'true' if gc else 'false', cfun))
            found.add(name)
            print('remapped %s to %s' % (name, cfun))
    missing = set(want) - found - optional
    if missing:
        sys.exit('remap_const: no constant %s' % ', '.join(sorted(missing)))
    out = []
    dump(prog, out)
    open(out_f, 'w').write(''.join(out))
    attrs = open(attrs_f).read()
    head = '(attributes_config () ('
    assert attrs.startswith(head), attrs[:40]
    open(out_attrs_f, 'w').write(head + ' '.join(remaps) + ' ' + attrs[len(head):])

if __name__ == '__main__':
    main(*sys.argv[1:])
