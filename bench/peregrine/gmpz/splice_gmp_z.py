#!/usr/bin/env python3
"""Prepare a Peregrine λ□ program for Z, positive and N as GMP integers (C backend).

usage: splice_gmp_z.py PROGRAM.ast GMP_Z.ast OUT.ast ATTRS.sexp

GMP_Z.ast is the extraction of GmpZ.v.  The bodies of the Z, Pos and N
operations listed in OPS, in Corelib's BinNums and in Stdlib's ZArith, PArith
and NArith, are replaced by the axioms or [*_impl] definitions of GmpZ, and
ATTRS.sexp maps the axioms to the functions of z_gmp.c and remaps the inductives
Z, positive and N.  Constants of those modules that the program uses and that
are not replaced are printed; they run on the remapped constructors and case
analyses, which is correct but slower.
"""
import re, sys
from splice_locked import parse, dump, kn_str, env_of, refs, topo_sort

HEADER = '"z_gmp.h"'
FILES = {
    'Z': ('IntDef', 'BinIntDef', 'BinInt'),
    'Pos': ('PosDef', 'BinPosDef', 'BinPos'),
    'N': ('NatDef', 'BinNatDef', 'BinNat'),
}
OPS = {
    'Z': {
        'add': 'zg_add', 'sub': 'zg_sub', 'mul': 'zg_mul', 'opp': 'zg_opp', 'abs': 'zg_abs',
        'div': 'zg_fdiv', 'modulo': 'zg_fmod', 'quot': 'zg_tdiv', 'rem': 'zg_tmod',
        'pow': 'zg_pow', 'pow_pos': 'zg_pow', 'shiftl': 'zg_shiftl', 'shiftr': 'zg_shiftr',
        'land': 'zg_land', 'lor': 'zg_lor', 'lxor': 'zg_lxor', 'testbit': 'zg_testbit',
        'compare': 'zg_compare', 'eqb': 'zg_eqb', 'leb': 'zg_leb', 'ltb': 'zg_ltb',
        'pos_sub': 'zg_sub', 'to_pos': 'zg_to_pos', 'to_N': 'zg_to_n', 'abs_N': 'zg_abs',
        'of_N': 'id_impl', 'succ': 'succ_impl', 'pred': 'pred_impl', 'double': 'double_impl',
        'succ_double': 'succ_double_impl', 'pred_double': 'pred_double_impl',
        'div2': 'div2_impl', 'geb': 'geb_impl', 'gtb': 'gtb_impl', 'min': 'min_impl',
        'max': 'max_impl', 'even': 'even_impl', 'odd': 'odd_impl', 'sgn': 'sgn_impl',
        'div_eucl': 'div_eucl_impl',
    },
    'Pos': {
        'add': 'zg_add', 'mul': 'zg_mul', 'sub': 'zg_pos_sub_trunc', 'pred': 'zg_pos_pred',
        'pow': 'zg_pow', 'size': 'zg_pos_size', 'compare': 'zg_compare', 'eqb': 'zg_eqb',
        'leb': 'zg_leb', 'ltb': 'zg_ltb', 'succ': 'succ_impl', 'pred_double': 'pred_double_impl',
        'min': 'min_impl', 'max': 'max_impl', 'compare_cont': 'compare_cont_impl',
    },
    'N': {
        'add': 'zg_add', 'mul': 'zg_mul', 'sub': 'zg_n_sub_trunc', 'pred': 'zg_n_pred',
        'div': 'zg_fdiv', 'modulo': 'zg_fmod', 'pow': 'zg_pow', 'shiftr': 'zg_shiftr',
        'shiftl': 'zg_shiftl', 'testbit': 'zg_testbit', 'compare': 'zg_compare',
        'eqb': 'zg_eqb', 'leb': 'zg_leb', 'ltb': 'zg_ltb', 'succ': 'succ_impl',
        'double': 'double_impl', 'succ_double': 'succ_double_impl', 'div2': 'div2_impl',
        'min': 'min_impl', 'max': 'max_impl', 'div_eucl': 'div_eucl_impl',
    },
}
# axiom of GmpZ.v -> (C function, arity, takes the thread_info).  The functions
# that allocate their result in the heap take the thread_info, so that the
# generated code publishes its alloc pointer and roots its live values around
# the call (z_gmp.c); the others never allocate.
ALLOCATING = {
    'zg_add', 'zg_sub', 'zg_mul', 'zg_fdiv', 'zg_fmod', 'zg_tdiv', 'zg_tmod', 'zg_pow',
    'zg_shiftl', 'zg_shiftr', 'zg_land', 'zg_lor', 'zg_lxor', 'zg_pos_sub_trunc',
    'zg_n_sub_trunc', 'zg_opp', 'zg_abs', 'zg_pos_pred', 'zg_n_pred', 'zg_Zneg', 'zg_xO',
    'zg_xI'}
PRIMS = {a: (a, 2, a in ALLOCATING) for a in (
    'zg_add', 'zg_sub', 'zg_mul', 'zg_fdiv', 'zg_fmod', 'zg_tdiv', 'zg_tmod', 'zg_pow',
    'zg_shiftl', 'zg_shiftr', 'zg_land', 'zg_lor', 'zg_lxor', 'zg_pos_sub_trunc',
    'zg_n_sub_trunc', 'zg_testbit', 'zg_eqb', 'zg_leb', 'zg_ltb', 'zg_compare')}
PRIMS.update({a: (a, 1, a in ALLOCATING) for a in (
    'zg_opp', 'zg_abs', 'zg_pos_pred', 'zg_n_pred', 'zg_pos_size', 'zg_to_pos', 'zg_to_n',
    'zg_Zpos', 'zg_Zneg', 'zg_xO', 'zg_xI', 'zg_Npos')})
PRIMS.update({a: (a, 0, False) for a in ('zg_Z0', 'zg_xH', 'zg_N0')})
PRIMS.update({'zg_z_case': ('zg_z_case', 4, True), 'zg_pos_case': ('zg_pos_case', 4, True),
              'zg_n_case': ('zg_n_case', 3, True)})
HELPERS = set(PRIMS) | {'two'}
BINNUMS = '((MPfile ("BinNums" "Numbers" "Corelib")) "%s")'
# inductive -> (constructors in order, case analysis)
INDS = {
    'Z': (('zg_Z0', 'zg_Zpos', 'zg_Zneg'), 'zg_z_case'),
    'positive': (('zg_xI', 'zg_xO', 'zg_xH'), 'zg_pos_case'),
    'N': (('zg_N0', 'zg_Npos'), 'zg_n_case'),
}
SKIP = set(filter(None, __import__('os').environ.get('ZG_SKIP', '').split(',')))
KN = re.compile(r'^\(\(MPdot \(MPfile \("(\w+)"[^)]*\)\) "(\w+)"\) "(\w+)"\)$')


def op_of(k):
    """The GmpZ name that replaces the constant k, or None."""
    m = KN.match(k)
    if not m:
        return None
    f, mod, name = m.groups()
    if mod in FILES and f in FILES[mod] and mod + '.' + name not in SKIP:
        return OPS[mod].get(name)
    return None


def numeric(k):
    m = KN.match(k)
    return bool(m) and m.group(2) in FILES and m.group(1) in FILES[m.group(2)]


def eta(kn, arity):
    """fun x1 .. xn => kn x1 .. xn: Peregrine's C backend rejects a constant
    whose body is a remapped constant left unapplied."""
    t = ['tConst', kn]
    for i in range(arity):
        t = ['tApp', t, ['tRel', str(arity - 1 - i)]]
    for i in range(arity):
        t = ['tLambda', ['nNamed', '"x%d"' % (arity - i)], t]
    return t


LIT_DEPTH = 8


def is_num_ctor(t):
    return (isinstance(t, list) and len(t) == 4 and t[0] == 'tConstruct' and isinstance(t[1], list)
            and t[1][1][0] == ['MPfile', ['"BinNums"', '"Numbers"', '"Corelib"']])


def literal_depth(t):
    """The number of constructor applications if t is a closed numeral, else None."""
    n = 0
    while isinstance(t, list) and len(t) == 3 and t[0] == 'tApp' and is_num_ctor(t[1]):
        t = t[2]
        n += 1
    return n if is_num_ctor(t) else None


def lift_literals(t, lits):
    """Replace each numeral of at least LIT_DEPTH constructors in t by a constant.
    Peregrine's C backend fails with 'Unknown DeBruijn index' on a numeral of
    more than about 80 remapped constructors nested inside an application; a
    numeral that is the whole body of a constant compiles.  lits maps the text
    of a numeral to its declaration."""
    if not isinstance(t, list):
        return t
    d = literal_depth(t)
    if d is not None and d >= LIT_DEPTH:
        out = []
        dump(t, out)
        key = ''.join(out)
        if key not in lits:
            kn = parse('((MPfile ("GmpZ")) "lit_%d")' % len(lits))
            lits[key] = [kn, ['ConstantDecl', ['constant_body', ['Some', t]]]]
        return ['tConst', lits[key][0]]
    return [lift_literals(x, lits) for x in t]


def closure(roots, by_kn):
    seen, todo = set(), list(roots)
    while todo:
        k = todo.pop()
        if k in seen or k not in by_kn:
            continue
        seen.add(k)
        todo.extend(refs(by_kn[k][1], set()) - {k})
    return seen


def main(prog_f, gmp_f, out_f, attrs_f):
    prog = parse(open(prog_f).read())
    penv, genv = env_of(prog), env_of(parse(open(gmp_f).read()))
    impl = {d[0][-1].strip('"'): d for d in genv if 'GmpZ' in kn_str(d[0])}
    present = {kn_str(d[0]) for d in penv}
    replaced, kept = [], []
    new_env = []
    for d in penv:
        k = kn_str(d[0])
        name = op_of(k)
        if name:
            if name in PRIMS:
                body = ['Some', eta(impl[name][0], PRIMS[name][1])]
            else:
                body = impl[name][1][1][1]
            d = [d[0], ['ConstantDecl', ['constant_body', body]]]
            replaced.append(k)
        elif numeric(k):
            kept.append(k)
        new_env.append(d)
    lits = {}
    for i, d in enumerate(new_env):
        if d[1][0] == 'ConstantDecl' and d[1][1][1] != 'None':
            body = d[1][1][1]
            if literal_depth(body[1]) is None:  # a numeral that is the whole body stays
                new_env[i] = [d[0], ['ConstantDecl', ['constant_body', ['Some', lift_literals(body[1], lits)]]]]
    new_env.extend(lits.values())
    for d in genv:
        k = kn_str(d[0])
        if 'GmpZ' in k and d[0][-1].strip('"') not in HELPERS and k not in present:
            # an impl is copied only as the body of the operation it replaces
            continue
        if k not in present:
            new_env.append(d)
            present.add(k)
    env = topo_sort(new_env)
    by_kn = {kn_str(d[0]): d for d in env}
    prim_kn = {name: kn_str(impl[name][0]) for name in PRIMS}
    # The inductive remapping adds references to these in every other declaration.
    roots = [prim_kn[c] for ctors, case in INDS.values() for c in ctors + (case,)]
    oldest = closure(roots, by_kn)
    env = [d for d in env if kn_str(d[0]) not in oldest] + \
          [d for d in env if kn_str(d[0]) in oldest]
    prog[1] = env
    out = []
    dump(prog, out)
    open(out_f, 'w').write(''.join(out))
    remaps = ' '.join(
        '(%s (remapped_constant (Some %s) %d %s false "%s"))'
        % (prim_kn[name], HEADER, arity, 'true' if gc else 'false', c)
        for name, (c, arity, gc) in PRIMS.items())
    inds = ' '.join(
        '(KnIndRemap %s ((extract_inductive (%s) %s)))'
        % (BINNUMS % ind, ' '.join(prim_kn[c] for c in ctors), prim_kn[case])
        for ind, (ctors, case) in INDS.items())
    open(attrs_f, 'w').write('(attributes_config () (%s) (%s) () ())\n' % (remaps, inds))
    print('replaced %d operations; kept %d: %s' % (
        len(replaced), len(kept), ' '.join(KN.match(k).group(2) + '.' + KN.match(k).group(3) for k in kept)))
    print('declarations', len(env), '; numerals lifted', len(lits))


if __name__ == '__main__':
    main(*sys.argv[1:])
