#!/usr/bin/env python3
"""Wrap an extracted CakeML exp into a full program: scrape constructor
names/arities and declare them all in one datatype (type inference is
skipped, so only name->(tag, arity) matters)."""
import sys, re, threading
sys.setrecursionlimit(10**6)

def tokenize(s):
    out, i, n = [], 0, len(s)
    while i < n:
        c = s[i]
        if c in '()': out.append(c); i += 1
        elif c == '"':
            j = i + 1
            while s[j] != '"': j += 2 if s[j] == '\\' else 1
            out.append(s[i:j+1]); i = j + 1
        elif c.isspace(): i += 1
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in '()': j += 1
            out.append(s[i:j]); i = j
    return out

def parse(ts):
    t = ts.pop(0)
    if t == '(':
        l = []
        while ts[0] != ')': l.append(parse(ts))
        ts.pop(0)
        return l
    return t

ctors = {}
def scan(x):
    if isinstance(x, str): return
    # (Con (SOME (Short "N")) (args...)) / (Con (SOME (Short "N")) nil)
    if len(x) >= 2 and x[0] in ('Con', 'Pcon') and isinstance(x[1], list) \
       and len(x[1]) == 2 and x[1][0] == 'SOME':
        name = x[1][1][1]
        args = x[2] if len(x) > 2 else 'nil'
        arity = 0 if args == 'nil' or isinstance(args, str) else len(args)
        prev = ctors.get(name)
        if prev is None or arity > prev: ctors[name] = arity
    for e in x:
        scan(e)

def main():
    global tree
    exp = open(sys.argv[1]).read().strip()
    tree = parse(tokenize(exp))
    scan(tree)

threading.stack_size(512 * 1024 * 1024)
th = threading.Thread(target=main)
th.start(); th.join()
exp = open(sys.argv[1]).read().strip()
decls = ' '.join(
    '(%s%s)' % (n, ''.join(' (Atapp nil (Short "meta"))' for _ in range(a)))
    for n, a in sorted(ctors.items()))
dtype = f'(Dtype (unk unk) ((nil "meta" {decls})))'
prog = f'({dtype} (Dlet (unk unk) "result" {exp}))'
open(sys.argv[2], 'w').write(prog)
print(f'{len(ctors)} constructors:', ' '.join(sorted(ctors)))
