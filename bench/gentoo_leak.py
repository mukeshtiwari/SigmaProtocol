#!/usr/bin/env python3
"""The leak in the Gentoo election archive, and the Schulze winner of each
election.

Gentoo elects its Council and Foundation Trustees with a Condorcet count
(countify in https://anongit.gentoo.org/git/proj/elections.git: Schwartz
sequential dropping, i.e. Debian Constitution A.5 steps 5-8 with no quorum,
majority or default option) and publishes every ballot: the master ballot
of each election lists, under an anonymous confirmation id, the voter's
ranked lines (names on one line are tied; candidates not listed rank last,
tied). bench/gentoo-votes/ holds the master and candidate files of every
completed election that has a published master ballot (repository commit
4ca0b003, 2026-07-19).

For each election this script reports the number of ballots N, the number
of candidates m (including _reopen_nominations where it is on the ballot),
the fraction of ballots whose ranking (as a position vector, i.e. the
information our ballot encrypts) is cast by no other voter, the number of
unordered candidate pairs whose margin |D_ij - D_ji| is at most 2, the
Schulze (beatpath) winner set, and Gentoo's own first-pass winner set
(Schwartz sequential dropping), with a flag when the two differ.

Usage: python3 bench/gentoo_leak.py [--tex]
"""
import glob, os, re, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, 'gentoo-votes')

def read_candidates(election):
    path = os.path.join(DATA, 'ballot-' + election)
    if not os.path.exists(path):
        return None
    return [l.strip() for l in open(path) if l.strip()]

def read_master(election):
    text = open(os.path.join(DATA, 'master-' + election)).read()
    ballots = []
    for entry in re.split(r'^--------- confirmation ', text, flags=re.M):
        if not entry.strip():
            continue
        m = re.match(r'([0-9a-fA-F]{4,12}) ---------\n(.*)$', entry, re.S)
        if not m:
            raise ValueError('cannot parse entry in ' + election)
        lines = [l.split() for l in m.group(2).splitlines() if l.strip()]
        ballots.append(lines)
    return ballots

def positions(ballot, cands):
    """position vector: rank of each candidate, unlisted = m (last, tied)"""
    m = len(cands)
    pos = {c: m for c in cands}
    for i, group in enumerate(ballot):
        for c in group:
            if c in pos:
                pos[c] = i
    return tuple(pos[c] for c in cands)

def margins(vectors, m):
    D = [[0] * m for _ in range(m)]
    for s in vectors:
        for i in range(m):
            for j in range(m):
                if s[i] < s[j]:
                    D[i][j] += 1
    return D

def schulze_winners(D, m):
    d = [[D[i][j] if D[i][j] > D[j][i] else 0 for j in range(m)] for i in range(m)]
    p = [row[:] for row in d]
    for k in range(m):
        for i in range(m):
            for j in range(m):
                if i != j and i != k and j != k:
                    p[i][j] = max(p[i][j], min(p[i][k], p[k][j]))
    return [w for w in range(m) if all(p[w][j] >= p[j][w] for j in range(m) if j != w)]

def cssd_winners(D, m):
    """Gentoo's countify: one pass of Schwartz sequential dropping"""
    defeats = {(i, j) for i in range(m) for j in range(m) if D[i][j] > D[j][i]}
    cands = list(range(m))
    while True:
        td = set(defeats)
        for i in cands:
            for j in cands:
                for k in cands:
                    if (j, i) in td and (i, k) in td:
                        td.add((j, k))
        active = [a for a in cands if all((a, b) in td or (b, a) not in td for b in cands)]
        cands = active
        plist = [(a, b) for a in cands for b in cands if (a, b) in defeats]
        if not plist:
            return cands
        def weaker(x, y):  # x weaker than y
            (a, p), (b, q) = x, y
            return D[a][p] < D[b][q] or (D[a][p] == D[b][q] and D[p][a] > D[q][b])
        weakest = [x for x in plist if not any(weaker(y, x) for y in plist if y != x)]
        for x in weakest:
            defeats.discard(x)

def analyse(election):
    cands = read_candidates(election)
    ballots = read_master(election)
    if cands is None:
        cands = sorted({c for b in ballots for g in b for c in g})
    m = len(cands)
    vectors = [positions(b, cands) for b in ballots]
    N = len(vectors)
    counts = Counter(vectors)
    unique = sum(1 for v in vectors if counts[v] == 1)
    D = margins(vectors, m)
    close = sum(1 for i in range(m) for j in range(i + 1, m) if abs(D[i][j] - D[j][i]) <= 2)
    sw = [cands[w] for w in schulze_winners(D, m)]
    cw = [cands[w] for w in cssd_winners(D, m)]
    return dict(election=election, N=N, m=m, unique=unique, pairs=m * (m - 1) // 2,
                close=close, schulze=sw, cssd=cw, D=D, cands=cands)

def write_positions(election, out):
    """m, the candidate names, then one line per ballot with the position of
    each candidate (0 = top; unlisted = m): the input of the Gentoo driver"""
    cands = read_candidates(election)
    ballots = read_master(election)
    if cands is None:
        cands = sorted({c for b in ballots for g in b for c in g})
    with open(out, 'w') as f:
        f.write('%d %s\n' % (len(cands), ' '.join(cands)))
        for b in ballots:
            f.write(' '.join(str(p) for p in positions(b, cands)) + '\n')

def main():
    if '--positions' in sys.argv:
        i = sys.argv.index('--positions'); write_positions(sys.argv[i + 1], sys.argv[i + 2]); return
    tex = '--tex' in sys.argv
    elections = sorted(os.path.basename(f)[len('master-'):] for f in glob.glob(os.path.join(DATA, 'master-*')))
    rows = [analyse(e) for e in elections]
    if tex:
        for r in rows:
            print('    %s & %d & %d & %d (%.0f\\%%) & %d of %d & %s%s \\\\' % (
                r['election'].replace('_', '\\_'), r['N'], r['m'], r['unique'],
                100.0 * r['unique'] / r['N'], r['close'], r['pairs'],
                ', '.join(r['schulze']).replace('_', '\\_'),
                '' if r['schulze'] == r['cssd'] else ' (Gentoo: %s)' % ', '.join(r['cssd'])))
    else:
        print('%-30s %5s %3s %12s %10s  %s' % ('election', 'N', 'm', 'unique', 'close', 'Schulze winner(s) [Gentoo first pass if different]'))
        for r in rows:
            print('%-30s %5d %3d %5d (%3.0f%%) %4d of %3d  %s%s' % (
                r['election'], r['N'], r['m'], r['unique'], 100.0 * r['unique'] / r['N'],
                r['close'], r['pairs'], ','.join(r['schulze']),
                '' if r['schulze'] == r['cssd'] else '  [Gentoo: %s]' % ','.join(r['cssd'])))
        totN = sum(r['N'] for r in rows); totU = sum(r['unique'] for r in rows)
        totC = sum(r['close'] for r in rows); totP = sum(r['pairs'] for r in rows)
        print('%-30s %5d     %5d (%3.0f%%) %4d of %3d  elections %d, agreement %d' % (
            'all', totN, totU, 100.0 * totU / totN, totC, totP, len(rows),
            sum(1 for r in rows if r['schulze'] == r['cssd'])))

if __name__ == '__main__':
    main()
