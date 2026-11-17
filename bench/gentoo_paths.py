#!/usr/bin/env python3
"""What the witness paths of the Schulze certificate reveal, on the Gentoo
council elections.

The certificate (Backend/SchulzeTally.v, tally_proof.tp_paths) publishes, for
every ordered pair (i, j) of candidates, the diagonal included, the honest
trustees' witness path in the clear. This script recomputes those paths
exactly as the extracted prover does:

  d = defeat D                      (defeat)
  p = m steps of closure_step from d (minmax_closure)
  path(i, j) = i :: BFS walk to j through edges of weight >= p_ij,
               or the direct edge [i; j] if the BFS fails  (witness_path)

with candidates in the order of the election's candidate file, as in the
Gentoo driver. A path with one edge is the direct edge, which the honest
prover publishes both when p_ij = 0 and when d_ij >= p_ij > 0, so it does
not tell the public whether i defeats j. A path with two or more edges only
arises when p_ij > 0, and then every edge (u, v) on it has d_uv >= p_ij > 0:
the public learns that u defeats v head to head (the direction, not the
margin). The script reports, per election, the number of unordered candidate
pairs whose head-to-head winner the paths reveal this way, out of all pairs,
and how many of those revealed pairs have a margin |D_ij - D_ji| of at most 2
(the close pairs of gentoo_leak.py).

Usage: python3 bench/gentoo_paths.py [--tex]
"""
import glob, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gentoo_leak import DATA, read_candidates, read_master, positions, margins


def defeat(D, m):
    return [[D[i][j] if D[j][i] < D[i][j] else 0 for j in range(m)] for i in range(m)]


def minmax_closure(d, m):
    p = [row[:] for row in d]
    for _ in range(m):
        p = [[max(p[i][j], max([min(p[i][k], d[k][j]) for k in range(m)] + [0]))
              for j in range(m)] for i in range(m)]
    return p


def bfs_walk(d, s, fuel, j, frontier, visited, m):
    while fuel > 0 and frontier:
        fuel -= 1
        (u, path), frontier = frontier[0], frontier[1:]
        if s <= d[u][j]:
            return list(reversed([j] + path))
        nexts = [k for k in range(m) if s <= d[u][k] and k not in visited]
        frontier = frontier + [(k, [k] + path) for k in nexts]
        visited = nexts + visited
    return None


def witness_path(d, p, i, j, m):
    walk = bfs_walk(d, p[i][j], m * m + 1, j, [(i, [])], [i], m)
    return [i] + walk if walk is not None else [i, j]


def analyse(election):
    cands = read_candidates(election)
    ballots = read_master(election)
    if cands is None:
        cands = sorted({c for b in ballots for g in b for c in g})
    m = len(cands)
    D = margins([positions(b, cands) for b in ballots], m)
    d = defeat(D, m)
    p = minmax_closure(d, m)
    revealed = set()
    long_paths = 0
    for i in range(m):
        for j in range(m):
            path = witness_path(d, p, i, j, m)
            if len(path) > 2:
                long_paths += 1
                for u, v in zip(path, path[1:]):
                    assert d[u][v] >= p[i][j] > 0
                    revealed.add(frozenset((u, v)))
    defeats = sum(1 for i in range(m) for j in range(i + 1, m) if D[i][j] != D[j][i])
    close = sum(1 for e in revealed for (u, v) in [tuple(e)] if abs(D[u][v] - D[v][u]) <= 2)
    return dict(election=election, N=len(ballots), m=m, pairs=m * (m - 1) // 2,
                defeats=defeats, long_paths=long_paths, revealed=len(revealed), close=close)


def main():
    tex = '--tex' in sys.argv
    elections = sorted(os.path.basename(f)[len('master-'):]
                       for f in glob.glob(os.path.join(DATA, 'master-council-*')))
    rows = [analyse(e) for e in elections]
    if tex:
        for r in rows:
            print('    %s & %d of %d & %d \\\\' % (r['election'].replace('_', '\\_'),
                  r['revealed'], r['pairs'], r['close']))
        return
    print('%-22s %4s %3s %6s %8s %11s %9s %14s' % ('election', 'N', 'm', 'pairs', 'defeats',
          'long paths', 'revealed', 'revealed close'))
    for r in rows:
        print('%-22s %4d %3d %6d %8d %11d %9d %14d' % (r['election'], r['N'], r['m'], r['pairs'],
              r['defeats'], r['long_paths'], r['revealed'], r['close']))
    print('%-22s %4s %3s %6d %8d %11d %9d %14d' % ('all', '', '', sum(r['pairs'] for r in rows),
          sum(r['defeats'] for r in rows), sum(r['long_paths'] for r in rows),
          sum(r['revealed'] for r in rows), sum(r['close'] for r in rows)))


if __name__ == '__main__':
    main()
