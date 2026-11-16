#!/usr/bin/env python3
"""Summarise the logs of the Gentoo council runs (bench/README.md, "Gentoo")
as LaTeX table rows: year, m, N, median encryption time (from the encrypt.exe
log), median verification time, accepted ballots, certificate generation and
verification time, transcript entries, and the certified winner. Logs of
encrypt.exe and main.exe for the same election (council-YYYYMM in the file
name) are merged. Usage: gentoo_table.py LOG... """
import re, sys, statistics
from collections import defaultdict
data = defaultdict(str)
for f in sys.argv[1:]:
    m = re.search(r'council-(\d{6})', f)
    if m:
        data[m.group(1)] += open(f).read() + '\n'
for name in sorted(data):
    s = data[name]
    y = name[:4]
    enc = [float(x) for x in re.findall(r'encrypted and proved in ([\d.]+) s', s)]
    mN = re.search(r'm = (\d+) candidates, N = (\d+) ballots', s)
    ver = re.search(r'ballots: verify median ([\d.]+) s, total (\d+) s, accepted (\d+) of (\d+)', s)
    cert = re.search(r'certificate: generation (\d+) s, verification (\d+) s, verified (\w+), transcript entries (\d+)', s)
    win = re.search(r'Schulze winner: (\S+)', s)
    m_, N = (mN.group(1), mN.group(2)) if mN else ('?', str(len(enc)))
    secs = lambda t: f"{t:.1f}\\,s" if t < 10 else f"{t:.0f}\\,s"
    e = secs(statistics.median(enc)) if enc else '?'
    v = secs(float(ver.group(1))) if ver else '?'
    acc = f"{ver.group(3)}/{ver.group(4)}" if ver else '?'
    if cert:
        cg, cv, ok, sz = int(cert.group(1)), int(cert.group(2)), cert.group(3), int(cert.group(4))
        c = f"{cg//60}\\,min & {cv//60}\\,min & {sz/1000:,.0f}k"
        if ok != 'true': c += ' (REJECTED)'
    else:
        c = "\\TODO{} & \\TODO{} & \\TODO{}"
    w = win.group(1) if win else '?'
    board = re.search(r'board \S+ \((\d+) bytes\)', s)
    b = f" & {int(board.group(1))/1e6:.0f}\\,MB" if board else ''
    print(f"    {y} & {m_} & {N} & {e} & {v} & {acc} & {c} & \\texttt{{{w}}}{b} \\\\")
