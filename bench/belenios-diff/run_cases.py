#!/usr/bin/env python3
"""Runs belenios-tool (`election verify`) and the certified verifier
(src/Executable/Beleniosverifier) on every case of WORK/cases/manifest.tsv
and compares the verdicts. A verifier accepts iff it exits with status 0.

Writes RESULTS/STAGE.tsv (one line per case: name, expected, belenios-tool,
certified, comparison, the case's description and each verifier's last
message) and RESULTS/summary.tsv (per stage: cases, verdict pairs,
disagreements, cases where both verdicts differ from the expected one).

usage: run_cases.py BELENIOS_TOOL CERTIFIED_VERIFIER WORK RESULTS [JOBS]"""
import collections, concurrent.futures, os, re, shutil, subprocess, sys, tempfile

tool, ours, work, results = sys.argv[1:5]
jobs = int(sys.argv[5]) if len(sys.argv) > 5 else 4
cases = [l.rstrip("\n").split("\t") for l in open(os.path.join(work, "cases", "manifest.tsv"))]
os.makedirs(results, exist_ok=True)

def last_line(s):
    ls = [l for l in s.strip().splitlines() if l.strip()]
    # without paths and timings, so that two runs give identical tables
    return re.sub(r" ?\(\d+\.\d+ s\)", "", re.sub(r"/\S*/", "", ls[-1]))[:160] if ls else ""

def run(case):
    stage, name, expect, note = case
    path = os.path.join(work, "cases", stage, name + ".bel")
    with tempfile.TemporaryDirectory() as d:
        shutil.copy(path, os.path.join(d, "election.bel"))
        try:
            b = subprocess.run([tool, "election", "verify", "--dir", d], capture_output=True, text=True, timeout=600,
                               env={**os.environ, "BELENIOS_USE_URANDOM": "1"})
            bv, bm = ("accept" if b.returncode == 0 else "reject"), last_line(b.stderr + b.stdout)
        except subprocess.TimeoutExpired:
            bv, bm = "reject", "timeout"
    try:
        o = subprocess.run([ours, path], capture_output=True, text=True, timeout=1200)
        ov = "accept" if o.returncode == 0 else "reject"
        om = last_line(o.stdout) if o.returncode in (0, 1) else last_line(o.stderr) or f"exit {o.returncode}"
        if o.returncode not in (0, 1): om = f"exit {o.returncode}: " + om
    except subprocess.TimeoutExpired:
        ov, om = "reject", "timeout"
    return stage, name, expect, bv, ov, note, bm, om

with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
    rows = list(ex.map(run, cases))

by_stage = collections.defaultdict(list)
for r in rows: by_stage[r[0]].append(r)
summary = []
for stage, rs in by_stage.items():
    with open(os.path.join(results, stage + ".tsv"), "w") as f:
        f.write("name\texpected\tbelenios-tool\tcertified\tcomparison\tdescription\tbelenios-tool message\tcertified message\n")
        for _, name, expect, bv, ov, note, bm, om in sorted(rs, key=lambda r: r[1]):
            cmp_ = "agree" if bv == ov else "DISAGREE"
            f.write("\t".join([name, expect, bv, ov, cmp_, note, bm, om]) + "\n")
    pairs = collections.Counter((bv, ov) for _, _, _, bv, ov, *_ in rs)
    dis = sum(1 for r in rs if r[3] != r[4])
    unexpected = sum(1 for r in rs if r[2] != "either" and (r[3] != r[2] or r[4] != r[2]) and r[3] == r[4])
    summary.append((stage, len(rs), pairs, dis, unexpected))
order = ["honest", "field", "struct", "forge"]
with open(os.path.join(results, "summary.tsv"), "w") as f:
    f.write("stage\tcases\tboth accept\tboth reject\tbelenios-tool accepts only\tcertified accepts only\tdisagreements\tagreeing but unexpected\n")
    for stage, n, pairs, dis, unexp in sorted(summary, key=lambda s: order.index(s[0]) if s[0] in order else 9):
        f.write(f"{stage}\t{n}\t{pairs[('accept','accept')]}\t{pairs[('reject','reject')]}\t{pairs[('accept','reject')]}\t{pairs[('reject','accept')]}\t{dis}\t{unexp}\n")
print(open(os.path.join(results, "summary.tsv")).read())
