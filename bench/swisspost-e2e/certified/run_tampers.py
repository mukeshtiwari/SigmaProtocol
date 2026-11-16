#!/usr/bin/env python3
"""Runs the certified checker (e2e_extract.py + Swissposte2e/main.exe) on the
untampered election and on every tampered copy listed in a manifest written
by the Swiss Post Verifier harness (bench/swisspost-e2e/verifier/), and
compares the verdicts: a scenario is a disagreement when one side accepts and
the other rejects.

usage: run_tampers.py CLEAN_ELECTION_DIR TAMPER_ROOT   (TAMPER_ROOT/manifest.json, TAMPER_ROOT/<name>/)"""
import concurrent.futures, json, os, subprocess, sys

clean, troot = sys.argv[1], sys.argv[2]
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.abspath(os.path.join(here, "..", "..", ".."))
driver = os.path.join(root, "_build/default/src/Executable/Swissposte2e/main.exe")
work = os.path.join(troot, "_certified"); os.makedirs(work, exist_ok=True)

def election_dir(d):   # the directory holding D2/ and D3/
    for dp, dns, _ in os.walk(d):
        if "D2" in dns and "D3" in dns: return dp
    return d

def certified(name, d):
    stm = os.path.join(work, name + ".json")
    x = subprocess.run([sys.executable, "-I", os.path.join(here, "e2e_extract.py"), election_dir(d), stm], capture_output=True, text=True)
    if x.returncode != 0:
        return False, "extraction failed: " + (x.stderr.strip().splitlines() or ["?"])[-1]
    r = subprocess.run([driver, stm], capture_output=True, text=True)
    fails = [l.split("\t")[2] if l.count("\t") >= 2 else l for l in r.stdout.splitlines() if "\tfalse\t" in l]
    open(os.path.join(work, name + ".out"), "w").write(r.stdout)
    return r.returncode == 0, "; ".join(fails[:4]) + (f" (+{len(fails) - 4})" if len(fails) > 4 else "")

manifest = json.load(open(os.path.join(troot, "manifest.json")))
jobs = [("untampered", clean, None)] + [(s["name"], os.path.join(troot, s["name"]), s) for s in manifest]
with concurrent.futures.ThreadPoolExecutor(os.cpu_count()) as ex:
    res = list(ex.map(lambda j: (j, certified(j[0], j[1])), jobs))
bad = 0
for (name, _, s), (ok, why) in res:
    sp = "accept" if s is None else str(s.get("verifier_verdict", "?")).lower()
    sp_acc = s is None or sp in ("true", "accept", "accepted", "ok", "pass", "passed", "success")
    exp = "accept" if s is None else s.get("expected", "reject")
    agree = ok == sp_acc
    bad += not agree or (exp == "reject" and (ok or sp_acc))
    print(f"{'agree   ' if agree else 'DISAGREE'} expected={exp:6} swisspost={'accept' if sp_acc else 'reject':6} certified={'accept' if ok else 'reject':6} {name}"
          + ("" if ok else f"\n{'':10}certified rejects: {why}"))
print(f"{len(res)} cases, {bad} disagreements or acceptances of a tampered election")
sys.exit(1 if bad else 0)
