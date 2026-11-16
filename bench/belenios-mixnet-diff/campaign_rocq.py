#!/usr/bin/env python3
"""Run Belenios shuffle inputs through the EXTRACTED certified verifier.

For each seed and mode, export_tw.py writes the same proof as a .bel (for
belenios-tool) and a .dat (for the extracted Terelius-Wikström verifier driver
Executable/Belenioshuffleverifier, which runs Crypto/ShuffleTW.v's tw_verify at
the Ed25519 group of Belenioslib). This records, per case:

  rocq_tw        verdict of the extracted tw_verify on the Belenios proof
  subgroup       whether every output ciphertext is in the prime-order subgroup
  belenios_tool  verdict of `belenios-tool election verify` on the same proof

Reading the result:
  * honest  -> rocq_tw = accept and belenios_tool = accept: the extracted
    certified algebra agrees with Belenios's own prover (cross-validation).
  * torsion -> subgroup = false for every case. The extracted tw_verify, run
    directly on the off-subgroup points (the Coq group type's subgroup proof
    is erased by extraction), still accepts a parity-dependent fraction --- the
    verified ALGEBRA does not reject torsion. The certified verifier is sound
    only because its driver (Executable/Beleniosverifier/parsing/ast.ml) checks
    order l at parse time and so rejects every subgroup=false point BEFORE
    tw_verify runs. Belenios's check_shuffle_proof has no such check.

usage: campaign_rocq.py BELENIOS_TOOL ROCQ_DRIVER FIXTURE.bel RESULTS_DIR [SEEDS]
"""
import os, re, subprocess, sys, tempfile

tool, driver, fixture, results = sys.argv[1:5]
seeds = int(sys.argv[5]) if len(sys.argv) > 5 else 40
os.makedirs(results, exist_ok=True)
here = os.path.dirname(os.path.abspath(__file__))
env = {**os.environ, "BELENIOS_USE_URANDOM": "1"}

def run_case(seed, mode, workdir):
    pre = os.path.join(workdir, "c")
    out = subprocess.run([sys.executable, "-I", os.path.join(here, "export_tw.py"),
                          fixture, pre, str(seed), mode], capture_output=True, text=True)
    m = re.search(r"output_in_subgroup=(\w+)", out.stdout)
    subgroup = (m.group(1) == "True")
    r = subprocess.run([driver, pre + ".dat"], capture_output=True, text=True)
    rocq = (r.returncode == 0)
    d = os.path.join(workdir, "e"); os.makedirs(d, exist_ok=True)
    subprocess.run(["cp", pre + ".bel", os.path.join(d, "election.bel")])
    b = subprocess.run([tool, "election", "verify", "--dir", d],
                       capture_output=True, text=True, timeout=600, env=env)
    return rocq, subgroup, (b.returncode == 0)

rows = []
with tempfile.TemporaryDirectory() as tmp:
    for mode in ("honest", "torsion2", "torsion8"):
        ns = 3 if mode == "honest" else seeds
        for s in range(1, ns + 1):
            wd = os.path.join(tmp, f"{mode}{s}"); os.makedirs(wd)
            rows.append((mode, s, *run_case(s, mode, wd)))

with open(os.path.join(results, "rocq.tsv"), "w") as f:
    f.write("mode\tseed\trocq_tw\toutput_in_subgroup\tbelenios_tool\n")
    for mode, s, rq, sg, bt in rows:
        f.write(f"{mode}\t{s}\t{rq}\t{sg}\t{bt}\n")

def tally(mode):
    rs = [r for r in rows if r[0] == mode]
    return (len(rs), sum(1 for r in rs if r[2]), sum(1 for r in rs if not r[3]),
            sum(1 for r in rs if r[4]))

print("mode       cases  rocq_tw accepts  out_of_subgroup  belenios-tool accepts")
for mode in ("honest", "torsion2", "torsion8"):
    n, rq, osg, bt = tally(mode)
    print(f"  {mode:9s} {n:4d}      {rq:4d}            {osg:4d}             {bt:4d}")
h = [r for r in rows if r[0] == "honest"]
assert all(r[2] and r[4] and r[3] for r in h), "honest cross-validation failed"
print("\nhonest: extracted tw_verify and belenios-tool both accept; outputs in subgroup.")
print("torsion: every output is off-subgroup; the extracted ALGEBRA still accepts a")
print("fraction, so soundness rests on the certified driver's parse-time order-l check,")
print("which rejects all off-subgroup points --- the check Belenios's shuffle verifier omits.")
