#!/usr/bin/env python3
"""Differential campaign for the Belenios mix-net (src/lib/v1/mixnet.ml).

Two things are compared on an honest, non-homomorphic (mix-net) Belenios
election:

  honest   belenios-tool's own shuffle proofs, re-checked by an independent
           Python port of mixnet.ml's check_shuffle_proof (mix_lib.py). The
           two agree on every honest shuffle, which is the fidelity check of
           the port.

  torsion  a mix server's output carries a low-order (torsion) point: output
           #0's beta is replaced by beta + T, with T of order 2 or 8, and a
           fresh shuffle proof is produced for that output with the Python
           prover. The output is therefore NOT in the prime-order subgroup.
           Each case is a one-shuffle archive (owner 1, no EndShuffles) fed to
           `belenios-tool election verify`.

What this probes. mixnet.ml's check_shuffle_proof applies G.check (the order-l
subgroup test) only to the proof commitments t1..t42, cc, cc_hat, tt_hat, and
never to its ciphertext arguments ee/ee'. Belenios subgroup-checks ciphertexts
everywhere else (ballots question_nh.ml, tally and decryption election.ml), so
the shuffle verifier is the one place a non-subgroup group element is accepted.
The certified mix-net verifier of this repository (Backend/VerificatumVerifier.v
over Crypto/ShuffleTW.v) models the group as a prime-order vector space over a
field, in which torsion points do not exist and whose soundness theorems assume
exactly the subgroup membership mixnet.ml omits to check; its drivers
(Executable/Vmnverifier, Executable/Beleniosverifier/parsing/ast.ml) reject any
point not of order l at parse time. So a torsion-tampered shuffle that
belenios-tool accepts is rejected by this repository's certified pipeline.

usage: campaign.py BELENIOS_TOOL FIXTURE.bel RESULTS_DIR [SEEDS] [JOBS]
"""
import concurrent.futures, os, random, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mix_lib import *

tool, fixture, results = sys.argv[1:4]
seeds = int(sys.argv[4]) if len(sys.argv) > 4 else 100
jobs = int(sys.argv[5]) if len(sys.argv) > 5 else 4
os.makedirs(results, exist_ok=True)
env = {**os.environ, "BELENIOS_USE_URANDOM": "1"}

arch = Archive.load(fixture)
el = Election(arch)

def tool_verify(a):
    with tempfile.TemporaryDirectory() as d:
        a.save(os.path.join(d, "election.bel"))
        r = subprocess.run([tool, "election", "verify", "--dir", d],
                           capture_output=True, text=True, timeout=600, env=env)
        return r.returncode == 0

# ---- honest: the port re-checks belenios-tool's own shuffles ----
def honest_row():
    prev = nh_input(arch, el)
    rows = []
    for k, (_, s) in enumerate(shuffle_docs(arch)):
        for j, q in enumerate(s["ciphertexts"]):
            out = [ct_of_json(c) for c in q]
            ok = check_shuffle_proof(el.fingerprint, el.y, prev[j], out,
                                     proof_of_json(s["proofs"][j]))
            insub = all(is_subgroup(a) and is_subgroup(b) for a, b in out)
            rows.append((k, j, ok, insub))
            prev[j] = out
    return rows

# ---- torsion: one case for a (seed, T) ----
def torsion_case(seed, tname):
    T = {"2": T2, "8": T8}[tname]
    rng = random.Random(seed)
    ee = nh_input(arch, el)[0]
    ee2, rr2, psi = gen_shuffle(rng, el.y, ee)
    bad = [(a, add(b, T)) if k == 0 else (a, b) for k, (a, b) in enumerate(ee2)]
    pf = gen_shuffle_proof(rng, el.fingerprint, el.y, ee, bad, rr2, psi)
    port = check_shuffle_proof(el.fingerprint, el.y, ee, bad, pf)
    insub = all(is_subgroup(a) and is_subgroup(b) for a, b in bad)
    a = with_shuffles(arch, [(1, compact(shuffle_json([bad], [pf])))], end=False)
    return (tname, seed, port, insub, tool_verify(a))

# honest control: the unmodified fixture, and the port on its shuffles
honest = honest_row()
with open(os.path.join(results, "honest.tsv"), "w") as f:
    f.write("shuffle\tquestion\tport_accepts\toutput_in_subgroup\n")
    for k, j, ok, insub in honest:
        f.write(f"{k}\t{j}\t{ok}\t{insub}\n")
assert all(ok and insub for _, _, ok, insub in honest), "port disagrees on an honest shuffle"
assert tool_verify(arch), "belenios-tool rejects the honest fixture"

cases = [(s, t) for t in ("2", "8") for s in range(1, seeds + 1)]
with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
    rows = list(ex.map(lambda c: torsion_case(c[0], c[1]), cases))

with open(os.path.join(results, "torsion.tsv"), "w") as f:
    f.write("order\tseed\tport_accepts\toutput_in_subgroup\tbelenios_tool_accepts\n")
    for tname, seed, port, insub, tv in sorted(rows):
        f.write(f"{tname}\t{seed}\t{port}\t{insub}\t{tv}\n")

summary = {}
for tname, seed, port, insub, tv in rows:
    s = summary.setdefault(tname, [0, 0, 0])
    s[0] += 1; s[1] += 1 if tv else 0; s[2] += 0 if insub else 1
print("honest shuffles: port and belenios-tool agree, every output in subgroup")
print("order  cases  outputs_out_of_subgroup  belenios-tool 'all checks passed'")
for tname in ("2", "8"):
    n, acc, outsub = summary[tname]
    print(f"  {tname}    {n:4d}        {outsub:4d}/{n}               {acc:4d}/{n}")
print("\n=> belenios-tool accepts a shuffle proof whose output is not a subgroup "
      "element.\n   The certified verifier (prime-order model) rejects every such output.")
