#!/usr/bin/env python3
"""Extended differential campaign for the Belenios mix-net, beyond the single
torsion-tampered shuffle of campaign.py. Three stages, each on the committed
non-homomorphic fixture, each case seeded and fed to `belenios-tool`:

  chain    a chain of N mix servers (port-built, each output the next's input).
           One server at position t taints output #0 with an order-2 point; the
           others are honest. Probes whether a torsion point injected mid-chain
           survives the honest re-encryptions that follow and whether the whole
           chain's shuffle check is still accepted.

  multi    a single shuffle that taints j of the M outputs (j = 1..M) with an
           order-2 (and, separately, order-8) point. Probes how acceptance falls
           as more outputs leave the subgroup (each imposes its own parity
           condition on the Fiat-Shamir challenge).

  decrypt  a control on the joint-decryption path. The honest fixture's archive
           is tampered by adding an order-2 point to one published decryption
           factor (and, separately, to one ciphertext of the encrypted tally),
           then re-hashed and verified. Belenios subgroup-checks both
           (check_factor's `G.check f`, check_result's `check_ciphertext`), so
           unlike the shuffle check these are expected to reject every case ---
           the contrast that localises the finding to check_shuffle_proof.

usage: campaign_ext.py BELENIOS_TOOL FIXTURE.bel RESULTS_DIR [SEEDS] [JOBS]
"""
import concurrent.futures, os, random, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mix_lib import *

tool, fixture, results = sys.argv[1:4]
seeds = int(sys.argv[4]) if len(sys.argv) > 4 else 50
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

def insub(cts): return all(is_subgroup(a) and is_subgroup(b) for a, b in cts)

# ---------- chain: N mixers, one taints output #0 at position t ----------
def chain_case(seed, n, t):
    rng = random.Random(seed)
    ee = nh_input(arch, el)[0]
    shuffles = []
    for k in range(n):
        ee2, rr2, psi = gen_shuffle(rng, el.y, ee)
        if k == t:
            ee2 = [(a, add(b, T2)) if i == 0 else (a, b) for i, (a, b) in enumerate(ee2)]
        pf = gen_shuffle_proof(rng, el.fingerprint, el.y, ee, ee2, rr2, psi)
        shuffles.append(((k % 2) + 1, compact(shuffle_json([ee2], [pf]))))
        ee = ee2
    a = with_shuffles(arch, shuffles, end=False)
    return (n, t, seed, insub(ee), tool_verify(a))

# ---------- multi: one shuffle taints j of M outputs ----------
def multi_case(seed, j, tname):
    T = {"2": T2, "8": T8}[tname]
    rng = random.Random(seed)
    ee = nh_input(arch, el)[0]
    ee2, rr2, psi = gen_shuffle(rng, el.y, ee)
    ee2 = [(a, add(b, T)) if i < j else (a, b) for i, (a, b) in enumerate(ee2)]
    pf = gen_shuffle_proof(rng, el.fingerprint, el.y, ee, ee2, rr2, psi)
    a = with_shuffles(arch, [(1, compact(shuffle_json([ee2], [pf])))], end=False)
    return (tname, j, seed, tool_verify(a))

# ---------- decrypt control: taint a factor / a tally ciphertext ----------
def find_pd_doc(a):
    """the name and parsed JSON of the first partial-decryption document"""
    for h in a.payloads("PartialDecryption"):
        inner = a.doc(h)["payload"]
        return inner, a.doc(inner)
    return None, None

def decrypt_factor_case():
    a = arch.copy()
    name, doc = find_pd_doc(a)
    pt = ofstr(doc["decryption_factors"][0][0], check=False)
    doc["decryption_factors"][0][0] = tostr(add(pt, T2))
    a.replace_data(name, compact(doc))
    return tool_verify(a)

def decrypt_tally_case():
    a = arch.copy()
    th = a.doc(a.payloads("EncryptedTally")[0])
    tname = th["encrypted_tally"]
    tally = a.doc(tname)
    c = tally[0][0]
    tally[0][0] = {"alpha": c["alpha"], "beta": tostr(add(ofstr(c["beta"], check=False), T2))}
    a.replace_data(tname, compact(tally))
    return tool_verify(a)

# ---- run ----
M = len(nh_input(arch, el)[0])

chain_cases = [(s, n, t) for n in (2, 3) for t in range(n) for s in range(1, seeds + 1)]
with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
    chain_rows = list(ex.map(lambda c: chain_case(*c), chain_cases))
with open(os.path.join(results, "chain.tsv"), "w") as f:
    f.write("mixers\ttaint_pos\tseed\tfinal_output_in_subgroup\tbelenios_tool_accepts\n")
    for n, t, s, fin, tv in sorted(chain_rows):
        f.write(f"{n}\t{t}\t{s}\t{fin}\t{tv}\n")

multi_cases = [(s, j, tn) for tn in ("2", "8") for j in range(1, M + 1) for s in range(1, seeds + 1)]
with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
    multi_rows = list(ex.map(lambda c: multi_case(*c), multi_cases))
with open(os.path.join(results, "multi.tsv"), "w") as f:
    f.write("order\ttainted_outputs\tseed\tbelenios_tool_accepts\n")
    for tn, j, s, tv in sorted(multi_rows):
        f.write(f"{tn}\t{j}\t{s}\t{tv}\n")

df = decrypt_factor_case()
dt = decrypt_tally_case()
with open(os.path.join(results, "decrypt.tsv"), "w") as f:
    f.write("target\tbelenios_tool_accepts\n")
    f.write(f"decryption_factor+T2\t{df}\n")
    f.write(f"encrypted_tally_ciphertext+T2\t{dt}\n")

# ---- summaries ----
print(f"M = {M} ciphertexts; {seeds} seeds per config\n")
print("chain: a torsion point injected by mixer t, among N honest-otherwise mixers")
print("  mixers  taint_pos  final_output_out_of_subgroup  belenios-tool accepts")
for n in (2, 3):
    for t in range(n):
        rs = [r for r in chain_rows if r[0] == n and r[1] == t]
        out = sum(1 for r in rs if not r[3]); acc = sum(1 for r in rs if r[4])
        print(f"    {n}        {t}             {out:3d}/{len(rs)}                 {acc:3d}/{len(rs)}")

print("\nmulti: a single shuffle taints j of the outputs")
print("  order  tainted  belenios-tool accepts")
for tn in ("2", "8"):
    for j in range(1, M + 1):
        rs = [r for r in multi_rows if r[0] == tn and r[1] == j]
        print(f"    {tn}      {j}        {sum(1 for r in rs if r[3]):3d}/{len(rs)}")

print("\ndecrypt control (joint-decryption path is subgroup-checked):")
print(f"  decryption factor + T2          -> belenios-tool accepts: {df}")
print(f"  encrypted-tally ciphertext + T2 -> belenios-tool accepts: {dt}")
print("  (both False: unlike the shuffle check, these paths reject torsion)")
