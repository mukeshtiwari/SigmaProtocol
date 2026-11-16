#!/usr/bin/env python3
"""Generates the base elections of the campaign at the Helios (IACR) group:
ballots from the Helios booth JS (fixtures/booth.json, see gen_booth.js) and
from the certified prover (prove.exe, randomness drawn from SEED), the
trustees' keys, proofs of knowledge, decryption factors and proofs from
Helios's own Python code (algs.py, with its random source replaced by one
seeded from SEED), and the published tally. Everything except the booth's
ballots is a function of SEED; the booth's ballots are fixtures, checked to
be for the same keys and votes.

Also lists the IACR 2023 and 2024 elections (honest, as published).

usage: gen.py SEED WORK_DIR [--regen-booth]"""
import json, os, random, re, subprocess, sys
import helios_stub

seed, work = sys.argv[1], sys.argv[2]
regen = "--regen-booth" in sys.argv
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.abspath(os.path.join(here, "..", ".."))
prove = os.path.join(root, "_build/default/src/Executable/HeliosVerifiercode/prove.exe")
data = os.path.join(root, "src/Executable/HeliosDatacode")
fixtures = os.path.join(here, "fixtures", "booth.json")
os.makedirs(os.path.join(work, "elections"), exist_ok=True)
algs, cutils = helios_stub.load()

# the IACR group (the trustees' declared parameters of IACR 2024)
tr = json.loads([l for l in open(os.path.join(data, "IACR2024.txt")) if l.startswith(";")][0][1:])
P, Q, G = (int(tr[0]["public_key"][k]) for k in ("p", "q", "g"))

def rng(*tag): return random.Random(":".join([seed, *map(str, tag)]))
def dumps(x): return json.dumps(x, sort_keys=True, separators=(", ", ": "))

# name, candidates, trustees, booth ballots, certified-prover ballots (votes drawn from SEED,
# E4 also has an all-0 and an all-1 ballot of each prover)
ELECTIONS = [("E1", 3, 2, 3, 3), ("E2", 1, 2, 2, 2), ("E3", 7, 2, 2, 2), ("E4", 5, 2, 3, 3), ("E5", 2, 3, 2, 2)]

def votes_for(name, n, k, who):
    r = rng(name, who, "votes")
    vs = [[r.randrange(2) for _ in range(n)] for _ in range(k)]
    if name == "E4": vs[0], vs[1] = [0] * n, [1] * n
    return vs

elections = {}
for name, n, m, kb, kc in ELECTIONS:
    rt = rng(name, "trustees")
    xs = [rt.randrange(1, Q) for _ in range(m)]
    ys = [pow(G, x, P) for x in xs]
    h = 1
    for y in ys: h = h * y % P
    elections[name] = dict(n=n, m=m, xs=xs, ys=ys, h=h, vb=votes_for(name, n, kb, "booth"), vc=votes_for(name, n, kc, "certified"))

# ---- booth ballots: fixtures ----
want = {name: {"y": str(e["h"]), "votes": e["vb"]} for name, e in elections.items()}
fx = json.load(open(fixtures)) if os.path.exists(fixtures) else {}
if regen or any(name not in fx or {k: fx[name][k] for k in ("y", "votes")} != w for name, w in want.items()):
    if not regen: sys.exit("fixtures/booth.json is missing or for other keys/votes (another SEED?): rerun with --regen-booth")
    inp = {"elections": [{"name": name, "p": str(P), "q": str(Q), "g": str(G), "y": w["y"], "votes": w["votes"]} for name, w in want.items()]}
    out = json.loads(subprocess.run(["node", os.path.join(here, "gen_booth.js")], input=json.dumps(inp), capture_output=True, text=True, check=True).stdout)
    fx = {name: {**want[name], "ballots": out[name]} for name in want}
    os.makedirs(os.path.dirname(fixtures), exist_ok=True)
    json.dump(fx, open(fixtures, "w"), indent=1, sort_keys=True)

# ---- certified-prover ballots ----
def certified(name, e):
    r = rng(name, "certified", "randomness")
    inp = {"h": str(e["h"]), "ballots": [{"votes": v, "rs": [str(r.randrange(Q)) for _ in v],
                                          "uscs": [[str(r.randrange(Q)) for _ in range(3)] for _ in v]} for v in e["vc"]]}
    out = subprocess.run([prove], input=json.dumps(inp), capture_output=True, text=True, check=True).stdout
    return [json.loads(l) for l in out.splitlines()]

def ballot(name, i, enc):
    return {"cast_at": "2026-10-21 00:00:%02d" % i,
            "vote": {"answers": [{"choices": enc["choices"], "individual_proofs": enc["individual_proofs"], "overall_proof": None}],
                     "election_hash": "hash-" + name, "election_uuid": "uuid-" + name},
            "vote_hash": "vote-%s-%d" % (name, i), "voter_hash": "voter-%s-%d" % (name, i), "voter_uuid": "voter-uuid-%s-%d" % (name, i)}

specs = {}
for name, e in elections.items():
    encs = fx[name]["ballots"] + certified(name, e)
    votes = e["vb"] + e["vc"]
    ballots = [ballot(name, i, enc) for i, enc in enumerate(encs)]
    n = e["n"]
    agg = [[1, 1] for _ in range(n)]
    for enc in encs:
        for i, ch in enumerate(enc["choices"]):
            agg[i][0] = agg[i][0] * int(ch["alpha"]) % P
            agg[i][1] = agg[i][1] * int(ch["beta"]) % P
    # the trustees, with Helios's own code; its random source is seeded
    r = rng(name, "trustee-proofs")
    cutils.random.mpz_lt = lambda q: r.randrange(q)
    trustees = []
    for j, (x, y) in enumerate(zip(e["xs"], e["ys"])):
        pk = algs.EGPublicKey(); pk.p, pk.q, pk.g, pk.y = P, Q, G, y
        sk = algs.EGSecretKey(); sk.x, sk.pk = x, pk
        pok = sk.prove_sk(algs.DLog_challenge_generator)
        factors, proofs = [], []
        for i in range(n):
            f, pr = sk.decryption_factor_and_proof(algs.EGCiphertext(agg[i][0], agg[i][1], pk), algs.EG_fiatshamir_challenge_generator)
            factors.append(str(f)); proofs.append(pr.to_dict())
        trustees.append({"decryption_factors": [factors], "decryption_proofs": [proofs], "email": "trustee%d@%s.example" % (j, name),
                         "pok": {"challenge": str(pok.challenge), "commitment": str(pok.commitment), "response": str(pok.response)},
                         "public_key": {"g": str(G), "p": str(P), "q": str(Q), "y": str(y)},
                         "public_key_hash": "pkh-%s-%d" % (name, j), "uuid": "trustee-uuid-%s-%d" % (name, j)})
    result = [[sum(v[i] for v in votes) for i in range(n)]]
    with open(os.path.join(work, "elections", name + ".txt"), "w") as f:
        for b in ballots: f.write(dumps(b) + "\n")
        f.write(";" + dumps(trustees) + "\n;" + json.dumps(result) + "\n")
    specs[name] = {"p": str(P), "q": str(Q), "g": str(G), "h": str(e["h"]), "n": n, "m": e["m"],
                   "file": os.path.join(work, "elections", name + ".txt"), "votes": votes,
                   "provers": ["booth"] * len(e["vb"]) + ["certified"] * len(e["vc"]),
                   "election_hash": "hash-" + name, "election_uuid": "uuid-" + name}

# the IACR elections, with the election keys of HeliosTallyIns.v
ins = open(os.path.join(root, "src/Examples/HeliosTallyIns.v")).read()
for year, n in (("2023", 6), ("2024", 7)):
    hval = re.search(r"Definition hval%s\s*:\s*Z\s*:=\s*([0-9]+)" % year, ins).group(1)
    first = json.loads(open(os.path.join(data, "IACR%s.txt" % year)).readline())["vote"]   # the election's hash and UUID
    ntr = len(json.loads([l for l in open(os.path.join(data, "IACR%s.txt" % year)) if l.startswith(";")][0][1:]))
    specs["IACR" + year] = {"p": str(P), "q": str(Q), "g": str(G), "h": hval, "n": n, "m": ntr,
                            "file": os.path.join(data, "IACR%s.txt" % year), "iacr": True,
                            "election_hash": first["election_hash"], "election_uuid": first["election_uuid"]}
json.dump(specs, open(os.path.join(work, "specs.json"), "w"), indent=1, sort_keys=True)
print("elections:", ", ".join("%s (n=%d, m=%d, %d ballots)" % (k, v["n"], v["m"], len(v.get("votes", []))) for k, v in specs.items() if "votes" in v))
