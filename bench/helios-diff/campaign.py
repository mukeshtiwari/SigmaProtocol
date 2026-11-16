#!/usr/bin/env python3
"""The Helios differential campaign. From the base elections of gen.py:

  honest      the base elections and IACR 2023, 2024 as published
  field       one random occurrence of every field of the ballots (ciphertexts,
              commitments, challenges, responses), trustees (keys, proofs of
              knowledge, decryption factors and proofs) and the tally, mutated
              by type: group elements (times g, 1, inverse, random, swapped
              with a sibling), exponents (+1, 0, negated, random), the tally
              (+1, -1, swapped); unverified metadata (strings, the trustees'
              declared group) changed
  structural  list lengths, sub-structures, field sets and order, the
              overall proof, number encodings of one group element, values
              outside the group or the exponent range
  tally       dropped and duplicated ballots, a wrong published tally, a
              trustee's decryption replaced by another's, trustees reordered,
              removed or replaced by a fresh trustee, a wrong election key, a
              ballot under another key

Each case is an election file; Helios's own crypto (oracle_helios.py) and
the certified verifier (diff.exe) give their component verdicts, which are
compared: the election verdict (final), and the per-ballot verdicts where
both parsed. Writes results/verdicts.tsv (per case) and results/summary.tsv.

usage: campaign.py SEED WORK_DIR RESULTS_DIR [--no-iacr]"""
import collections, concurrent.futures, copy, json, os, random, subprocess, sys
import helios_stub

seed, work, results = sys.argv[1], sys.argv[2], sys.argv[3]
no_iacr = "--no-iacr" in sys.argv
here = os.path.dirname(os.path.abspath(__file__))
root = os.path.abspath(os.path.join(here, "..", ".."))
diff = os.path.join(root, "_build/default/src/Executable/HeliosVerifiercode/diff.exe")
prove = os.path.join(root, "_build/default/src/Executable/HeliosVerifiercode/prove.exe")
specs = json.load(open(os.path.join(work, "specs.json")))
algs, cutils = helios_stub.load()
cdir = os.path.join(work, "cases"); os.makedirs(cdir, exist_ok=True); os.makedirs(results, exist_ok=True)

def dumps(x, sort=True): return json.dumps(x, sort_keys=sort, separators=(", ", ": "))
def load(path):
    bl, ex = [], []
    for l in open(path, encoding="utf-8"):
        l = l.strip()
        if l: (ex if l.startswith(";") else bl).append(l)
    return {"ballots": [json.loads(l) for l in bl], "trustees": json.loads(ex[0][1:]), "result": json.loads(ex[1][1:])}
def text(el, raw_ballots=None):
    lines = raw_ballots if raw_ballots is not None else [dumps(b) for b in el["ballots"]]
    return "\n".join(lines) + "\n;" + dumps(el["trustees"]) + "\n;" + json.dumps(el["result"]) + "\n"

cases = []
def add(source, ename, desc, expect, content=None, spec=None, file=None):
    cid = "%04d" % len(cases)
    if file is None:
        file = os.path.join(cdir, cid + ".txt")
        open(file, "w", encoding="utf-8").write(content)
    cases.append({"id": cid, "source": source, "election": ename, "desc": desc, "expect": expect, "file": file,
                  "spec": spec or specs[ename]})

def get(x, path):
    for k in path: x = x[k]
    return x
def put(x, path, v): get(x, path[:-1])[path[-1]] = v

for ename, sp in sorted(specs.items()):
    if sp.get("iacr"):
        if not no_iacr: add("honest", ename, "as published", "accept", file=sp["file"])
        continue
    P, Q, G, n = int(sp["p"]), int(sp["q"]), int(sp["g"]), sp["n"]
    base = load(sp["file"])
    rng = random.Random("%s:%s:mutants" % (seed, ename))
    add("honest", ename, "as generated", "accept", text(base))

    # ---- field mutants ----
    fields = collections.defaultdict(list)   # field name -> [(path, kind)]
    for i, b in enumerate(base["ballots"]):
        ans = ["ballots", i, "vote", "answers", 0]
        for c in range(n):
            fields["ballot alpha"].append((ans + ["choices", c, "alpha"], "G"))
            fields["ballot beta"].append((ans + ["choices", c, "beta"], "G"))
            for br in (0, 1):
                pr = ans + ["individual_proofs", c, br]
                fields["ballot proof A (branch %d)" % br].append((pr + ["commitment", "A"], "G"))
                fields["ballot proof B (branch %d)" % br].append((pr + ["commitment", "B"], "G"))
                fields["ballot proof challenge (branch %d)" % br].append((pr + ["challenge"], "F"))
                fields["ballot proof response (branch %d)" % br].append((pr + ["response"], "F"))
        for k in ("cast_at", "vote_hash", "voter_hash", "voter_uuid"): fields["ballot " + k].append((["ballots", i, k], "S"))
        for k in ("election_hash", "election_uuid"): fields["ballot " + k].append((["ballots", i, "vote", k], "S"))
    for j, t in enumerate(base["trustees"]):
        T = ["trustees", j]
        fields["trustee y"].append((T + ["public_key", "y"], "G"))
        for k in ("g", "p", "q"): fields["trustee declared " + k].append((T + ["public_key", k], "S"))
        for k in ("email", "public_key_hash", "uuid"): fields["trustee " + k].append((T + [k], "S"))
        fields["pok commitment"].append((T + ["pok", "commitment"], "G"))
        fields["pok challenge"].append((T + ["pok", "challenge"], "F"))
        fields["pok response"].append((T + ["pok", "response"], "F"))
        for c in range(n):
            fields["decryption factor"].append((T + ["decryption_factors", 0, c], "G"))
            dp = T + ["decryption_proofs", 0, c]
            fields["decryption proof A"].append((dp + ["commitment", "A"], "G"))
            fields["decryption proof B"].append((dp + ["commitment", "B"], "G"))
            fields["decryption proof challenge"].append((dp + ["challenge"], "F"))
            fields["decryption proof response"].append((dp + ["response"], "F"))
    for c in range(n): fields["published tally"].append((["result", 0, c], "T"))
    for fname, paths in sorted(fields.items()):
        path, kind = rng.choice(paths)
        v = get(base, path)
        if kind == "G":
            x = int(v)
            ops = [("times g", str(x * G % P)), ("1", "1"), ("inverse", str(pow(x, -1, P))), ("random", str(pow(G, rng.randrange(Q), P)))]
            sib = [p2 for p2, _ in paths if p2 != path and get(base, p2) != v]
            if sib: ops.append(("swapped with a sibling", rng.choice(sib)))
        elif kind == "F":
            x = int(v)
            ops = [("+1", str((x + 1) % Q)), ("0", "0"), ("negated", str((-x) % Q)), ("random", str(rng.randrange(Q)))]
        elif kind == "T":
            ops = [("+1", v + 1)] + ([("-1", v - 1)] if v > 0 else [])
            others = [p2 for p2, _ in paths if p2 != path and get(base, p2) != v]
            if others: ops.append(("swapped with another candidate", rng.choice(others)))
        elif fname.startswith("trustee declared"):   # another number: the declared group, unused by both
            ops = [("changed", str(int(v) + 2))]
        else:
            ops = [("changed", v + "-changed")]
        for oname, nv in ops:
            el = copy.deepcopy(base)
            if isinstance(nv, list):
                a, b = get(base, path), get(base, nv); put(el, path, b); put(el, nv, a)
            else:
                put(el, path, nv)
            if el == base: continue
            # the ballot's election hash and UUID bind it to the election (EncryptedVote.verify)
            binding = fname in ("ballot election_hash", "ballot election_uuid")
            add("field", ename, "%s %s" % (fname, oname), "either" if kind == "S" and not binding else "reject", text(el))

    # ---- structural and encoding mutants ----
    ans0 = ["ballots", 0, "vote", "answers", 0]
    def mutate(desc, f, expect):
        el = copy.deepcopy(base); f(el); add("structural", ename, desc, expect, text(el))
    mutate("ballot 0: last choice dropped", lambda el: get(el, ans0 + ["choices"]).pop(), "reject")
    mutate("ballot 0: last choice duplicated", lambda el: get(el, ans0 + ["choices"]).append(copy.deepcopy(get(el, ans0 + ["choices"])[-1])), "reject")
    mutate("ballot 0: last proof dropped", lambda el: get(el, ans0 + ["individual_proofs"]).pop(), "reject")
    mutate("ballot 0: last proof duplicated", lambda el: get(el, ans0 + ["individual_proofs"]).append(copy.deepcopy(get(el, ans0 + ["individual_proofs"])[-1])), "reject")
    mutate("ballot 0: proof 0 with one branch", lambda el: get(el, ans0 + ["individual_proofs", 0]).pop(), "reject")
    mutate("ballot 0: proof 0 with a third branch", lambda el: get(el, ans0 + ["individual_proofs", 0]).append(copy.deepcopy(get(el, ans0 + ["individual_proofs", 0, 0]))), "reject")
    mutate("ballot 0: overall_proof [] instead of null", lambda el: put(el, ans0 + ["overall_proof"], []), "either")
    mutate("ballot 0: overall_proof = proof 0", lambda el: put(el, ans0 + ["overall_proof"], copy.deepcopy(get(el, ans0 + ["individual_proofs", 0]))), "either")
    mutate("ballot 0: answer duplicated", lambda el: get(el, ["ballots", 0, "vote", "answers"]).append(copy.deepcopy(get(el, ans0))), "reject")
    mutate("ballot 0: extra field", lambda el: get(el, ["ballots", 0]).__setitem__("extra", "x"), "either")
    mutate("ballot 0: voter_uuid missing", lambda el: get(el, ["ballots", 0]).pop("voter_uuid"), "either")
    mutate("trustee 0: last decryption factor dropped", lambda el: get(el, ["trustees", 0, "decryption_factors", 0]).pop(), "reject")
    mutate("trustee 0: extra decryption factor", lambda el: get(el, ["trustees", 0, "decryption_factors", 0]).append(get(el, ["trustees", 0, "decryption_factors", 0, 0])), "reject")
    mutate("trustee 0: last decryption proof dropped", lambda el: get(el, ["trustees", 0, "decryption_proofs", 0]).pop(), "reject")
    mutate("published tally: last entry dropped", lambda el: el["result"][0].pop(), "reject")
    mutate("published tally: extra entry", lambda el: el["result"][0].append(0), "reject")
    # ballot 0's keys in reverse order (same JSON object)
    raw = [dumps(b) for b in base["ballots"]]
    rev = lambda d: {k: rev(d[k]) for k in sorted(d, reverse=True)} if isinstance(d, dict) else [rev(x) for x in d] if isinstance(d, list) else d
    add("structural", ename, "ballot 0: keys in reverse order", "either", text(base, [dumps(rev(base["ballots"][0]), sort=False)] + raw[1:]))
    # encodings of the same integer, and values outside the group or Z_q
    apath = ans0 + ["choices", 0, "alpha"]; a = int(get(base, apath))
    rpath = ans0 + ["individual_proofs", 0, 0, "response"]; r = int(get(base, rpath))
    full = "".join(chr(0xFF10 + int(d)) for d in str(a))
    for desc, val, exp in [("leading zero", "0" + str(a), "either"), ("plus sign", "+" + str(a), "either"),
                           ("leading space", " " + str(a), "either"), ("trailing space", str(a) + " ", "either"),
                           ("digit-group underscore", str(a)[:3] + "_" + str(a)[3:], "either"),
                           ("full-width digits", full, "either"), ("hexadecimal 0x", hex(a), "either"),
                           ("decimal point", str(a) + ".0", "either"),
                           ("0", "0", "reject"), ("p", str(P), "reject"), ("alpha + p", str(a + P), "reject"),
                           ("p - alpha", str(P - a), "reject"), ("-alpha", str(-a), "reject")]:
        el = copy.deepcopy(base); put(el, apath, val)
        add("structural", ename, "ballot 0 alpha: " + desc, exp, text(el))
    for desc, val in [("q", str(Q)), ("response + q", str(r + Q)), ("-1", "-1")]:
        el = copy.deepcopy(base); put(el, rpath, val)
        add("structural", ename, "ballot 0 response: " + desc, "reject", text(el))

    # ---- tally-level tampering ----
    votes = sp["votes"]
    def tamper(desc, f, expect, spec=None):
        el = copy.deepcopy(base); f(el); add("tally", ename, desc, expect, text(el), spec)
    nz = next(i for i, v in enumerate(votes) if any(v))
    tamper("ballot %d (votes %s) dropped" % (nz, votes[nz]), lambda el: el["ballots"].pop(nz), "reject")
    tamper("ballot %d (votes %s) duplicated" % (nz, votes[nz]), lambda el: el["ballots"].append(copy.deepcopy(el["ballots"][nz])), "reject")
    z = next((i for i, v in enumerate(votes) if not any(v)), None)
    if z is not None:   # the counts are unchanged, but the decryption factors are bound to the aggregate ciphertext
        tamper("all-0 ballot %d dropped" % z, lambda el: el["ballots"].pop(z), "reject")
        tamper("all-0 ballot %d duplicated" % z, lambda el: el["ballots"].append(copy.deepcopy(el["ballots"][z])), "reject")
    tamper("published tally: candidate 0 + 1", lambda el: el["result"][0].__setitem__(0, el["result"][0][0] + 1), "reject")
    def borrow(el):
        el["trustees"][0]["decryption_factors"] = copy.deepcopy(el["trustees"][1]["decryption_factors"])
        el["trustees"][0]["decryption_proofs"] = copy.deepcopy(el["trustees"][1]["decryption_proofs"])
    tamper("trustee 0's decryption replaced by trustee 1's", borrow, "reject")
    tamper("trustees in reverse order", lambda el: el["trustees"].reverse(), "accept")
    tamper("last trustee removed", lambda el: el["trustees"].pop(), "reject")
    tamper("election key h times g", lambda el: None, "reject", {**sp, "h": str(int(sp["h"]) * G % P)})
    # a fresh trustee replacing the last one, with valid proofs for its own key (Helios's code)
    def fresh(el):
        fr = random.Random("%s:%s:fresh" % (seed, ename))
        cutils.random.mpz_lt = lambda q: fr.randrange(q)
        x = fr.randrange(1, Q); pk = algs.EGPublicKey(); pk.p, pk.q, pk.g, pk.y = P, Q, G, pow(G, x, P)
        sk = algs.EGSecretKey(); sk.x, sk.pk = x, pk
        agg = [[1, 1] for _ in range(n)]
        for bb in base["ballots"]:
            for i, ch in enumerate(bb["vote"]["answers"][0]["choices"]):
                agg[i][0] = agg[i][0] * int(ch["alpha"]) % P; agg[i][1] = agg[i][1] * int(ch["beta"]) % P
        pok = sk.prove_sk(algs.DLog_challenge_generator)
        fs = [sk.decryption_factor_and_proof(algs.EGCiphertext(agg[i][0], agg[i][1], pk), algs.EG_fiatshamir_challenge_generator) for i in range(n)]
        t = el["trustees"][-1]
        t["public_key"]["y"] = str(pk.y)
        t["pok"] = {"challenge": str(pok.challenge), "commitment": str(pok.commitment), "response": str(pok.response)}
        t["decryption_factors"] = [[str(f) for f, _ in fs]]; t["decryption_proofs"] = [[pr.to_dict() for _, pr in fs]]
    tamper("last trustee replaced by a fresh trustee with valid proofs", fresh, "reject")
    # a ballot of the certified prover under another key (invalid here, so not counted)
    other = random.Random("%s:%s:other" % (seed, ename))
    k2 = pow(G, other.randrange(1, Q), P)
    inp = {"h": str(k2), "ballots": [{"votes": [1] * n, "rs": [str(other.randrange(Q)) for _ in range(n)],
                                      "uscs": [[str(other.randrange(Q)) for _ in range(3)] for _ in range(n)]}]}
    enc = json.loads(subprocess.run([prove], input=json.dumps(inp), capture_output=True, text=True, check=True).stdout)
    def foreign(el):
        b = copy.deepcopy(el["ballots"][0]); b["vote"]["answers"][0]["choices"] = enc["choices"]
        b["vote"]["answers"][0]["individual_proofs"] = enc["individual_proofs"]; el["ballots"].append(b)
    tamper("ballot encrypted under another key appended", foreign, "accept")

# ---- the two oracles ----
manifest = [{"file": c["file"], "spec": c["spec"]} for c in cases]
json.dump(manifest, open(os.path.join(work, "manifest.json"), "w"))
py_out = os.path.join(work, "helios.jsonl")
py = subprocess.Popen([sys.executable, "-I", os.path.join(here, "oracle_helios.py"),
                       os.path.join(work, "manifest.json"), py_out, "3"])
groups = collections.defaultdict(list)
for c in cases: groups[(c["spec"]["n"], c["spec"]["m"], c["spec"]["h"], c["spec"]["election_hash"], c["spec"]["election_uuid"])].append(c["file"])
def run_group(item):
    (n, m, h, eh, eu), files = item
    out = []
    for k in range(0, len(files), 16):
        r = subprocess.run([diff, str(n), str(m), h, eh, eu, *files[k:k + 16]], capture_output=True, text=True)
        got = {json.loads(l)["file"]: json.loads(l) for l in r.stdout.splitlines() if l.startswith("{")}
        chunk = files[k:k + 16]
        if r.returncode != 0:   # a crash ends the chunk: run its files one by one
            for f in chunk:
                if f in got: continue
                r1 = subprocess.run([diff, str(n), str(m), h, eh, eu, f], capture_output=True, text=True)
                ls = [json.loads(l) for l in r1.stdout.splitlines() if l.startswith("{")]
                got[f] = ls[0] if ls else {"file": f, "parse": "crash: exit %d" % r1.returncode, "ballots": [],
                                            "pk": False, "decryption": False, "pok": False, "tally": False, "final": False}
        out += [got[f] for f in chunk]
    return out
with concurrent.futures.ThreadPoolExecutor(1) as ex:
    cert = {o["file"]: o for g in ex.map(run_group, sorted(groups.items())) for o in g}
if py.wait() != 0: sys.exit("oracle_helios.py failed")
hel = {}
for l in open(py_out):
    o = json.loads(l); hel[o["file"]] = o

# ---- comparison ----
rows, summ = [], collections.OrderedDict()
for c in cases:
    h, o = hel[c["file"]], cert[c["file"]]
    hv, ov = ("accept" if h["final"] else "reject"), ("accept" if o["final"] else "reject")
    ballot_diff = h["parse"] == "ok" and o["parse"] == "ok" and h["ballots"] != o["ballots"]
    status = "agree" if hv == ov and not ballot_diff else ("DISAGREE" if hv != ov else "BALLOT-DIFF")
    unexpected = c["expect"] != "either" and (hv != c["expect"] or ov != c["expect"])
    rows.append([c["id"], c["source"], c["election"], c["expect"], hv, ov, status, "yes" if unexpected else "",
                 h["parse"] if h["parse"] != "ok" else "", o["parse"] if o["parse"] != "ok" else "", c["desc"]])
    s = summ.setdefault(c["source"], collections.Counter())
    s["cases"] += 1; s["helios %s, certified %s" % (hv, ov)] += 1
    s["disagreements"] += hv != ov; s["ballot-level differences"] += ballot_diff; s["unexpected"] += unexpected
with open(os.path.join(results, "verdicts.tsv"), "w") as f:
    f.write("id\tsource\telection\texpected\thelios\tcertified\tstatus\tunexpected\thelios_note\tcertified_note\tcase\n")
    for r in rows: f.write("\t".join(r) + "\n")
cols = ["cases", "helios accept, certified accept", "helios reject, certified reject", "helios accept, certified reject",
        "helios reject, certified accept", "disagreements", "ballot-level differences", "unexpected"]
with open(os.path.join(results, "summary.tsv"), "w") as f:
    f.write("source\t" + "\t".join(cols) + "\n")
    tot = collections.Counter()
    for src, s in summ.items():
        f.write(src + "\t" + "\t".join(str(s[k]) for k in cols) + "\n"); tot.update(s)
    f.write("total\t" + "\t".join(str(tot[k]) for k in cols) + "\n")
print(open(os.path.join(results, "summary.tsv")).read())
for r in rows:
    if r[6] != "agree" or r[7]: print("\t".join(r))
