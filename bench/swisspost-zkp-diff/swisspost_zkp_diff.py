#!/usr/bin/env python3
"""Differential testing of the certified verifier of the Swiss Post
zero-knowledge proofs (src/Executable/Swisspostzkp, Examples/SwissPostZkpIns.v)
against the crypto-primitives verifiers (Java, ZkpDiff.java built by build.sh),
for the Schnorr, exponentiation, plaintext equality and decryption proofs
(specification 1.6.0, Section 10).

For each kind: the Swiss Post test vectors, COUNT honest proofs of the
Swiss Post prover (random sizes, k >= l for decryption, random auxiliary
information with empty, Unicode, NUL and long strings) and COUNT/8 under
the generator g = 4, and the proofs of a third prover written here from the
specification for statements at the edges (identities, zero witnesses,
repeated bases, h = h', l = 10); then for every honest case
  - every field mutated by type: group elements (times g, 1, inverse,
    random, swapped with a sibling), exponents (+1, 0, negated, random);
  - the auxiliary information: a string appended, removed, changed, the
    strings reordered, [] <-> [""], a composed <-> decomposed accent, a lone
    surrogate (not UCS; Java's encoder refuses it);
  - the proof replayed on the statement of another case;
  - structure and encoding: vectors one element short or long, e >= q,
    negative and non-minimal encodings, integers not in the group, another
    generator in the context.
Every case gets the Swiss Post verdict (an exception counts as a rejection)
and the certified one (a refusal of the trusted boundary counts as a
rejection); the expected verdict is accept for the honest cases and the
encodings of the same values, reject for the rest, except the key elements
pk_l, ..., pk_{k-1} of a decryption proof, which the proof does not involve.

usage: bench/swisspost-zkp-diff/swisspost_zkp_diff.py BUILD_DIR WORK_DIR [COUNT]"""
import base64, collections, copy, json, os, random, subprocess, sys

build, work = sys.argv[1], sys.argv[2]
count = int(sys.argv[3]) if len(sys.argv) > 3 else 40
root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
vectors = os.path.join(root, "bench/crypto-primitives/src/test/resources/zeroknowledgeproofs")
verifier = os.path.join(root, "_build/default/src/Executable/Swisspostzkp/main.exe")
java = os.path.join(os.environ["JAVA_HOME"], "bin", "java") if "JAVA_HOME" in os.environ else "java"
rng = random.Random(int(os.environ.get("SEED", "1")))
os.makedirs(work, exist_ok=True)
KINDS = ["schnorr", "exponentiation", "plaintext-equality", "decryption"]
VERDICT = {"schnorr": "result", "exponentiation": "verif_result", "plaintext-equality": "output", "decryption": "verif_result"}

def zkpdiff(*args):
    r = subprocess.run([java, "--module-path", f"{build}/classes:{build}/mods", "-m",
                        "ch.post.it.evoting.cryptoprimitives/ch.post.it.evoting.cryptoprimitives.internal.zeroknowledgeproofs.ZkpDiff", *args],
                       capture_output=True, text=True)
    if r.returncode != 0: sys.exit(r.stderr)
    return r.stdout.splitlines()

def dec(s): return int.from_bytes(base64.b64decode(s), "big", signed=True)
def enc(v): return base64.b64encode(v.to_bytes(v.bit_length() // 8 + 1, "big", signed=True)).decode()
raw = lambda b: base64.b64encode(b).decode()

GROUP = {"statement", "bases", "gamma", "phis", "h", "h_prime", "public_key", "message"}
SCALAR = {"e", "z"}
AUX = {"additional_information", "i_aux"}

def leaves(x, path=()):
    if isinstance(x, dict):
        for k, v in x.items(): yield from leaves(v, path + (k,))
    elif isinstance(x, list):
        for i, v in enumerate(x): yield from leaves(v, path + (i,))
    else:
        name = next(p for p in reversed(path) if isinstance(p, str))
        yield path, ("group" if name in GROUP else "scalar" if name in SCALAR else "aux" if name in AUX else None)

def get(x, path):
    for p in path: x = x[p]
    return x
def put(x, path, v): get(x, path[:-1])[path[-1]] = v
def field(path): return "/".join("[]" if isinstance(p, int) else p for p in path)

def aux_path(case):
    return ("input", "i_aux") if "i_aux" in case["input"] else ("input", "additional_information")

def bound(kind, case):
    """what the proof is about: the input, except pk_j for j >= l in a
    decryption proof, which is neither hashed nor in phi; the response z of an
    exponentiation proof whose bases are all 1; the generator,
    except for the exponentiation proof, which does not use it"""
    i = copy.deepcopy(case["input"])
    if kind == "decryption": i["public_key"] = i["public_key"][:len(i["ciphertext"]["phis"])]
    # with every base 1, phi(z) = 1 for every z: the response is not bound
    if kind == "exponentiation" and i["proof"] and all(dec(b) == 1 for b in i["bases"]): i["proof"]["z"] = None
    ctx = {k: v for k, v in case["context"].items() if not (kind == "exponentiation" and k == "g")}
    return json.dumps([ctx, i], sort_keys=True)

def mutants(kind, case):
    """(name, case, expected)"""
    p, q = dec(case["context"]["p"]), dec(case["context"]["q"])
    by_field = collections.defaultdict(list)
    for path, k in leaves(case["input"], ("input",)):
        if k in ("group", "scalar"): by_field[field(path)].append((path, k))
    for f, paths in sorted(by_field.items()):
        path, k = rng.choice(paths)
        v = dec(get(case, path))
        if k == "group":
            ops = [("times g", v * 2 % p), ("identity", 1), ("inverse", pow(v, -1, p)), ("random", pow(2, rng.randrange(q), p))]
            sib = [s for s, _ in paths if s[:-1] == path[:-1] and s != path and get(case, s) != get(case, path)]
        else:
            ops = [("+1", (v + 1) % q), ("zero", 0), ("negated", (-v) % q), ("random", rng.randrange(q))]
            sib = []
        for name, nv in ops + ([("swap with sibling", None)] if sib else []):
            c = copy.deepcopy(case)
            if nv is None:
                s = rng.choice(sib); a, b = get(case, path), get(case, s); put(c, path, b); put(c, s, a)
            else:
                put(c, path, enc(nv))
            if c != case:
                yield f"{f} {name}", c, ("accept" if bound(kind, c) == bound(kind, case) else "reject")
    # the auxiliary information
    ap = aux_path(case); a = get(case, ap)
    def aux(name, new, expect="reject"):
        c = copy.deepcopy(case); put(c, ap, new); return (f"aux: {name}", c, expect)
    yield aux("string appended", a + ["x"])
    if a:
        i = rng.randrange(len(a))
        yield aux("one string removed", a[:i] + a[i + 1:])
        yield aux("one string changed", a[:i] + [a[i] + "x"] + a[i + 1:])
        if a[::-1] != a: yield aux("strings reversed", a[::-1])
    yield aux("[] <-> [\"\"]", [""] if a == [] else ([] if a == [""] else a + [""]))
    yield aux("composed accent", a + ["é"])
    yield aux("decomposed accent", a + ["é"])
    yield aux("lone surrogate", a + ["\ud800"])
    if a and a[0] == "é": yield aux("decomposed -> composed", ["é"] + a[1:])

def structural(kind, case):
    p, q = dec(case["context"]["p"]), dec(case["context"]["q"])
    def edit(name, f, expect="reject"):
        c = copy.deepcopy(case); f(c); return (name, c, expect)
    out = []
    vectors = [pth[:-1] for pth, k in leaves(case["input"], ("input",)) if isinstance(pth[-1], int) and k in ("group", "scalar")]
    for v in sorted(set(vectors)):
        for name, f in [("last dropped", lambda c, v=v: get(c, v).pop()), ("last duplicated", lambda c, v=v: get(c, v).append(get(c, v)[-1]))]:
            c = copy.deepcopy(case); f(c)
            ok = kind == "decryption" and v[-1] == "public_key" and bound(kind, c) == bound(kind, case)
            out.append((f"{field(v)} {name}", c, "accept" if ok else "reject"))
    ep = ("input", "proof", "e"); e = dec(get(case, ep))
    out.append(edit("e + q", lambda c: put(c, ep, enc(e + q))))
    out.append(edit("e - q (negative)", lambda c: put(c, ep, enc(e - q))))
    out.append(edit("e with an extra leading zero byte", lambda c: put(c, ep, raw(b"\0" + base64.b64decode(get(case, ep)))), "accept"))
    gpaths = [pth for pth, k in leaves(case["input"], ("input",)) if k == "group"]
    gp = gpaths[0]; g = dec(get(case, gp))
    out.append(edit(f"{field(gp)} with an extra leading zero byte", lambda c: put(c, gp, raw(b"\0" + base64.b64decode(get(case, gp)))), "accept"))
    for name, v in [("0", 0), ("p", p), ("+ p", g + p), ("p - 1 (not a square)", p - 1), ("p - x (not a square)", p - g), ("-x", -g)]:
        out.append(edit(f"{field(gp)} := {name}", lambda c, v=v: put(c, gp, enc(v))))
    ub = g.to_bytes((g.bit_length() + 7) // 8, "big")
    if ub[0] >= 0x80: out.append(edit(f"{field(gp)} as unsigned bytes (negative)", lambda c: put(c, gp, raw(ub))))
    out.append(edit("generator g := 4 in the context", lambda c: c["context"].__setitem__("g", enc(4)),
                    "accept" if kind == "exponentiation" else "reject"))
    out.append(edit("generator g := 1 in the context", lambda c: c["context"].__setitem__("g", enc(1)),
                    "either" if kind == "exponentiation" else "reject"))
    return [(n, c, e) for n, c, e in out if c != case]   # no-ops, e.g. g := 4 when g = 4

# ---- a third prover, from the specification (Section 10, RecursiveHash of
# Algorithm 5.5), for statements at the edges: identities, zero witnesses,
# repeated bases, h = h', large sizes; both verifiers must accept ----
import hashlib
def rh(v):
    if isinstance(v, bytes): return hashlib.sha3_256(b"\0" + v).digest()
    if isinstance(v, int): return hashlib.sha3_256(b"\1" + (v.to_bytes((v.bit_length() + 7) // 8, "big") if v else b"")).digest()
    if isinstance(v, str): return hashlib.sha3_256(b"\2" + v.encode("utf-8")).digest()
    return hashlib.sha3_256(b"\3" + b"".join(rh(x) for x in v)).digest()

def spec_cases(kind, ctx):
    p, q, g = dec(ctx["p"]), dec(ctx["q"]), dec(ctx["g"])
    E = lambda v: enc(v % p); S = lambda v: enc(v % q)
    def haux(tag, extra, aux): return [tag] + extra + ([aux] if aux else [])
    def chal(f, y, c, h): return int.from_bytes(rh([f, y, c, h]), "big")
    out = []
    auxes = [[], ["", "\U0001F5F3", "a\0b"], ["x" * 5000], ["ok"]]
    if kind == "schnorr":
        for name, x in [("x = 0, y = 1", 0), ("x = 1", 1), ("x = q - 1", q - 1)]:
            for aux in auxes[:2]:
                y = pow(g, x, p); b = rng.randrange(q); c = pow(g, b, p)
                e = chal([p, q, g], y, c, haux("SchnorrProof", [], aux))
                out.append((name, {"input": {"proof": {"e": S(e), "z": S(b + e * x)}, "statement": E(y), "additional_information": aux},
                                   "output": {"result": "true"}}))
    elif kind == "exponentiation":
        r = lambda: pow(g, rng.randrange(1, q), p)
        for name, gs, x in [("a base 1", [1, r()], rng.randrange(q)), ("all bases equal", [g] * 3, rng.randrange(q)),
                            ("x = 0", [r(), r()], 0), ("n = 20", [r() for _ in range(20)], rng.randrange(q)), ("bases = [1]", [1], 5)]:
            for aux in auxes[1:3]:
                ys = [pow(b_, x, p) for b_ in gs]; b = rng.randrange(q); cs = [pow(b_, b, p) for b_ in gs]
                e = chal([p, q, gs], ys, cs, haux("ExponentiationProof", [], aux))
                out.append((name, {"input": {"bases": [E(v) for v in gs], "statement": [E(v) for v in ys],
                                             "proof": {"e": S(e), "z": S(b + e * x)}, "additional_information": aux},
                                   "output": {"verif_result": "true"}}))
    elif kind == "plaintext-equality":
        r_ = lambda: pow(g, rng.randrange(1, q), p)
        for name, h, h2, r1, r2, msg in [("h = h'", None, None, rng.randrange(q), rng.randrange(q), r_()),
                                          ("r = r' = 0", r_(), r_(), 0, 0, r_()), ("message 1", r_(), r_(), rng.randrange(q), rng.randrange(q), 1),
                                          ("h = 1", 1, r_(), rng.randrange(q), rng.randrange(q), r_())]:
            if h is None: h = h2 = r_()
            for aux in auxes[:2]:
                c0, c1 = pow(g, r1, p), pow(h, r1, p) * msg % p
                c0_, c1_ = pow(g, r2, p), pow(h2, r2, p) * msg % p
                b1, b2 = rng.randrange(q), rng.randrange(q)
                cs = [pow(g, b1, p), pow(g, b2, p), pow(h, b1, p) * pow(pow(h2, b2, p), -1, p) % p]
                ys = [c0, c0_, c1 * pow(c1_, -1, p) % p]
                e = chal([p, q, g, h, h2], ys, cs, haux("PlaintextEqualityProof", [c1, c1_], aux))
                out.append((name, {"input": {"upper_c": {"gamma": E(c0), "phis": [E(c1)]}, "upper_c_prime": {"gamma": E(c0_), "phis": [E(c1_)]},
                                             "h": E(h), "h_prime": E(h2), "proof": {"e": S(e), "z": [S(b1 + e * r1), S(b2 + e * r2)]}, "i_aux": aux},
                                   "output": {"output": "true"}}))
    elif kind == "decryption":
        for name, l, k, r, zero_sk in [("gamma = 1 (r = 0)", 2, 2, 0, False), ("sk = 0, pk = 1", 2, 3, None, True),
                                       ("l = k = 1", 1, 1, None, False), ("l = 10, k = 12", 10, 12, None, False)]:
            for aux in auxes[:2]:
                sk = [0 if zero_sk else rng.randrange(q) for _ in range(k)]; pk = [pow(g, s, p) for s in sk]
                r1 = rng.randrange(q) if r is None else r
                ms = [pow(g, rng.randrange(q), p) for _ in range(l)]
                gamma = pow(g, r1, p); phis = [pow(pk[i], r1, p) * ms[i] % p for i in range(l)]
                bs = [rng.randrange(q) for _ in range(l)]
                cs = [pow(g, b_, p) for b_ in bs] + [pow(gamma, b_, p) for b_ in bs]
                ys = pk[:l] + [phis[i] * pow(ms[i], -1, p) % p for i in range(l)]
                e = chal([p, q, g, gamma], ys, cs, haux("DecryptionProof", [phis, ms], aux))
                out.append((name, {"input": {"ciphertext": {"gamma": E(gamma), "phis": [E(v) for v in phis]}, "public_key": [E(v) for v in pk],
                                             "message": [E(v) for v in ms], "proof": {"e": S(e), "z": [S(bs[i] + e * sk[i]) for i in range(l)]},
                                             "additional_information": aux}, "output": {"verif_result": "true"}}))
    return [{"description": f"spec prover {kind}: {n}", "context": dict(ctx), **c} for n, c in out]

def certified(kind, cases, tag):
    f = os.path.join(work, f"{tag}.json"); json.dump(cases, open(f, "w"))
    r = subprocess.run([verifier, kind, f], capture_output=True, text=True)
    lines = [l.split("\t") for l in r.stdout.splitlines() if l and l[0].isdigit()]
    if len(lines) == len(cases): return [(l[1], l[4]) for l in lines]
    out = []   # the file as a whole was refused (e.g. by the JSON parser): one case at a time
    for i, c in enumerate(cases):
        g = os.path.join(work, f"{tag}-{i}.json"); json.dump([c], open(g, "w"))
        r = subprocess.run([verifier, kind, g], capture_output=True, text=True)
        l = [x.split("\t") for x in r.stdout.splitlines() if x and x[0].isdigit()]
        out.append((l[0][1], l[0][4]) if l else ("false", "(refused: " + (r.stderr.strip().splitlines() or ["?"])[-1][:80] + ")"))
    return out

total_dis = 0
for kind in KINDS:
    honest = json.load(open(os.path.join(vectors, f"verify-{kind}.json")))
    for h in honest: h["description"] = "vector " + h["description"]
    gen = os.path.join(work, f"{kind}-honest.json")
    zkpdiff("gen", kind, os.path.join(vectors, f"verify-{kind}.json"), gen, str(count))
    honest += json.load(open(gen))
    # honest proofs under another generator of G_q (g = 4 = 2^2)
    fx = json.load(open(os.path.join(vectors, f"verify-{kind}.json")))[:1]; fx[0]["context"]["g"] = enc(4)
    g4 = os.path.join(work, f"{kind}-g4.json"); json.dump(fx, open(g4, "w"))
    zkpdiff("gen", kind, g4, gen, str(max(1, count // 8)))
    for h in json.load(open(gen)): h["description"] += ", g=4"; honest.append(h)
    honest += spec_cases(kind, json.load(open(os.path.join(vectors, f"verify-{kind}.json")))[0]["context"])
    cases, expects = [], []
    for i, h in enumerate(honest):
        cases.append(h); expects.append("accept")
        for name, c, e in list(mutants(kind, h)) + structural(kind, h):
            c["description"] = h["description"] + " | " + name; cases.append(c); expects.append(e)
        # replay on the statement of another case
        o = honest[(i + 1) % len(honest)]
        c = copy.deepcopy(o); c["input"]["proof"] = copy.deepcopy(h["input"]["proof"])
        c["description"] = h["description"] + " | proof replayed on " + o["description"]; cases.append(c)
        same = bound(kind, {**c, "input": {**c["input"], "proof": None}}) == bound(kind, {**h, "input": {**h["input"], "proof": None}})
        expects.append("accept" if same else "reject")
    f = os.path.join(work, f"{kind}-cases.json"); json.dump(cases, open(f, "w"))
    javas = zkpdiff("verify", kind, f)
    assert len(javas) == len(cases)
    for c, j in zip(cases, javas): c["output"] = {VERDICT[kind]: "true" if j == "true" else "false"}
    ours = certified(kind, cases, f"{kind}-certified")
    tally, notes = collections.Counter(), []
    with open(os.path.join(work, f"{kind}.tsv"), "w") as t:
        for c, e, j, (o, note) in zip(cases, expects, javas, ours):
            jv = "accept" if j == "true" else "reject"; ov = "accept" if o == "true" else "reject"
            agree = jv == ov
            tally[(e, "swisspost " + ("exception" if j.startswith("error") else jv),
                   "ours " + ("refused" if "(input:" in note or "(refused" in note else ov), "agree" if agree else "DISAGREE")] += 1
            t.write(f"{e}\t{j[:160]}\t{o}\t{note}\n")
            if not agree or (e != "either" and (jv != e or ov != e)):
                notes.append(f"  {'agree' if agree else 'DISAGREE':8} expected {e}  swisspost: {j[:110]}\n{'':11}ours: {o} {note[:160]}")
    print(f"\n{kind}: {len(cases)} cases ({len(honest)} honest; verdicts in {kind}.tsv)")
    for k, n in sorted(tally.items()): print("  expected " + ", ".join(k) + f": {n}")
    for n in notes[:40]: print(n)
    if len(notes) > 40: print(f"  ... {len(notes) - 40} more")
    total_dis += sum(n for k, n in tally.items() if k[3] != "agree")
print(f"\n{total_dis} disagreements")
sys.exit(1 if total_dis else 0)
