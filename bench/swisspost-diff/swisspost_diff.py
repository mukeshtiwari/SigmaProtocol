#!/usr/bin/env python3
"""Differential testing of the certified Bayer–Groth verifier
(src/Executable/Bgverifier, --diff and --gen modes) against the Swiss Post
crypto-primitives verifier (Java, BgDiff.java built by build.sh).

Stage 1, Swiss Post prover: honest shuffle arguments for each M,N,L; every
  field of the context (pk, ck), the statement and the argument is mutated by
  type: group elements (times g, 1, inverse, random, swapped with a sibling),
  exponents (+1, 0, negated, random); the statement's lists are permuted or
  replaced by the input list.
Stage 2, extracted prover (main.exe --gen): honest arguments with degenerate
  randomness or statements, which both verifiers must accept, and arguments
  of a prover run on a witness that does not explain the statement (every
  Fiat–Shamir challenge derived from the transcript), which both must reject.
Stage 3, structure and encoding: vectors one element short or long,
  sub-arguments removed, N not a multiple of m, non-minimal and negative
  encodings, exponents >= q, integers that are not group elements.

Every case gets the Swiss Post verdict (an exception of its checks counts as
a rejection) and the certified verdict (a parse failure of the trusted
boundary counts as a rejection), each certified run on its own file, in
parallel; on the honest cases of stage 1 the challenges x, y, z are compared.

Stage 4, the production path: shuffles of MixnetService.genVerifiableShuffle
  for large N under both optimization modes (COMPUTATION_OPTIMIZED, the
  default: m = 1, n = N; MEMORY_OPTIMIZED: m the largest divisor of N up to
  sqrt(N)), with the verifiable commitment key, and a sample of stage-1
  mutants of each; the Java verdicts of ShuffleArgumentService (key from the
  file) and of the production MixnetService.verifyShuffle (key derived) are
  compared too, except on mutants of the commitment key, which the
  production verifier does not read.

usage: bench/swisspost-diff/swisspost_diff.py BUILD_DIR WORK_DIR [--stages 1234] [--java M,N,L[,K] ...] [--ocaml M,N,L ...]
         [--prod N,L[,K] ...] [--prod-mutants K]"""
import base64, collections, concurrent.futures, copy, json, os, random, subprocess, sys

build, work = sys.argv[1], sys.argv[2]
opts = {"--stages": ["123"], "--java": [], "--ocaml": [], "--prod": [], "--prod-mutants": ["6"]}
cur = None
for a in sys.argv[3:]:
    if a in opts: cur = a
    else: opts[cur].append(a)
stages = opts["--stages"][-1]
java_shapes = opts["--java"] or ["1,2,1", "1,3,3", "2,2,1", "2,3,2", "3,4,2", "4,4,1", "8,8,2", "1,2,1,3", "2,3,2,4"]   # M,N,L[,K]
ocaml_shapes = opts["--ocaml"] or ["1,2,1", "2,2,1", "2,3,2", "3,3,2"]
prod_shapes = opts["--prod"] or ["2,1", "2,3", "3,1", "3,3", "7,1", "7,3", "16,1", "16,3", "100,1", "100,3",
                                 "257,1", "257,3", "1000,1", "1000,3", "100,1,3"]   # N,L[,K]
prod_mutants = int(opts["--prod-mutants"][-1])
root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
fixture = os.path.join(root, "src/Executable/Bgverifier/data/verify-shuffle-argument.json")
verifier = os.path.join(root, "_build/default/src/Executable/Bgverifier/main.exe")
java = os.path.join(os.environ["JAVA_HOME"], "bin", "java") if "JAVA_HOME" in os.environ else "java"
rng = random.Random(int(os.environ.get("SEED", "1")))
os.makedirs(work, exist_ok=True)

def bgdiff(*args):
    r = subprocess.run([java, "--module-path", f"{build}/classes:{build}/mods", "-m",
                        "ch.post.it.evoting.cryptoprimitives/ch.post.it.evoting.cryptoprimitives.internal.mixnet.BgDiff", *args],
                       capture_output=True, text=True)
    if r.returncode != 0: sys.exit(r.stderr)
    return r.stdout.splitlines()

# ---- values: Base64 of Java BigInteger.toByteArray() ----
def dec(s): return int.from_bytes(base64.b64decode(s), "big", signed=True)
def enc(v): return base64.b64encode(v.to_bytes(v.bit_length() // 8 + 1, "big", signed=True)).decode()

# ---- the fields, by type ----
GROUP = {"pk", "h", "ca", "cb", "c_b", "cUpperB", "c_a0", "c_bm", "c_d", "c_lower_delta", "c_upper_delta", "c_a_0", "gamma", "phis"}
SCALAR = {"a", "b", "r", "s", "t", "a_tilde", "b_tilde", "r_tilde", "s_tilde", "tau"}

def leaves(x, path=()):
    """(path, kind) of every leaf; list elements are addressed by index"""
    if isinstance(x, dict):
        for k, v in x.items(): yield from leaves(v, path + (k,))
    elif isinstance(x, list):
        for i, v in enumerate(x): yield from leaves(v, path + (i,))
    else:
        name = next(p for p in reversed(path) if isinstance(p, str))
        if path[0] == "context" and name == "g" and len(path) > 2: name = "ck_g"   # the commitment key generators
        yield path, ("group" if name in GROUP or name == "ck_g" else "scalar" if name in SCALAR else None)

def get(x, path):
    for p in path: x = x[p]
    return x
def put(x, path, v): get(x, path[:-1])[path[-1]] = v

def field(path):   # the field name with list indices elided, e.g. input/argument/ca/[]
    return "/".join("[]" if isinstance(p, int) else p for p in path)

def fields_of(case):
    by_field = collections.defaultdict(list)
    for path, kind in leaves(case):
        if kind and path[0] in ("context", "input"): by_field[field(path)].append((path, kind))
    return by_field

def mutants(case, only=None):
    """only: a set of field names (and "statement" for the statement-level mutants) to restrict to"""
    p, q = dec(case["context"]["p"]), dec(case["context"]["q"])
    by_field = fields_of(case)
    for f, paths in sorted(by_field.items()):
        if only is not None and f not in only: continue
        path, kind = rng.choice(paths)   # one random occurrence of each field
        v = dec(get(case, path))
        if kind == "group":
            ops = [("times g", v * 2 % p), ("identity", 1), ("inverse", pow(v, -1, p)), ("random", pow(2, rng.randrange(q), p))]
            sib = [s for s, _ in paths if s[:-1] == path[:-1] and s != path and get(case, s) != get(case, path)]
            if sib:
                s = rng.choice(sib); ops.append(("swap with sibling", None))
        else:
            ops = [("+1", (v + 1) % q), ("zero", 0), ("negated", (-v) % q), ("random", rng.randrange(q))]
        for name, nv in ops:
            c = copy.deepcopy(case)
            if nv is None:
                a, b = get(case, path), get(case, s); put(c, path, b); put(c, s, a)
            else:
                put(c, path, enc(nv))
            if c != case:   # e.g. c_d[m+1] of the zero argument is com(0; 0) = 1 already
                yield f"{f} {name}", c
    if only is not None and "statement" not in only: return
    st = case["input"]["statement"]
    if len(st["shuffled_ciphertexts"]) >= 2:
        for lst in ("ciphertexts", "shuffled_ciphertexts"):
            c = copy.deepcopy(case); l = c["input"]["statement"][lst]
            i, j = rng.sample(range(len(l)), 2); l[i], l[j] = l[j], l[i]
            yield f"statement {lst} two swapped", c
    c = copy.deepcopy(case); c["input"]["statement"]["shuffled_ciphertexts"] = copy.deepcopy(st["ciphertexts"])
    yield "statement C' := C", c

def structural(case):
    """(name, case, expected): expected is "reject", "accept" (the same values) or "either\""""
    p, q = dec(case["context"]["p"]), dec(case["context"]["q"])
    def edit(name, f, expect="reject"):
        c = copy.deepcopy(case); f(c); return (name, c, expect)
    arg = case["input"]["argument"]; prod = arg["product_argument"]
    vectors = [("context", "pk"), ("context", "ck", "g"), ("input", "argument", "ca"), ("input", "argument", "cb"),
               ("input", "argument", "product_argument", "single_vpa", "a_tilde"), ("input", "argument", "product_argument", "single_vpa", "b_tilde"),
               ("input", "argument", "multi_exp_argument", "c_b"), ("input", "argument", "multi_exp_argument", "a"),
               ("input", "argument", "multi_exp_argument", "e"), ("input", "argument", "multi_exp_argument", "e", 0, "phis"),
               ("input", "statement", "ciphertexts", 0, "phis"), ("input", "statement", "shuffled_ciphertexts", 0, "phis")]
    if "hadamard_argument" in prod:
        h = ("input", "argument", "product_argument", "hadamard_argument")
        vectors += [h + ("cUpperB",), h + ("zero_argument", "c_d"), h + ("zero_argument", "a"), h + ("zero_argument", "b")]
    out = []
    for v in vectors:
        out.append(edit(f"{field(v)} last dropped", lambda c, v=v: get(c, v).pop()))
        out.append(edit(f"{field(v)} last duplicated", lambda c, v=v: get(c, v).append(copy.deepcopy(get(c, v)[-1]))))
    if "hadamard_argument" in prod:
        P = ("input", "argument", "product_argument")
        out.append(edit("product argument without Hadamard argument and c_b", lambda c: (get(c, P).pop("hadamard_argument"), get(c, P).pop("c_b"))))
        out.append(edit("product argument without Hadamard argument", lambda c: get(c, P).pop("hadamard_argument")))
    st = ("input", "statement")
    out.append(edit("statement: one ciphertext appended to C and to C' (N not m*n)",
                    lambda c: (get(c, st)["ciphertexts"].append(copy.deepcopy(get(c, st)["ciphertexts"][0])),
                               get(c, st)["shuffled_ciphertexts"].append(copy.deepcopy(get(c, st)["shuffled_ciphertexts"][0])))))
    out.append(edit("statement: last ciphertext of C and C' dropped",
                    lambda c: (get(c, st)["ciphertexts"].pop(), get(c, st)["shuffled_ciphertexts"].pop())))
    # encodings and ranges, on one exponent and one group element
    sp = ("input", "argument", "product_argument", "single_vpa", "r_tilde")
    gp = ("input", "argument", "ca", 0)
    s, g = dec(get(case, sp)), dec(get(case, gp))
    raw = lambda b: base64.b64encode(b).decode()
    out.append(edit("exponent with an extra leading zero byte", lambda c: put(c, sp, raw(b"\0" + base64.b64decode(get(case, sp)))), "accept"))
    out.append(edit("group element with an extra leading zero byte", lambda c: put(c, gp, raw(b"\0" + base64.b64decode(get(case, gp)))), "accept"))
    # minimal unsigned bytes: when the top bit is set this reads as a negative two's-complement number
    ub = lambda v: raw(v.to_bytes((v.bit_length() + 7) // 8, "big"))
    out.append(edit("exponent as unsigned bytes (top bit %d)" % (s >> (8 * ((s.bit_length() + 7) // 8) - 1)), lambda c: put(c, sp, ub(s)), "either"))
    out.append(edit("group element as unsigned bytes (top bit %d)" % (g >> (8 * ((g.bit_length() + 7) // 8) - 1)), lambda c: put(c, gp, ub(g)), "either"))
    for name, v in [("q", q), ("exponent + q", s + q), ("-1", -1), ("exponent - q", s - q), ("2^3072 + exponent", (1 << 3072) + s)]:
        out.append(edit(f"exponent := {name}", lambda c, v=v: put(c, sp, enc(v))))
    for name, v in [("0", 0), ("p", p), ("element + p", g + p), ("p - 1 (not a square)", p - 1), ("-element", -g),
                    ("element - p", g - p), ("p - element (not a square)", p - g)]:
        out.append(edit(f"group element := {name}", lambda c, v=v: put(c, gp, enc(v))))
    out.append(edit("generator g := 4 in the context", lambda c: c["context"].__setitem__("g", enc(4)), "either"))
    out.append(edit("q := q + 2 in the context", lambda c: c["context"].__setitem__("q", enc(q + 2))))
    return out

# ---- the certified verifier, one process per case ----
def ours(cases, tag):
    d = os.path.join(work, tag); os.makedirs(d, exist_ok=True)
    def one(i):
        f = os.path.join(d, f"{i}.json"); json.dump([cases[i]], open(f, "w"))
        r = subprocess.run([verifier, "--diff", f], capture_output=True, text=True)
        line = [l.split("\t") for l in r.stdout.splitlines() if l and l[0].isdigit()]
        if line: return line[0][1], line[0][3]
        err = (r.stderr.strip().splitlines() or ["(no output)"])[-1]
        return "error: " + err.replace(f, "FILE"), None
    with concurrent.futures.ThreadPoolExecutor(os.cpu_count()) as ex:
        return list(ex.map(one, range(len(cases))))

def run(cases, tag, expect):
    """both verdicts of every case; expect(case) is "accept", "reject" or "either\""""
    f = os.path.join(work, tag + ".json")
    json.dump(cases, open(f, "w"))
    javas = bgdiff("verify", f)
    assert len(javas) == len(cases)
    for c, j in zip(cases, javas): c["output"]["result"] = j == "true"
    res = ours(cases, tag)
    tally, notes = collections.Counter(), []
    for c, j, (o, status) in zip(cases, javas, res):
        jv = "accept" if j == "true" else "reject"
        ov = "accept" if o == "true" else "reject"
        e = expect(c)
        agree = jv == ov and status != "CHALLENGE-MISMATCH"
        tally[(e, "swisspost " + ("exception" if j.startswith("error") else jv), "ours " + ("parse/exception" if o.startswith("error") else ov),
               "agree" if agree else "DISAGREE")] += 1
        if not agree or (e != "either" and (jv != e or ov != e)):
            notes.append(f"  {'agree' if agree else 'DISAGREE':8} expected {e:6} swisspost: {j[:100]}\n{'':17} ours: {o[:100]}\n{'':17} {c['description']}")
    with open(os.path.join(work, tag + ".tsv"), "w") as t:
        for c, j, (o, _) in zip(cases, javas, res): t.write(f"{expect(c)}\t{j[:150]}\t{o[:150]}\t{c['description']}\n")
    print(f"\n{tag}: {len(cases)} cases (verdicts in {tag}.tsv)")
    for k, n in sorted(tally.items()): print("  expected " + ", ".join(k) + f": {n}")
    for n in notes: print(n)
    return sum(n for k, n in tally.items() if k[3] != "agree")

disagreements = 0
honest = []
if "1" in stages or "3" in stages:
    honest_file = os.path.join(work, "honest.json")
    print("Swiss Post prover:", " ".join(java_shapes))
    bgdiff("gen", fixture, honest_file, *java_shapes)
    honest = json.load(open(honest_file))

if "1" in stages:
    cases = []
    for h in honest:
        cases.append(h)
        for name, c in mutants(h):
            c["description"] = h["description"].replace(", honest", "") + " | " + name
            del c["output"]["x"], c["output"]["y"], c["output"]["z"]
            cases.append(c)
    disagreements += run(cases, "stage1-fields", lambda c: "reject" if "|" in c["description"] else "accept")

if "2" in stages:
    f = os.path.join(work, "ocaml.json")
    print("\nextracted prover:", " ".join(ocaml_shapes))
    r = subprocess.run([verifier, "--gen", f, *ocaml_shapes], capture_output=True, text=True)
    if r.returncode != 0: sys.exit(r.stderr)
    disagreements += run(json.load(open(f)), "stage2-extracted-prover", lambda c: c["description"].rsplit("expect ", 1)[1])

if "3" in stages:
    cases, expects = [], {}
    for h in honest:
        if h["description"].split(", m=")[1].split(",")[0] in ("1", "2", "3"):   # m = 1 and m > 1
            for name, c, e in structural(h):
                c["description"] = h["description"].replace(", honest", "") + " | " + name
                for k in ("x", "y", "z"): c["output"].pop(k, None)
                expects[c["description"]] = e
                cases.append(c)
    disagreements += run(cases, "stage3-structure", lambda c: expects[c["description"]])

if "4" in stages:
    modes = ["COMPUTATION_OPTIMIZED", "MEMORY_OPTIMIZED"]
    Ns = [s.split(",")[0] for s in prod_shapes]
    dims = {mode: dict(zip(Ns, bgdiff("dims", mode, *Ns))) for mode in modes}
    print("\nproduction path (N: m,n per mode):", ", ".join(f"{N}: {dims[modes[0]][N]} / {dims[modes[1]][N]}" for N in dict.fromkeys(Ns)))
    cases = []
    for mode in modes:
        # MEMORY_OPTIMIZED only where it chooses other dimensions
        shapes = [s for s in prod_shapes if mode == modes[0] or dims[mode][s.split(",")[0]] != dims[modes[0]][s.split(",")[0]]]
        f = os.path.join(work, f"stage4-honest-{mode}.json")
        bgdiff("genprod", fixture, f, mode, *shapes)
        for h in json.load(open(f)):
            cases.append(h)
            fs = sorted(fields_of(h)) + ["statement"]
            ms = list(mutants(h, only=set(rng.sample(fs, min(prod_mutants, len(fs))))))
            for name, c in rng.sample(ms, min(prod_mutants, len(ms))):
                c["description"] = h["description"].replace(", honest", "") + " | " + name
                del c["output"]["x"], c["output"]["y"], c["output"]["z"]
                cases.append(c)
            del ms
    disagreements += run(cases, "stage4-production", lambda c: "reject" if "|" in c["description"] else "accept")
    # the production verifier, which derives the commitment key itself
    prod = bgdiff("verifyprod", os.path.join(work, "stage4-production.json"))
    diff = [(c["description"], c["output"]["result"], v) for c, v in zip(cases, prod)
            if "| context/ck" not in c["description"] and (v == "true") != c["output"]["result"]]
    print(f"  MixnetService.verifyShuffle vs ShuffleArgumentService: {len(diff)} differences"
          f" ({sum(1 for c in cases if '| context/ck' in c['description'])} commitment-key mutants not compared)")
    for d, a, b in diff: print(f"    {d}: ShuffleArgumentService {a}, MixnetService {b}")
    disagreements += len(diff)

print(f"\n{disagreements} disagreements")
sys.exit(1 if disagreements else 0)
