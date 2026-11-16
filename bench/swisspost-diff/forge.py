#!/usr/bin/env python3
"""Single-check forgeries of the sub-arguments of the Bayer–Groth shuffle
argument (Swiss Post crypto-primitives specification 1.6.0, Section 9).

Most checks of the verifiers compare a response with the commitments
(responses are not hashed, so a changed response breaks only its own
equation: stage 1 of swisspost_diff.py covers them). The others compare a
hashed value with a constant or with the statement; changing such a value
changes the Fiat–Shamir challenge and breaks every equation at once. For each
of them this script runs the prover of the specification on a false
statement, arranged so that every equation holds and only that check fails;
a verifier that omitted the check would accept a false statement:

  zero argument (9.23)          c_d[m+1] = 1             the statement sum is d != 0
  single value product (9.26)   b~_0 = a~_0              the chain starts at a_0 + e
                                b~_{n-1} = x b           the statement product is b + e
  Hadamard argument (9.21)      c_B0 = c_A0              the chain starts at a_0 + e
                                c_B{m-1} = c_b           c_b commits to b + e
  multi-exponentiation (9.16)   E_m = C                  C is multiplied by Enc(g^e; s)
                                c_B[m] = 1               the same, absorbed by b_m = e

Each forgery comes with its control, the same construction with e = 0,
which is a true statement that both verifiers must accept: so the only check
that can reject the forgery is the one it targets. The hash is checked
against the challenges recorded in the Swiss Post test vectors first.

usage: forge.py BUILD_DIR WORK_DIR [M,N,L ...]"""
import base64, concurrent.futures, hashlib, json, os, random, subprocess, sys

build, work = sys.argv[1], sys.argv[2]
shapes = [tuple(map(int, s.split(","))) for s in sys.argv[3:]] or [(1, 2, 1), (2, 2, 1), (2, 3, 2), (3, 4, 2), (4, 3, 1)]
root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
data = os.path.join(root, "src/Executable/Bgverifier/data")
verifier = os.path.join(root, "_build/default/src/Executable/Bgverifier/main.exe")
java = os.path.join(os.environ["JAVA_HOME"], "bin", "java") if "JAVA_HOME" in os.environ else "java"
rng = random.Random(int(os.environ.get("SEED", "1")))
os.makedirs(work, exist_ok=True)

def dec(s): return int.from_bytes(base64.b64decode(s), "big", signed=True)
def enc(v): return base64.b64encode(v.to_bytes(v.bit_length() // 8 + 1, "big", signed=True)).decode()

fx = json.load(open(os.path.join(data, "verify-zero-argument.json")))[0]["context"]
p, q, G = dec(fx["p"]), dec(fx["q"]), 2

# ---- RecursiveHash (Algorithm 5.5) and the challenges ----
def sha3(b): return hashlib.sha3_256(b).digest()
def ibytes(z): return b"" if z == 0 else z.to_bytes((z.bit_length() + 7) // 8, "big")
def rh(v):
    t, x = v
    if t == "I": return sha3(b"\x01" + ibytes(x))
    if t == "S": return sha3(b"\x02" + x.encode())
    return sha3(b"\x03" + b"".join(rh(e) for e in x))
I = lambda z: ("I", z)
L = lambda xs: ("L", list(xs))
def hl(xs): return L(I(x) for x in xs)
def hct(c): return hl(c)                       # a ciphertext is (gamma, phi_1, ..., phi_l)
def hcl(cs): return L(hct(c) for c in cs)
def chal(vs): return int.from_bytes(rh(L(vs)), "big")

class Ctx:
    def __init__(self, n, l):
        self.pk = [pow(G, rng.randrange(1, q), p) for _ in range(l)]
        self.h = pow(G, rng.randrange(1, q), p)
        self.gs = [pow(G, rng.randrange(1, q), p) for _ in range(n)]
    @staticmethod
    def of_json(c):
        x = Ctx.__new__(Ctx); x.pk = [dec(v) for v in c["pk"]]; x.h = dec(c["ck"]["h"]); x.gs = [dec(v) for v in c["ck"]["g"]]; return x
    def base(self): return [I(p), I(q), hl(self.pk), L([I(self.h)] + [I(g) for g in self.gs])]
    def com(self, a, r):                         # Algorithm 9.7
        c = pow(self.h, r, p)
        for gi, ai in zip(self.gs, a): c = c * pow(gi, ai % q, p) % p
        return c
    def json(self):
        return {"p": enc(p), "q": enc(q), "g": enc(G), "pk": [enc(v) for v in self.pk], "ck": {"h": enc(self.h), "g": [enc(v) for v in self.gs]}}
    # ElGamal multi-recipient: GetCiphertext(msgs, r, pk) = (g^r, pk_i^r m_i)
    def ct(self, msgs, r): return [pow(G, r, p)] + [pow(k, r, p) * m % p for k, m in zip(self.pk, msgs)]

def ctmul(a, b): return [x * y % p for x, y in zip(a, b)]
def ctexp(a, e): return [pow(x, e % q, p) for x in a]
def ctvexp(cs, es):                              # Algorithm 8.8: prod_j C_j^{e_j}
    acc = [1] * len(cs[0])
    for c, e in zip(cs, es): acc = ctmul(acc, ctexp(c, e))
    return acc
def rv(k): return [rng.randrange(q) for _ in range(k)]
def star(y, a, b): return sum(ai * bi * pow(y, j + 1, q) for j, (ai, bi) in enumerate(zip(a, b))) % q   # 9.10
def vadd(a, b): return [(x + y) % q for x, y in zip(a, b)]
def vscale(e, a): return [e * x % q for x in a]
def had(a, b): return [x * y % q for x, y in zip(a, b)]

# ---- the challenges, as the verifiers compute them ----
def x_zero(c, cA0, cBm, cd, cB, cA): return chal(c.base() + [I(cA0), I(cBm), hl(cd), hl(cB), hl(cA)])
def x_svp(c, cDelta, cdelta, cd, b, ca): return chal(c.base() + [I(cDelta), I(cdelta), I(cd), I(b), I(ca)])
def xy_had(c, cA, cb, cB):
    v = [hl(cA), I(cb), hl(cB)]
    return chal(c.base() + v), chal([("S", "1")] + c.base() + v)
def x_mexp(c, rows, C, cA, cA0, cB, E): return chal(c.base() + [L(hcl(r) for r in rows), hct(C), hl(cA), I(cA0), hl(cB), hcl(E)])

def selftest():
    for t in json.load(open(os.path.join(data, "verify-zero-argument.json"))):
        c, st, a = Ctx.of_json(t["context"]), t["input"]["statement"], t["input"]["argument"]
        D = lambda v: [dec(x) for x in v]
        assert x_zero(c, dec(a["c_a0"]), dec(a["c_bm"]), D(a["c_d"]), D(st["c_b"]), D(st["c_a"])) == dec(t["output"]["x"]), "zero x"
    for t in json.load(open(os.path.join(data, "verify-single-value-product-argument.json"))):
        c, st, a = Ctx.of_json(t["context"]), t["input"]["statement"], t["input"]["argument"]
        assert x_svp(c, dec(a["c_upper_delta"]), dec(a["c_lower_delta"]), dec(a["c_d"]), dec(st["b"]), dec(st["c_a"])) == dec(t["output"]["x"]), "svp x"
    for t in json.load(open(os.path.join(data, "verify-hadamard-argument.json"))):
        c, st, a = Ctx.of_json(t["context"]), t["input"]["statement"], t["input"]["argument"]
        x, y = xy_had(c, [dec(v) for v in st["c_a"]], dec(st["c_b"]), [dec(v) for v in a["cUpperB"]])
        assert (x, y) == (dec(t["output"]["x"]), dec(t["output"]["y"])), "hadamard x, y"
    for t in json.load(open(os.path.join(data, "verify-multiexp-argument.json"))):
        c, st, a = Ctx.of_json(t["context"]), t["input"]["statement"], t["input"]["argument"]
        CT = lambda j: [dec(j["gamma"])] + [dec(v) for v in j["phis"]]
        x = x_mexp(c, [[CT(j) for j in row] for row in st["ciphertexts"]], CT(st["ciphertext_product"]), [dec(v) for v in st["c_a"]],
                   dec(a["c_a_0"]), [dec(v) for v in a["c_b"]], [CT(j) for j in a["e"]])
        assert x == dec(t["output"]["x"]), "multiexp x"
    print("RecursiveHash: the challenges of the Swiss Post test vectors are reproduced")

# ---- provers of the specification, with the deviations of the forgeries ----
def zero_prove(c, cA, cB, y, A, B, r, s):
    """Algorithm 9.22: A = (a_1..a_m), B = (b_0..b_{m-1}) columns"""
    m, n = len(A), len(A[0])
    a0, bm, r0, sm = rv(n), rv(n), rng.randrange(q), rng.randrange(q)
    cA0, cBm = c.com(a0, r0), c.com(bm, sm)
    AA, BB = [a0] + A, B + [bm]
    d = []
    for k in range(2 * m + 1):                   # Algorithm 9.24
        dk = 0
        for i in range(max(0, k - m), m + 1):
            j = (m - k) + i
            if j > m: break
            dk = (dk + star(y, AA[i], BB[j])) % q
        d.append(dk)
    t = rv(2 * m + 1); t[m + 1] = 0
    cd = [c.com([dk], tk) for dk, tk in zip(d, t)]
    x = x_zero(c, cA0, cBm, cd, cB, cA)
    a_ = [sum(pow(x, i, q) * AA[i][j] for i in range(m + 1)) % q for j in range(n)]
    b_ = [sum(pow(x, m - i, q) * BB[i][j] for i in range(m + 1)) % q for j in range(n)]
    r_ = (r0 + sum(pow(x, i, q) * r[i - 1] for i in range(1, m + 1))) % q
    s_ = (sum(pow(x, m - i, q) * s[i] for i in range(m)) + sm) % q
    t_ = sum(pow(x, i, q) * t[i] for i in range(2 * m + 1)) % q
    return {"c_a0": enc(cA0), "c_bm": enc(cBm), "c_d": [enc(v) for v in cd], "a": [enc(v) for v in a_], "b": [enc(v) for v in b_],
            "r": enc(r_), "s": enc(s_), "t": enc(t_)}

def svp_prove(c, ca, b_stmt, a, r, e0=0):
    """Algorithm 9.25; e0 != 0: the chain starts at b_0 = a_0 + e0"""
    n = len(a)
    bk = [(a[0] + e0) % q]
    for k in range(1, n): bk.append(bk[-1] * a[k] % q)
    d, rd = rv(n), rng.randrange(q)
    delta = [d[0]] + rv(n - 2) + [0]
    s0, sx = rng.randrange(q), rng.randrange(q)
    dprime = [(-delta[k] * d[k + 1]) % q for k in range(n - 1)]
    Delta = [(delta[k + 1] - a[k + 1] * delta[k] - bk[k] * d[k + 1]) % q for k in range(n - 1)]
    cd, cdelta, cDelta = c.com(d, rd), c.com(dprime, s0), c.com(Delta, sx)
    x = x_svp(c, cDelta, cdelta, cd, b_stmt, ca)
    return {"c_d": enc(cd), "c_lower_delta": enc(cdelta), "c_upper_delta": enc(cDelta),
            "a_tilde": [enc((x * a[k] + d[k]) % q) for k in range(n)], "b_tilde": [enc((x * bk[k] + delta[k]) % q) for k in range(n)],
            "r_tilde": enc((x * r + rd) % q), "s_tilde": enc((x * sx + s0) % q)}

def had_prove(c, cA, cb, A, r, s, e0=0, honest_last=False):
    """Algorithm 9.20; e0 != 0: the chain starts at b_0 = a_0 + e0 (c_B0 = com(b_0; r_0));
    honest_last: c_B{m-1} commits to the true chain, not to the statement's c_b"""
    m, n = len(A), len(A[0])
    B = [[(x + e0) % q for x in A[0]]]
    for j in range(1, m): B.append(had(B[-1], A[j]))
    S = [r[0]] + rv(m - 2) + [s]
    cB = [c.com(B[0], S[0]) if e0 else cA[0]] + [c.com(B[j], S[j]) for j in range(1, m - 1)] + [c.com(B[m - 1], S[m - 1]) if honest_last else cb]
    x, y = xy_had(c, cA, cb, cB)
    dvec = [vscale(pow(x, i + 1, q), B[i]) for i in range(m - 1)]
    cD = [pow(cB[i], pow(x, i + 1, q), p) for i in range(m - 1)]
    t_ = [pow(x, i + 1, q) * S[i] % q for i in range(m - 1)]
    dsum = [sum(pow(x, i, q) * B[i][j] for i in range(1, m)) % q for j in range(n)]
    cDs = 1
    for i in range(1, m): cDs = cDs * pow(cB[i], pow(x, i, q), p) % p
    tsum = sum(pow(x, i, q) * S[i] for i in range(1, m)) % q
    minus1 = [q - 1] * n
    cm1 = c.com(minus1, 0)
    zst_a, zst_b = cA[1:] + [cm1], cD + [cDs]
    z = zero_prove(c, zst_a, zst_b, y, A[1:] + [minus1], dvec + [dsum], r[1:] + [0], t_ + [tsum])
    return {"cUpperB": [enc(v) for v in cB], "zero_argument": z}

def mexp_prove(c, rows, C, cA, A, r, rho, bm=0, taum=None):
    """Algorithm 9.15: rows C_0..C_{m-1} (n ciphertexts each), A = (a_1..a_m) columns;
    bm, taum: the values of b_m and tau_m (0 and rho in the specification)"""
    m, n = len(A), len(A[0])
    a0, r0 = rv(n), rng.randrange(q)
    b, s, tau = rv(2 * m), rv(2 * m), rv(2 * m)
    b[m], s[m], tau[m] = bm, (rng.randrange(q) if bm else 0), (rho if taum is None else taum)
    cA0 = c.com(a0, r0)
    AA = [a0] + A
    D = []
    for k in range(2 * m):                        # Algorithm 9.17
        dk = [1] * len(C)
        lb, ub = (m - k - 1, m) if k < m else (0, 2 * m - k)
        for i in range(lb, ub): dk = ctmul(dk, ctvexp(rows[i], AA[k - m + i + 1]))
        D.append(dk)
    l = len(C) - 1
    cB = [c.com([b[k]], s[k]) for k in range(2 * m)]
    E = [ctmul(c.ct([pow(G, b[k], p)] * l, tau[k]), D[k]) for k in range(2 * m)]
    x = x_mexp(c, rows, C, cA, cA0, cB, E)
    a = [(a0[j] + sum(pow(x, i, q) * A[i - 1][j] for i in range(1, m + 1))) % q for j in range(n)]
    rr = (r0 + sum(pow(x, i, q) * r[i - 1] for i in range(1, m + 1))) % q
    bb = (b[0] + sum(pow(x, k, q) * b[k] for k in range(1, 2 * m))) % q
    ss = (s[0] + sum(pow(x, k, q) * s[k] for k in range(1, 2 * m))) % q
    tt = (tau[0] + sum(pow(x, k, q) * tau[k] for k in range(1, 2 * m))) % q
    jct = lambda v: {"gamma": enc(v[0]), "phis": [enc(w) for w in v[1:]]}
    return {"c_a_0": enc(cA0), "c_b": [enc(v) for v in cB], "a": [enc(v) for v in a], "e": [jct(v) for v in E],
            "r": enc(rr), "b": enc(bb), "s": enc(ss), "tau": enc(tt)}, jct

# ---- the cases ----
def case(desc, ctx, st, arg): return {"description": desc, "context": ctx.json(), "input": {"statement": st, "argument": arg}, "output": {"result": True}}

def zero_cases(m, n, l):
    out = []
    for e in (0, rng.randrange(1, q)):
        c = Ctx(n, l)
        A, B, y = [rv(n) for _ in range(m)], [rv(n) for _ in range(m)], rng.randrange(1, q)
        # the statement sum_{i=1}^m a_i * b_{i-1} = e: the first entry of a_m fixes it
        rest = (sum(star(y, A[i], B[i]) for i in range(m)) - A[m - 1][0] * B[m - 1][0] * y) % q
        A[m - 1][0] = (e - rest) * pow(B[m - 1][0] * y % q, -1, q) % q
        assert sum(star(y, A[i], B[i]) for i in range(m)) % q == e
        r, s = rv(m), rv(m)
        cA, cB = [c.com(A[i], r[i]) for i in range(m)], [c.com(B[i], s[i]) for i in range(m)]
        arg = zero_prove(c, cA, cB, y, A, B, r, s)
        out.append(("zero", case(f"zero m={m} n={n}: c_d[m+1] = 1 | " + ("control" if e == 0 else "forgery"), c,
                                  {"c_a": [enc(v) for v in cA], "c_b": [enc(v) for v in cB], "y": enc(y)}, arg)))
    return out

def svp_cases(n, l):
    out = []
    for check in ("b~_0 = a~_0", "b~_{n-1} = x b"):
        for e in (0, rng.randrange(1, q)):
            c = Ctx(n, l)
            a, r = rv(n), rng.randrange(q)
            ca = c.com(a, r)
            prod = 1
            for v in a: prod = prod * v % q
            if check == "b~_0 = a~_0":
                b = (a[0] + e) * prod * pow(a[0], -1, q) % q
                arg = svp_prove(c, ca, b, a, r, e0=e)
            else:
                b = (prod + e) % q
                arg = svp_prove(c, ca, b, a, r)
            out.append(("svp", case(f"svp n={n}: {check} | " + ("control" if e == 0 else "forgery"), c, {"c_a": enc(ca), "b": enc(b)}, arg)))
    return out

def had_cases(m, n, l):
    out = []
    for check in ("c_B0 = c_A0", "c_B{m-1} = c_b"):
        for e in (0, rng.randrange(1, q)):
            c = Ctx(n, l)
            A, r, s = [rv(n) for _ in range(m)], rv(m), rng.randrange(q)
            cA = [c.com(A[j], r[j]) for j in range(m)]
            B = [(x + (e if check == "c_B0 = c_A0" else 0)) % q for x in A[0]]
            for j in range(1, m): B = had(B, A[j])
            if check == "c_B0 = c_A0":
                cb = c.com(B, s)
                arg = had_prove(c, cA, cb, A, r, s, e0=e)
            else:
                cb = c.com([(x + e) % q for x in B], s)
                arg = had_prove(c, cA, cb, A, r, s, honest_last=True)
            out.append(("hadamard", case(f"hadamard m={m} n={n}: {check} | " + ("control" if e == 0 else "forgery"), c,
                                         {"c_a": [enc(v) for v in cA], "c_b": enc(cb)}, arg)))
    return out

def mexp_cases(m, n, l):
    out = []
    for check in ("E_m = C", "c_B[m] = 1"):
        for e in (0, rng.randrange(1, q)):
            c = Ctx(n, l)
            rows = [[c.ct([pow(G, rng.randrange(q), p) for _ in range(l)], rng.randrange(q)) for _ in range(n)] for _ in range(m)]
            A, r, rho = [rv(n) for _ in range(m)], rv(m), rng.randrange(q)
            cA = [c.com(A[j], r[j]) for j in range(m)]
            C = c.ct([1] * l, rho)
            for i in range(m): C = ctmul(C, ctvexp(rows[i], A[i]))
            sigma = rng.randrange(q)
            Cf = ctmul(C, c.ct([pow(G, e, p)] * l, sigma)) if e else C      # the false statement
            if check == "E_m = C" or e == 0:
                arg, jct = mexp_prove(c, rows, Cf, cA, A, r, rho)
            else:
                arg, jct = mexp_prove(c, rows, Cf, cA, A, r, rho, bm=e, taum=(rho + sigma) % q)
            out.append(("multiexp", case(f"multiexp m={m} n={n} l={l}: {check} | " + ("control" if e == 0 else "forgery"), c,
                                         {"ciphertexts": [[jct(v) for v in row] for row in rows], "ciphertext_product": jct(Cf),
                                          "c_a": [enc(v) for v in cA]}, arg)))
    return out

# ---- run ----
def run(kind, cases):
    f = os.path.join(work, f"forge-{kind}.json"); json.dump(cases, open(f, "w"))
    j = subprocess.run([java, "--module-path", f"{build}/classes:{build}/mods", "-m",
                        "ch.post.it.evoting.cryptoprimitives/ch.post.it.evoting.cryptoprimitives.internal.mixnet.SubDiff", kind, f],
                       capture_output=True, text=True).stdout.splitlines()
    o = subprocess.run([verifier, "--diff-sub", kind, f], capture_output=True, text=True)
    ours = [l.split("\t")[1] for l in o.stdout.splitlines() if l and l[0].isdigit()]
    if len(ours) != len(cases) or len(j) != len(cases): sys.exit(f"{kind}: {o.stderr[-1000:]}")
    return [(c["description"], jv, ov) for c, jv, ov in zip(cases, j, ours)]

selftest()
by_kind = {}
for (m, n, l) in shapes:
    for k, c in zero_cases(m, n, l) + svp_cases(n, l) + (had_cases(m, n, l) if m >= 2 else []) + mexp_cases(m, n, l):
        by_kind.setdefault(k, []).append(c)
with concurrent.futures.ThreadPoolExecutor(5) as ex:
    results = [r for rs in ex.map(lambda kv: run(*kv), by_kind.items()) for r in rs]
bad = 0
for desc, jv, ov in results:
    want = "true" if desc.endswith("control") else "false"
    ok = jv.split("\t")[0] == want and ov == want
    bad += not ok
    print(f"{'ok ' if ok else 'BAD'}  swisspost={jv[:90]:40}  ours={ov:5}  {desc}")
print(f"{len(results)} cases, {bad} unexpected")
sys.exit(1 if bad else 0)
