"""The mix-net of Belenios 3.2.0 (src/lib/v1/mixnet.ml of the pinned
release; Haenni, Locher, Koenig, Dubuis, "Pseudo-code algorithms for
verifiable re-encryption mix-nets", the formulation of the Terelius-Wikström
proof of a shuffle that Belenios follows), at Ed25519, for differential
testing: the independent generators, the shuffle, the proof of a shuffle and
its verification, with seeded randomness and hooks that change one input of
the Fiat-Shamir hashes or one step of the prover.

Points are handled in extended coordinates (belenios_lib); the verifier
computes every exponentiation with the exact integer exponent (mul_raw), as
Belenios does: libsodium refuses a point outside the order-l subgroup and
Belenios then falls back to its pure implementation, which exponentiates on
the whole curve, so this verifier agrees with Belenios on every point of the
curve, not only on the subgroup."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "belenios-diff"))
from belenios_lib import *

# ---- the group, as Belenios's Ed25519_pure computes it ----

def uncompress_raw(z):
    """Ed25519_pure.uncompress: y = z mod 2^255 (reduced mod p), the sign of x from bit 255"""
    y = (z & ((1 << 255) - 1)) % P
    y2 = y * y % P; x2 = (y2 - 1) * pow(D * y2 + 1, P - 2, P) % P
    x = pow(x2, (P + 3) // 8, P)
    if (x * x - x2) % P: x = x * SQRT_M1 % P
    if (x * x - x2) % P: return None
    if (x & 1) != (z >> 255): x = (-x) % P
    return ext(x, y)

GEN_CACHE = {}
def get_generator(i):
    """Ed25519_pure.get_generator: the point of "ggen|i" times the cofactor 8"""
    if i not in GEN_CACHE:
        z = int(sha256_hex(("ggen|%d" % i).encode()), 16) >> 2
        while True:
            p1 = uncompress_raw(z)
            if p1 is not None: break
            z += 1
        GEN_CACHE[i] = mul_raw(8, p1)
    return GEN_CACHE[i]

def is_subgroup(p1):
    return eq(mul_raw(L, p1), ZERO)

# the torsion points used by the forgeries: the point of order 2 and one of order 8
T2 = ext(0, P - 1)
def _t8():
    for y in range(2, 1000):
        p1 = uncompress_raw(y)
        if p1 is None: continue
        t = mul_raw(L, p1)          # the torsion component of a random point
        if not eq(mul_raw(4, t), ZERO): return t
T8 = _t8()

def zq_hex(h): return int(h, 16) % L

# ---- the hashes (mixnet.ml) ----

def str_egs(e):  return "".join("%s,%s," % (tostr(a), tostr(b)) for a, b in e)
def str_elts(c): return "".join("%s," % tostr(x) for x in c)

def nizkp_challenges(n, s):
    h = sha256_hex(s.encode())
    return [zq_hex(sha256_hex((h + sha256_hex(str(i).encode())).encode())) for i in range(n)]

def nizkp_challenge(s): return zq_hex(sha256_hex(s.encode()))

class Hooks(dict):
    """changes to the prover: each key names one step (see gen_shuffle_proof)"""
    def get(self, k, d=None): return dict.get(self, k, d)

# ---- the shuffle and its proof ----

def reenc(y, c, r): return (add(c[0], gpow(r)), add(c[1], mul(r, y)))

def gen_shuffle(rng, y, ee):
    n = len(ee)
    tmp = list(range(n)); psi = [0] * n
    for i in range(n):
        k = rng.randrange(n - i) + i
        psi[i] = tmp[k]; tmp[k] = tmp[i]
    rr = [rng.randrange(L) for _ in range(n)]
    re = [reenc(y, c, r) for c, r in zip(ee, rr)]
    return [re[psi[i]] for i in range(n)], rr, psi

def gen_shuffle_proof(rng, fp, y, ee, ee2, rr2, psi, hooks=None):
    """the proof (t, s, cc, cc_hat) of mixnet.ml's gen_shuffle_proof for the input ee,
    the output ee2 = permuted re-encryption of ee with exponents rr2 (indexed by the input)"""
    hk = hooks or Hooks()
    rand = lambda: rng.randrange(L)
    n = len(ee)
    h = hk.get("h", get_generator(-1))
    hh = [get_generator(i) for i in range(n)]
    cc, rr = [None] * n, [0] * n
    for i in range(n):
        r_ = rand(); rr[psi[i]] = r_; cc[psi[i]] = add(gpow(r_), hh[i])
    str1 = str_egs(ee) + str_egs(ee2) + str_elts(cc)
    s_uu = hk.get("uu_input", lambda fp, str1: "shuffle-challenges|" + fp + "|" + str1)(fp, str1)
    uu = nizkp_challenges(n, s_uu)
    uu2 = [uu[psi[i]] for i in range(n)]
    cc_hat, rr_hat = [None] * n, [rand() for _ in range(n)]
    for i in range(n):
        prev = h if i == 0 else cc_hat[i - 1]
        cc_hat[i] = add(gpow(rr_hat[i]), mul(uu2[i], prev))
    w1, w2, w3, w4 = rand(), rand(), rand(), rand()
    ww_hat = [rand() for _ in range(n)]; ww2 = [rand() for _ in range(n)]
    t1, t2 = gpow(w1), gpow(w2)
    t3 = gpow(w3)
    for x, w in zip(hh, ww2): t3 = add(t3, mul(w, x))
    t41, t42 = neg(mul(w4, y)), neg(gpow(w4))
    for (a, b), w in zip(ee2, ww2): t41 = add(t41, mul_raw(w, b)); t42 = add(t42, mul_raw(w, a))
    tt_hat = [add(gpow(ww_hat[i]), mul(ww2[i], h if i == 0 else cc_hat[i - 1])) for i in range(n)]
    str2 = str_elts([t1, t2, t3, t41, t42]) + str_elts(tt_hat)
    str3 = str1 + str_elts(cc_hat) + tostr(hk.get("y_hash", y))
    s_c = hk.get("c_input", lambda fp, str2, str3: "shuffle-challenge|" + fp + "|" + str2 + str3)(fp, str2, str3)
    c = nizkp_challenge(s_c)
    r_bar = sum(rr) % L
    s1 = (w1 + c * r_bar) % L
    vv = [1] * n
    for i in range(n - 2, -1, -1): vv[i] = uu2[i + 1] * vv[i + 1] % L
    r_hat = sum(a * b for a, b in zip(rr_hat, vv)) % L
    s2 = (w2 + c * r_hat) % L
    r_tilde = sum(a * b for a, b in zip(rr, uu)) % L
    s3 = (w3 + c * r_tilde) % L
    r2 = sum(a * b for a, b in zip(rr2, uu)) % L
    s4 = (w4 + c * r2) % L
    ss_hat = [(ww_hat[i] + c * rr_hat[i]) % L for i in range(n)]
    ss2 = [(ww2[i] + c * uu2[i]) % L for i in range(n)]
    return ((t1, t2, t3, (t41, t42), tt_hat), (s1, s2, s3, s4, ss_hat, ss2), cc, cc_hat)

def check_shuffle_proof(fp, y, ee, ee2, proof):
    """mixnet.ml's check_shuffle_proof, with exact exponentiation on the whole curve
    (the G.check of the proof's points is the caller's: see check_points)"""
    n = len(ee)
    if n != len(ee2): return False
    (t1, t2, t3, (t41, t42), tt_hat), (s1, s2, s3, s4, ss_hat, ss2), cc, cc_hat = proof
    if not all(len(x) == n for x in (cc, cc_hat, tt_hat, ss_hat, ss2)): return False
    h = get_generator(-1); hh = [get_generator(i) for i in range(n)]
    str1 = str_egs(ee) + str_egs(ee2) + str_elts(cc)
    uu = nizkp_challenges(n, "shuffle-challenges|" + fp + "|" + str1)
    str2 = str_elts([t1, t2, t3, t41, t42]) + str_elts(tt_hat)
    str3 = str1 + str_elts(cc_hat) + tostr(y)
    c = nizkp_challenge("shuffle-challenge|" + fp + "|" + str2 + str3)
    def prod(xs):
        r = ZERO
        for x in xs: r = add(r, x)
        return r
    c_bar = sub(prod(cc), prod(hh))
    u = 1
    for x in uu: u = u * x % L
    c_hat = sub(h if n == 0 else cc_hat[n - 1], mul_raw(u, h))
    c_tilde = prod(mul_raw(u_, x) for x, u_ in zip(cc, uu))
    alpha_ = prod(mul_raw(u_, a) for (a, _), u_ in zip(ee, uu))
    beta_ = prod(mul_raw(u_, b) for (_, b), u_ in zip(ee, uu))
    t1_ = sub(mul_raw(s1, G), mul_raw(c, c_bar))
    t2_ = sub(mul_raw(s2, G), mul_raw(c, c_hat))
    t3_ = sub(add(mul_raw(s3, G), prod(mul_raw(s, x) for x, s in zip(hh, ss2))), mul_raw(c, c_tilde))
    t41_ = sub(prod(mul_raw(s, b) for (_, b), s in zip(ee2, ss2)), add(mul_raw(c, beta_), mul_raw(s4, y)))
    t42_ = sub(prod(mul_raw(s, a) for (a, _), s in zip(ee2, ss2)), add(mul_raw(c, alpha_), mul_raw(s4, G)))
    ok = eq(t1, t1_) and eq(t2, t2_) and eq(t3, t3_) and eq(t41, t41_) and eq(t42, t42_)
    for i in range(n):
        x = h if i == 0 else cc_hat[i - 1]
        ok = ok and eq(tt_hat[i], sub(add(mul_raw(ss_hat[i], G), mul_raw(ss2[i], x)), mul_raw(c, cc_hat[i])))
    return ok

# ---- JSON (serializable.atd: shuffle, shuffle_proof) ----

def ct_json(c): return {"alpha": tostr(c[0]), "beta": tostr(c[1])}
def ct_of_json(j): return (ofstr(j["alpha"], check=False), ofstr(j["beta"], check=False))

def proof_json(pf):
    (t1, t2, t3, (t41, t42), tt_hat), (s1, s2, s3, s4, ss_hat, ss2), cc, cc_hat = pf
    return [[tostr(t1), tostr(t2), tostr(t3), [tostr(t41), tostr(t42)], [tostr(x) for x in tt_hat]],
            [str(s1), str(s2), str(s3), str(s4), [str(x) for x in ss_hat], [str(x) for x in ss2]],
            [tostr(x) for x in cc], [tostr(x) for x in cc_hat]]

def proof_of_json(j):
    pt = lambda s: ofstr(s, check=False)
    (t1, t2, t3, (t41, t42), tt_hat), (s1, s2, s3, s4, ss_hat, ss2), cc, cc_hat = j
    return ((pt(t1), pt(t2), pt(t3), (pt(t41), pt(t42)), [pt(x) for x in tt_hat]),
            (int(s1), int(s2), int(s3), int(s4), [int(x) for x in ss_hat], [int(x) for x in ss2]),
            [pt(x) for x in cc], [pt(x) for x in cc_hat])

def shuffle_json(cts, proofs):
    return {"ciphertexts": [[ct_json(c) for c in q] for q in cts], "proofs": [proof_json(p) for p in proofs]}

# ---- the archive's shuffle phase ----

def with_shuffles(arch, shuffles, end=True, tail=()):
    """a copy of arch whose events after EncryptedTally are one Shuffle event per
    (owner, document bytes) of shuffles, then EndShuffles (if end), then the events
    of tail (dicts with type and, optionally, payload bytes)"""
    a = arch.copy()
    evs = a.event_list()
    k = [i for i, e in enumerate(evs) if e["type"] == "EncryptedTally"][0]
    evs = evs[:k + 1]
    for owner, doc in shuffles:
        h = a.add_data(doc)
        evs.append({"type": "Shuffle", "payload": a.add_data(compact({"owner": owner, "payload": h}))})
    if end: evs.append({"type": "EndShuffles"})
    for t in tail:
        e = {"type": t["type"]}
        if "payload" in t: e["payload"] = a.add_data(t["payload"])
        evs.append(e)
    for i, e in enumerate(evs): e["height"] = i
    a.set_events(evs)
    return a

def nh_input(arch, el):
    """the NH ciphertexts of the published encrypted tally, one list per NH question"""
    tally = arch.doc(arch.doc(arch.payloads("EncryptedTally")[0])["encrypted_tally"])
    return [[ct_of_json(c) for c in tally[i]] for i, q in enumerate(el.questions) if is_nh(q)]

def shuffle_docs(arch):
    """the (owner, shuffle document) of the Shuffle events, in order"""
    return [(arch.doc(h)["owner"], arch.doc(arch.doc(h)["payload"])) for h in arch.payloads("Shuffle")]

# ---- NH questions and the decoding of a plaintext (Ed25519_pure.of_ints / to_ints) ----

def is_nh(q): return q.get("type") == "NonHomomorphic"

def to_ints(n, p1, padding=14, bits=8):
    x, y = affine(p1); z = y | ((x & 1) << 255)
    z >>= padding; out = [0] * n
    for i in range(n - 1, -1, -1): out[i] = z & ((1 << bits) - 1); z >>= bits
    return out
