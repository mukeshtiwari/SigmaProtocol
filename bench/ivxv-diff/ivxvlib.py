"""Shared code of the IVXV campaign (our code, written from the Verificatum
3.1.0 verifier manual and from the IVXV sources; no IVXV code is copied).

- Verificatum byte trees, sessions (protocol info, ρ, the independent
  generators, the random oracles) and an independent prover for the
  Terelius--Wikström proof of a shuffle at key width κ, used to write
  honest controls and Fiat--Shamir-consistent proofs of false statements
  into a session;
- IVXV's decryption-proof encodings (DER) and challenge (DPRNG seeded with
  the DER sequence, IntegerConstructor), and a prover for them."""
import functools, hashlib, os, re, struct

# ---------------------------------------------------------------- byte trees
def bt_dec(b, pos=0):
    tag, n = b[pos], struct.unpack(">I", b[pos + 1:pos + 5])[0]; pos += 5
    if tag == 1: return ("L", bytes(b[pos:pos + n])), pos + n
    cs = []
    for _ in range(n):
        c, pos = bt_dec(b, pos); cs.append(c)
    return ("N", cs), pos
def bt_enc(t):
    if t[0] == "L": return b"\x01" + struct.pack(">I", len(t[1])) + t[1]
    return b"\x00" + struct.pack(">I", len(t[1])) + b"".join(bt_enc(c) for c in t[1])
def bt_load(path): return bt_dec(open(path, "rb").read())[0]
def bt_save(path, t): open(path, "wb").write(bt_enc(t))
def ival(t): return int.from_bytes(t[1], "big", signed=True)
def leaf(k, x): return ("L", x.to_bytes(k, "big", signed=True))
def width_of(m):
    k = 1
    while m >= 1 << (8 * k - 1): k += 1
    return k

H = lambda b: hashlib.sha256(b).digest()
def prg(seed, nb):
    out, i = b"", 0
    while len(out) < nb: out += H(seed + struct.pack(">I", i)); i += 1
    return out[:nb]
def ro(bits, data):
    a = bytearray(prg(H(struct.pack(">I", bits) + data), (bits + 7) // 8))
    if bits % 8: a[0] &= (1 << (bits % 8)) - 1
    return bytes(a)

class Session:
    """A Verificatum 3.1.0 shuffling session (protInfo.xml, default/), key width κ."""
    def __init__(self, prot, d):
        self.prot, self.d = prot, d
        x = open(prot).read()
        tag = lambda n: re.search("<%s>(.*?)</%s>" % (n, n), x, re.S).group(1).strip()
        self.pg = tag("pgroup")
        gt = bt_dec(bytes.fromhex(self.pg.split("::")[-1]))[0]
        self.p, self.q, self.g = (ival(z) for z in gt[1][1][1][:3])
        self.kp, self.kq = width_of(self.p), width_of(self.q)
        self.ne, self.nr, self.nv = int(tag("ebitlenro")), int(tag("statdist")), int(tag("vbitlenro"))
        self.kw = int(tag("keywidth"))
        rf = lambda f: open(os.path.join(d, f)).read().strip()
        L = lambda s: ("L", s.encode())
        i4 = lambda n: ("L", struct.pack(">I", n))
        self.rho = H(bt_enc(("N", [L(rf("version")), L(tag("sid") + "." + rf("auxsid")), i4(self.nr), i4(self.nv),
                                   i4(self.ne), L(tag("prg")), L(self.pg), L(tag("rohash"))])))
        pk = bt_load(os.path.join(d, "FullPublicKey.bt"))
        self.ys = self.prod(pk[1][1])
        self.w = self.ciphs(bt_load(os.path.join(d, "Ciphertexts.bt")))
        self.n = len(self.w)
        s = ro(256, self.rho + bt_enc(("L", b"generators")))
        np_ = self.p.bit_length(); nb = (np_ + self.nr + 7) // 8; out = prg(s, nb * self.n)
        self.hs = [pow(int.from_bytes(out[nb * i:nb * i + nb], "big") % (1 << (np_ + self.nr)), (self.p - 1) // self.q, self.p)
                   for i in range(self.n)]
    # elements of G^κ (a leaf for κ = 1) and arrays of them (κ component arrays)
    def prod(self, t): return [ival(t)] if self.kw == 1 else [ival(z) for z in t[1]]
    def bt_prod(self, xs): return leaf(self.kp, xs[0]) if self.kw == 1 else ("N", [leaf(self.kp, x) for x in xs])
    def prod_array(self, t):
        if self.kw == 1: return [[ival(z)] for z in t[1]]
        return [list(r) for r in zip(*[[ival(z) for z in c[1]] for c in t[1]])]
    def bt_prod_array(self, xs):
        if self.kw == 1: return ("N", [leaf(self.kp, x[0]) for x in xs])
        return ("N", [("N", [leaf(self.kp, x) for x in c]) for c in zip(*xs)])
    def ciphs(self, t): return list(zip(self.prod_array(t[1][0]), self.prod_array(t[1][1])))
    def bt_ciphs(self, cs): return ("N", [self.bt_prod_array([u for u, _ in cs]), self.bt_prod_array([v for _, v in cs])])
    def bt_pk(self): return ("N", [self.bt_prod([self.g] * self.kw), self.bt_prod(self.ys)])
    def bt_elems(self, xs): return ("N", [leaf(self.kp, x) for x in xs])
    # Enc(1; s) for s ∈ Z_q^κ, and ciphertext arithmetic
    def enc1(self, s): return ([pow(self.g, x, self.p) for x in s], [pow(y, x, self.p) for y, x in zip(self.ys, s)])
    def cmul(self, a, b): return ([x * y % self.p for x, y in zip(a[0], b[0])], [x * y % self.p for x, y in zip(a[1], b[1])])
    def cpow(self, a, e): return ([pow(x, e, self.p) for x in a[0]], [pow(x, e, self.p) for x in a[1]])
    def mexp(self, bs, es): return functools.reduce(lambda acc, be: acc * pow(be[0], be[1] % self.q, self.p) % self.p, zip(bs, es), 1)
    def challenges(self, u, wout, tau):
        seed = ro(256, self.rho + bt_enc(("N", [leaf(self.kp, self.g), self.bt_elems(self.hs), self.bt_elems(u),
                                                 self.bt_pk(), self.bt_ciphs(self.w), self.bt_ciphs(wout)])))
        nb = (self.ne + 7) // 8; out = prg(seed, nb * self.n)
        es = [int.from_bytes(out[nb * i:nb * i + nb], "big") % (1 << self.ne) for i in range(self.n)]
        v = int.from_bytes(ro(self.nv, self.rho + bt_enc(("N", [("L", seed), tau]))), "big")
        return es, v

    def prove(self, rng, wout, pi, r, s):
        """Writes a proof of a shuffle of server 1 for the statement (self.w, wout), computed with the
        witness (pi, r, s): u_i = g^{r_i} h_{pi(i)}; the prover's equations assume wout_j = Enc(1; s_j)
        w_{pi^-1(j)}, which a false statement does not satisfy. pi need not be a permutation."""
        p, q, g, n, kw = self.p, self.q, self.g, self.n, self.kw
        u = [pow(g, r[i], p) * self.hs[pi[i]] % p for i in range(n)]
        ob = [rng.randrange(q) for _ in range(n)]
        oA, oC, oD = rng.randrange(q), rng.randrange(q), rng.randrange(q)
        oE = [rng.randrange(q) for _ in range(n)]; oF = [rng.randrange(q) for _ in range(kw)]
        # B: the chain, with b_i fresh; computed once e is known, so the announcement needs B first:
        # B depends on e' (after e), hence B is part of the second message, as in Verificatum (tau contains B)
        bs = [rng.randrange(q) for _ in range(n)]
        def finish(es):
            ep = [0] * n
            for i in range(n): ep[pi[i]] = (ep[pi[i]] + es[i]) % q
            B, prev, x, prevx = [], self.hs[0], [], 0
            for i in range(n):
                B.append(pow(g, bs[i], p) * pow(prev, ep[i], p) % p); prev = B[-1]
                prevx = (bs[i] + ep[i] * prevx) % q; x.append(prevx)
            a = sum(r[i] * es[i] for i in range(n)) % q
            c = sum(r) % q
            d = x[-1]
            f = [sum(s[j][k] * ep[j] for j in range(n)) % q for k in range(kw)]
            A_ = pow(g, oA, p) * self.mexp(self.hs, oE) % p
            C_, D_ = pow(g, oC, p), pow(g, oD, p)
            Bp = [self.hs[0]] + B[:-1]
            B_ = [pow(g, ob[i], p) * pow(Bp[i], oE[i], p) % p for i in range(n)]
            F_ = self.enc1([(-x) % q for x in oF])
            for j in range(n): F_ = self.cmul(F_, self.cpow(wout[j], oE[j]))
            return ep, B, a, c, d, f, A_, C_, D_, B_, F_
        # e depends only on (u, w, wout): compute it, then the announcement, then v
        es, _ = self.challenges(u, wout, ("N", []))
        ep, B, a, c, d, f, A_, C_, D_, B_, F_ = finish(es)
        tau = ("N", [self.bt_elems(B), leaf(self.kp, A_), self.bt_elems(B_), leaf(self.kp, C_), leaf(self.kp, D_),
                     ("N", [self.bt_prod(F_[0]), self.bt_prod(F_[1])])])
        _, v = self.challenges(u, wout, tau)
        kA, kC, kD = (oA + v * a) % q, (oC + v * c) % q, (oD + v * d) % q
        kB = [(ob[i] + v * bs[i]) % q for i in range(n)]
        kE = [(oE[j] + v * ep[j]) % q for j in range(n)]
        kF = [(oF[k] + v * f[k]) % q for k in range(kw)]
        lq = lambda x: leaf(self.kq, x)
        sigma = ("N", [lq(kA), ("N", [lq(x) for x in kB]), lq(kC), lq(kD), ("N", [lq(x) for x in kE]),
                       lq(kF[0]) if kw == 1 else ("N", [lq(x) for x in kF])])
        pr = os.path.join(self.d, "proofs")
        bt_save(os.path.join(pr, "PermutationCommitment01.bt"), self.bt_elems(u))
        bt_save(os.path.join(pr, "PoSCommitment01.bt"), tau)
        bt_save(os.path.join(pr, "PoSReply01.bt"), sigma)
        bt_save(os.path.join(pr, "Ciphertexts01.bt"), self.bt_ciphs(wout))
        bt_save(os.path.join(self.d, "ShuffledCiphertexts.bt"), self.bt_ciphs(wout))

    def shuffle(self, rng, pi, s):
        """wout_j = Enc(1; s_j) w_{pi^-1(j)} for a permutation pi"""
        inv = [0] * self.n
        for i in range(self.n): inv[pi[i]] = i
        return [self.cmul(self.enc1(s[j]), self.w[inv[j]]) for j in range(self.n)]

# ------------------------------------------------- IVXV decryption proofs (DER)
OID_MODP = "1.3.6.1.4.1.3029.2.1"
def der_len(n):
    if n < 128: return bytes([n])
    b = n.to_bytes((n.bit_length() + 7) // 8, "big"); return bytes([0x80 | len(b)]) + b
def tlv(t, c): return bytes([t]) + der_len(len(c)) + c
def der_int(x): return tlv(0x02, x.to_bytes(x.bit_length() // 8 + 1, "big", signed=True))
def der_seq(*cs): return tlv(0x30, b"".join(cs))
def der_gstr(s): return tlv(0x1b, s.encode())
def der_oid(o):
    a = [int(x) for x in o.split(".")]; body = bytes([40 * a[0] + a[1]])
    for x in a[2:]:
        enc = [x & 0x7f]; x >>= 7
        while x: enc.append(0x80 | (x & 0x7f)); x >>= 7
        body += bytes(reversed(enc))
    return tlv(0x06, body)
def der_bits(b): return tlv(0x03, b"\x00" + b)

def ivxv_pk_bytes(p, g, eid, y):
    """X509PublicKey(OID_MODP, Sequence(y), params = Sequence(Field(p), Field(g), GeneralString(eid)))"""
    params = der_seq(der_int(p), der_int(g), der_gstr(eid))
    return der_seq(der_seq(der_oid(OID_MODP), params), der_bits(der_seq(der_int(y))))
def ivxv_ct_bytes(c1, c2): return der_seq(der_seq(der_oid(OID_MODP)), der_seq(der_int(c1), der_int(c2)))
def dec_prefix(p, g, eid, y, c1, c2, d):
    """the DER content of the challenge sequence before a and b"""
    return der_gstr("DECRYPTION") + ivxv_pk_bytes(p, g, eid, y) + ivxv_ct_bytes(c1, c2) + der_int(d)
def dprng_int(seed, upper):
    out, ctr = b"", 1
    nb = (upper.bit_length() + 7) // 8; m = upper.bit_length() % 8; mask = 0xff if m == 0 else (1 << m) - 1
    while True:
        while len(out) < nb: out += H(ctr.to_bytes(8, "big") + seed); ctr += 1
        b, out = bytearray(out[:nb]), out[nb:]
        b[0] &= mask
        x = int.from_bytes(b, "big")
        if x < upper: return x
def dec_challenge(prefix, a, b, q): return dprng_int(tlv(0x30, prefix + der_int(a) + der_int(b)), q)
def dec_prove(rng, p, q, g, eid, x, c1, c2, d, wrong_x=None):
    """a decryption proof of d for (c1, c2) under y = g^x; with wrong_x the responses use another key"""
    y = pow(g, x, p); t = rng.randrange(q)
    a, b = pow(c1, t, p), pow(g, t, p)
    k = dec_challenge(dec_prefix(p, g, eid, y, c1, c2, d), a, b, q)
    s = (t + k * (x if wrong_x is None else wrong_x)) % q
    return a, b, s

# strict DER reader (our side's parser of the IVXV encodings: definite minimal lengths,
# minimal INTEGERs, no trailing data)
class DerError(Exception): pass
def der_read(b, pos=0):
    if pos + 2 > len(b): raise DerError("truncated")
    t = b[pos]; l = b[pos + 1]; pos += 2
    if l & 0x80:
        k = l & 0x7f
        if k == 0 or k > 4 or pos + k > len(b): raise DerError("length")
        l = int.from_bytes(b[pos:pos + k], "big"); pos += k
        if l < 128 or b[pos - k] == 0: raise DerError("non-minimal length")
    if pos + l > len(b): raise DerError("truncated")
    return t, b[pos:pos + l], pos + l
def der_one(b, tag):
    t, c, end = der_read(b)
    if t != tag or end != len(b): raise DerError("expected tag %#x" % tag)
    return c
def der_items(c):
    out, pos = [], 0
    while pos < len(c):
        t, v, pos = der_read(c, pos); out.append((t, v))
    return out
def der_intval(t_v):
    t, v = t_v
    if t != 0x02 or not v: raise DerError("INTEGER")
    if len(v) > 1 and ((v[0] == 0 and v[1] < 0x80) or (v[0] == 0xff and v[1] >= 0x80)): raise DerError("non-minimal INTEGER")
    return int.from_bytes(v, "big", signed=True)
def parse_dec_case(pk, ct, msg, proof):
    """(p, g, eid, y, c1, c2, d, a, b, s) from the hex DER of a case, or DerError"""
    pk, ct, msg, proof = (bytes.fromhex(x) for x in (pk, ct, msg, proof))
    alg, bits = der_items(der_one(pk, 0x30))
    oid, params = der_items(der_one(bytes([alg[0]]) + der_len(len(alg[1])) + alg[1], 0x30))
    if oid[0] != 0x06 or tlv(0x06, oid[1]) != der_oid(OID_MODP): raise DerError("key OID")
    pi = der_items(params[1]) if params[0] == 0x30 else []
    if len(pi) != 3 or pi[2][0] != 0x1b: raise DerError("parameters")
    p, g, eid = der_intval(pi[0]), der_intval(pi[1]), pi[2][1].decode()
    if bits[0] != 0x03 or not bits[1] or bits[1][0] != 0: raise DerError("BIT STRING")
    yi = der_items(der_one(bits[1][1:], 0x30))
    if len(yi) != 1: raise DerError("key")
    y = der_intval(yi[0])
    oseq, pair = der_items(der_one(ct, 0x30))
    if oseq[0] != 0x30 or der_seq(der_oid(OID_MODP)) != tlv(0x30, oseq[1]): raise DerError("ciphertext OID")
    if pair[0] != 0x30: raise DerError("ciphertext")
    cc = der_items(pair[1])
    if len(cc) != 2: raise DerError("ciphertext")
    c1, c2 = der_intval(cc[0]), der_intval(cc[1])
    d = der_intval((0x02, der_one(msg, 0x02)))
    pp = der_items(der_one(proof, 0x30))
    if len(pp) != 3: raise DerError("proof")
    a, b, s = der_intval(pp[0]), der_intval(pp[1]), der_intval(pp[2])
    return p, g, eid, y, c1, c2, d, a, b, s

# ---------------------------------------- IVXV Go core decryption proofs (DER)
P14 = int("FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DD"
          "EF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7ED"
          "EE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F"
          "83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3B"
          "E39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA0510"
          "15728E5A8AACAA68FFFFFFFFFFFFFFFF", 16)
Q14 = (P14 - 1) // 2
def der_pstr(s): return tlv(0x13, s.encode())
def der_octets(b): return tlv(0x04, b)
def go_prefix(y, c1, c2, d):
    """ProofChallenge: SEQUENCE(PrintableString "DECRYPTION", y, SEQUENCE(c1, c2), d, msgc, keyc, SEQUENCE(OCTET STRING salt))"""
    return der_pstr("DECRYPTION") + der_int(y) + der_seq(der_int(c1), der_int(c2)) + der_int(d)
def go_suffix(salt): return der_seq(der_octets(salt or b""))   # Prove/Verify pass the salt as one variadic argument
def go_rand_int(stream, mx):
    """crypto/rand.Int(reader, max) over a byte stream, then ScalarValueOfReader maps 0 to 1"""
    bl = (mx - 1).bit_length(); k = (bl + 7) // 8; b = bl % 8 or 8; pos = 0
    while True:
        chunk = bytearray(stream[pos:pos + k]); pos += k
        if len(chunk) < k: raise ValueError("stream exhausted")
        chunk[0] &= (1 << b) - 1
        n = int.from_bytes(chunk, "big")
        if n < mx: return n or 1
def go_challenge(prefix, msgc, keyc, suffix, q):
    der = der_seq(prefix + der_int(msgc) + der_int(keyc) + suffix)
    return go_rand_int(hashlib.shake_256(der).digest(4096), q)
def go_parse_proof(pk, proof):
    """(y, c1, c2, d, e, s) from hex DER, strict"""
    y = der_intval((0x02, der_one(bytes.fromhex(pk), 0x02)))
    ct, dd, tr = der_items(der_one(bytes.fromhex(proof), 0x30))
    if ct[0] != 0x30 or tr[0] != 0x30: raise DerError("proof")
    cc, ee = der_items(ct[1]), der_items(tr[1])
    if len(cc) != 2 or len(ee) != 2: raise DerError("proof")
    return y, der_intval(cc[0]), der_intval(cc[1]), der_intval(dd), der_intval(ee[0]), der_intval(ee[1])
def go_proof_der(c1, c2, d, e, s): return der_seq(der_seq(der_int(c1), der_int(c2)), der_int(d), der_seq(der_int(e), der_int(s)))
def go_prove(rng, x, c1, c2, d, salt, wrong_x=None, p=P14, q=Q14, g=2):
    y = pow(g, x, p); t = rng.randrange(1, q)
    msgc, keyc = pow(c1, t, p), pow(g, t, p)
    e = go_challenge(go_prefix(y, c1, c2, d), msgc, keyc, go_suffix(salt), q)
    return e, (t + e * (x if wrong_x is None else wrong_x)) % q
