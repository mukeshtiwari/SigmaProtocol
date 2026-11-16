"""Belenios 3.2.0 public data (specification version 1, group Ed25519), for
differential testing: the archive format, the serialisations and the
cryptography of the Belenios specification (doc/specification.tex of the
pinned release), written from the specification, with all randomness drawn
from a seeded generator so that every generated case is reproducible.

Archive (src/lib/core/tar.ml): a tar of the entries BELENIOS, DATA.data.json
and EVENT.event.json, each named by the SHA-256 (hex) of its content, with
Belenios's own "reproducible" headers (mode 644, uid/gid 0, the archive's
timestamp); belenios-tool refuses any other header. Events form a chain:
each names its parent's hash and its payload's hash. Archive.save rewrites
every reference after a change, so a tampered archive is consistent and
reaches the checks behind the integrity check."""
import base64, hashlib, json

# ---- Ed25519 (twisted Edwards, a = -1), extended coordinates ----
P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = (-121665 * pow(121666, P - 2, P)) % P
BX = 15112221349535400772501151409588531511454012693041857206046113283949847762202
BY = 46316835694926478169428394003475163141307993866256225615783033603165251855960
SQRT_M1 = pow(2, (P - 1) // 4, P)

def ext(x, y): return (x, y, 1, x * y % P)
ZERO = (0, 1, 1, 0)
G = ext(BX, BY)

def add(p1, p2):
    X1, Y1, Z1, T1 = p1; X2, Y2, Z2, T2 = p2
    A = (Y1 - X1) * (Y2 - X2) % P; B = (Y1 + X1) * (Y2 + X2) % P
    C = 2 * D * T1 * T2 % P; Dd = 2 * Z1 * Z2 % P
    E, F, Gg, H = B - A, Dd - C, Dd + C, B + A
    return (E * F % P, Gg * H % P, F * Gg % P, E * H % P)
def neg(p1): X, Y, Z, T = p1; return ((-X) % P, Y, Z, (-T) % P)
def mul(k, p1):
    k %= L
    r = ZERO
    while k:
        if k & 1: r = add(r, p1)
        p1 = add(p1, p1); k >>= 1
    return r
def mul_raw(k, p1):   # without reduction mod L (for points outside the subgroup)
    r = ZERO
    while k:
        if k & 1: r = add(r, p1)
        p1 = add(p1, p1); k >>= 1
    return r
def affine(p1):
    X, Y, Z, _ = p1; zi = pow(Z, P - 2, P); return (X * zi % P, Y * zi % P)
def eq(p1, p2): return affine(p1) == affine(p2)
def sub(p1, p2): return add(p1, neg(p2))
def gpow(m): return mul(m, G)

# Belenios's serialisation of a point: the integer y | (x mod 2) << 255, as 64 hex digits
def tostr(p1):
    x, y = affine(p1); return "%064x" % (y | ((x & 1) << 255))
def ofstr(s, check=True):
    z = int(s, 16); y = z & ((1 << 255) - 1); sign = z >> 255
    if check and y >= P: raise ValueError("non-canonical")
    y2 = y * y % P; u = (y2 - 1) % P; v = (D * y2 + 1) % P
    x2 = u * pow(v, P - 2, P) % P
    x = pow(x2, (P + 3) // 8, P)
    if (x * x - x2) % P: x = x * SQRT_M1 % P
    if (x * x - x2) % P: raise ValueError("not on the curve")
    if (x & 1) != sign: x = (-x) % P
    return ext(x, y)

# ---- hashes ----
def sha256_hex(b): return hashlib.sha256(b).hexdigest()
def sha256_b64(b): return base64.b64encode(hashlib.sha256(b).digest()).decode().rstrip("=")
def hashq(prefix, pts):   # SHA256(prefix ^ points joined by commas) mod l
    return int(sha256_hex((prefix + ",".join(tostr(x) for x in pts)).encode()), 16) % L

def secret(uuid, cred):   # secret(c), specification section "Credentials"
    xs = "".join(sha256_hex(("derive_credential|%s|%d|%s" % (uuid, i, cred)).encode()) for i in (0, 1))
    return int(xs, 16) % L

def compact(obj): return json.dumps(obj, separators=(",", ":"), ensure_ascii=False).encode()

# ---- the archive ----
def tar_header(name, size, ts):
    if len(name) >= 100: raise ValueError("name too long")
    b = bytearray(512)
    def put(pos, s): b[pos:pos + len(s)] = s.encode()
    put(0, name); put(100, "0000644"); put(108, "0000000"); put(116, "0000000")
    put(124, "%011o" % size); put(136, "%011o" % ts); put(148, "        "); put(156, "0")
    put(148, "%06o\0 " % sum(b))
    return bytes(b)

class Archive:
    """entries: list of (name, bytes) in tar order; the BELENIOS header first"""
    def __init__(self, entries, ts, trailer):
        self.entries, self.ts, self.trailer = entries, ts, trailer

    @staticmethod
    def load(path):
        raw = open(path, "rb").read()
        entries, pos, ts = [], 0, 0
        while pos + 512 <= len(raw) and raw[pos:pos + 512] != bytes(512):
            h = raw[pos:pos + 512]
            name = h[:100].split(b"\0")[0].decode(); size = int(h[124:135], 8); ts = int(h[136:147], 8)
            data = raw[pos + 512:pos + 512 + size]
            entries.append((name, data)); pos += 512 + (size + 511) // 512 * 512
        return Archive(entries, ts, len(raw) - pos)

    def tobytes(self):
        out = bytearray()
        for name, data in self.entries:
            out += tar_header(name, len(data), self.ts) + data + bytes((-len(data)) % 512)
        return bytes(out) + bytes(self.trailer)

    def save(self, path): open(path, "wb").write(self.tobytes())
    def copy(self): return Archive(list(self.entries), self.ts, self.trailer)

    # ---- the documents ----
    def raw(self, h): return dict(self.entries)[h + ".data.json"]
    def doc(self, h): return json.loads(self.raw(h))
    def events(self):
        return [(n[:-len(".event.json")], json.loads(d)) for n, d in self.entries if n.endswith(".event.json")]
    def payloads(self, typ): return [ev["payload"] for _, ev in self.events() if ev["type"] == typ]

    def replace_data(self, old, new_bytes):
        """replace the document named old by new_bytes; every reference to old (in documents
        and events) is renamed, and the event chain rehashed. Returns the new name."""
        new = sha256_hex(new_bytes)
        self.entries = [((new + ".data.json", new_bytes) if n == old + ".data.json" else (n, d)) for n, d in self.entries]
        if new != old: self._rename(old, new)
        return new

    def _rename(self, old, new):
        o, nw = old.encode(), new.encode()
        changed = []
        for i, (n, d) in enumerate(self.entries):
            if n.endswith(".data.json") and o in d:
                nd = d.replace(o, nw); changed.append((n[:-len(".data.json")], nd))
        for h, nd in changed:
            self.replace_data(h, nd)
        self.rechain()

    def rechain(self):
        """recompute the event chain (parents) after a change, keeping the events' order"""
        self.set_events(self.event_list())

    def set_events(self, evs):
        """replace the events by the list evs of event dicts (parent fields ignored), in order;
        each event is placed after the documents it references"""
        datas = [(n, d) for n, d in self.entries if not n.endswith(".event.json")]
        out = [e for e in datas if e[0] == "BELENIOS"]
        placed = {"BELENIOS"}
        docs = dict(datas)
        def refs(b): return [h for h in [x[:64] for x in docs] if h.encode() in b and (h + ".data.json") in docs]
        def place(h):
            n = h + ".data.json"
            if n in placed or n not in docs: return
            placed.add(n)
            for r in refs(docs[n]):
                if r != h: place(r)
            out.append((n, docs[n]))
        parent = None
        for ev in evs:
            if "payload" in ev: place(ev["payload"])
            e = {}
            if parent is not None: e["parent"] = parent
            for k in ("height", "type", "payload"):
                if k in ev: e[k] = ev[k]
            b = compact(e); parent = sha256_hex(b); out.append((parent + ".event.json", b))
        self.entries = out

    def add_data(self, b):
        h = sha256_hex(b)
        if (h + ".data.json") not in dict(self.entries):
            # inserted after BELENIOS; set_events places it before its event
            self.entries.insert(1, (h + ".data.json", b))
        return h

    def event_list(self):
        return [dict(ev) for _, ev in self.events()]

# ---- an election, read from an archive ----
class Election:
    def __init__(self, arch):
        self.arch = arch
        setup_h = arch.payloads("Setup")[0]
        self.setup = arch.doc(setup_h)
        self.election_raw = arch.raw(self.setup["election"])
        self.election = json.loads(self.election_raw)
        self.uuid = self.election["uuid"]
        self.fingerprint = sha256_b64(self.election_raw)
        self.y = ofstr(self.election["public_key"])
        self.trustees = arch.doc(self.setup["trustees"])
        self.creds_raw = arch.doc(self.setup["credentials"])
        self.weights = {}
        for c in self.creds_raw:
            parts = c.split(",")
            self.weights[parts[0]] = int(parts[1]) if len(parts) > 1 else 1
        self.weighted = any("," in c for c in self.creds_raw)
        self.questions = self.election["questions"]

    def ballots(self): return [(h, self.arch.doc(h)) for h in self.arch.payloads("Ballot")]

# ---- the cryptography of a ballot (specification sections Encrypted answers to Signatures) ----
class Prover:
    def __init__(self, el, rng):
        self.el, self.rng = el, rng
    def rand(self): return self.rng.randrange(L)

    def iprove(self, prefix_S, alpha, beta, r, i, Ms, y=None):
        """interval proof that (alpha, beta) = (g^r, y^r g^{M_i}), M = Ms (Section "Proofs of interval membership")"""
        y = y or self.el.y
        k = len(Ms); cs, rs, As, Bs = [0] * k, [0] * k, [None] * k, [None] * k
        for j in range(k):
            if j == i: continue
            cs[j], rs[j] = self.rand(), self.rand()
            As[j] = add(gpow(rs[j]), mul(cs[j], alpha))
            Bs[j] = add(mul(rs[j], y), mul(cs[j], sub(beta, gpow(Ms[j]))))
        w = self.rand(); As[i] = gpow(w); Bs[i] = mul(w, y)
        h = hashq("prove|%s|%s,%s|" % (prefix_S, tostr(alpha), tostr(beta)), [x for j in range(k) for x in (As[j], Bs[j])])
        cs[i] = (h - sum(cs[j] for j in range(k) if j != i)) % L
        rs[i] = (w - r * cs[i]) % L
        return [{"challenge": str(cs[j]), "response": str(rs[j])} for j in range(k)]

    def encrypt(self, m, y=None):
        y = y or self.el.y; r = self.rand()
        return r, (gpow(r), add(mul(r, y), gpow(m)))

    def answer(self, S0, q, vote, hooks=None):
        """the answer_h to question q for the 0/1 vector vote (with its leading blank entry if q is blank)"""
        hooks = hooks or {}
        rs, cts = [], []
        for m in vote:
            r, c = self.encrypt(m); rs.append(r); cts.append(c)
        choices = [{"alpha": tostr(a), "beta": tostr(b)} for a, b in cts]
        b = ",".join("%s,%s" % (c["alpha"], c["beta"]) for c in choices)
        S = S0 + "|" + b
        indiv = [self.iprove(S0, a, bb, r, m, [0, 1]) for (a, bb), r, m in zip(cts, rs, vote)]
        ans = {"choices": choices, "individual_proofs": indiv}
        mn, mx = q.get("min", 0), q.get("max", len(q["answers"]))
        if not q.get("blank"):
            A = ZERO; B = ZERO
            for a, bb in cts: A = add(A, a); B = add(B, bb)
            M = sum(vote); R = sum(rs) % L
            ans["overall_proof"] = self.iprove(S, A, B, R, M - mn, list(range(mn, mx + 1)))
        else:
            ans.update(self.blank_proofs(S, cts, rs, vote, mn, mx, hooks))
        return ans

    def blank_proofs(self, S, cts, rs, vote, mn, mx, hooks):
        y = self.el.y
        (a0, b0), r0, m0 = cts[0], rs[0], vote[0]
        aS = ZERO; bS = ZERO
        for a, bb in cts[1:]: aS = add(aS, a); bS = add(bS, bb)
        rS = sum(rs[1:]) % L; mS = sum(vote[1:])
        # blank_proof: m0 = 0 or mS = 0 (pi_0, pi_Sigma)
        def cp(alpha, beta, c, r): return add(gpow(r), mul(c, alpha)), add(mul(r, y), mul(c, beta))
        if m0 == 0:   # true branch 0
            cS, rSig = self.rand(), self.rand(); AS, BS = cp(aS, bS, cS, rSig)
            w = self.rand(); A0, B0 = gpow(w), mul(w, y)
            h = hashq("bproof0|%s|" % S, [A0, B0, AS, BS]); c0 = (h - cS) % L; r0p = (w - r0 * c0) % L
        else:         # true branch Sigma
            c0, r0p = self.rand(), self.rand(); A0, B0 = cp(a0, b0, c0, r0p)
            w = self.rand(); AS, BS = gpow(w), mul(w, y)
            h = hashq("bproof0|%s|" % S, [A0, B0, AS, BS]); cS = (h - c0) % L; rSig = (w - rS * cS) % L
        bproof = [{"challenge": str(c0), "response": str(r0p)}, {"challenge": str(cS), "response": str(rSig)}]
        # overall_proof: m0 = 1 or mS in [min..max] (pi_0, pi_1..pi_k)
        Ms = list(range(mn, mx + 1)); k = len(Ms)
        cs, rr, As, Bs = [0] * (k + 1), [0] * (k + 1), [None] * (k + 1), [None] * (k + 1)
        true = 0 if m0 == 1 else 1 + Ms.index(mS)
        for j in range(k + 1):
            if j == true: continue
            cs[j], rr[j] = self.rand(), self.rand()
            if j == 0: As[0], Bs[0] = add(gpow(rr[0]), mul(cs[0], a0)), add(mul(rr[0], y), mul(cs[0], sub(b0, G)))
            else: As[j], Bs[j] = add(gpow(rr[j]), mul(cs[j], aS)), add(mul(rr[j], y), mul(cs[j], sub(bS, gpow(Ms[j - 1]))))
        w = self.rand(); As[true], Bs[true] = gpow(w), mul(w, y)
        h = hashq("bproof1|%s|" % S, [x for j in range(k + 1) for x in (As[j], Bs[j])])
        cs[true] = (h - sum(cs[j] for j in range(k + 1) if j != true)) % L
        rr[true] = (w - (r0 if true == 0 else rS) * cs[true]) % L
        oproof = [{"challenge": str(cs[j]), "response": str(rr[j])} for j in range(k + 1)]
        return {"overall_proof": oproof, "blank_proof": bproof}

    def ballot(self, cred, votes, uuid=None, election_hash=None, S0_fingerprint=None, sign=True):
        """a ballot for the secret credential cred and the vote vectors votes"""
        el = self.el
        s = secret(el.uuid, cred); C = gpow(s)
        S0 = (S0_fingerprint or el.fingerprint) + "|" + tostr(C)
        b = {"election_uuid": uuid or el.uuid, "election_hash": election_hash or el.fingerprint, "credential": tostr(C),
             "answers": [self.answer(S0, q, v) for q, v in zip(el.questions, votes)]}
        if sign: self.sign(b, s)
        return b

    def sign(self, b, s, hash_override=None):
        """the signature of the ballot b (without its signature field) with the secret s"""
        body = {k: v for k, v in b.items() if k != "signature"}
        h = hash_override or sha256_b64(compact(body))
        w = self.rand(); A = gpow(w); c = hashq("sig|%s|" % h, [A])
        b["signature"] = {"hash": h, "proof": {"challenge": str(c), "response": str((w - s * c) % L)}}
        return b

# ---- the tally (specification sections Encrypted tally, Partial decryptions, Election result) ----
def last(ballots):
    out = []
    for b in ballots:
        out = [x for x in out if x["credential"] != b["credential"]] + [b]
    return out

def encrypted_tally(el, ballots, weights=None):
    weights = weights or el.weights
    tally = []
    for i, q in enumerate(el.questions):
        n = len(q["answers"]) + (1 if q.get("blank") else 0)
        cts = [(ZERO, ZERO)] * n
        for b in ballots:
            w = weights.get(b["credential"], 1)
            for j, c in enumerate(b["answers"][i]["choices"]):
                a, bb = ofstr(c["alpha"]), ofstr(c["beta"])
                cts[j] = (add(cts[j][0], mul(w, a)), add(cts[j][1], mul(w, bb)))
        tally.append(cts)
    return tally

def tally_json(tally): return [[{"alpha": tostr(a), "beta": tostr(b)} for a, b in q] for q in tally]

def partial_decryption(el, tally, x, rng):
    X = gpow(x); factors, proofs = [], []
    for q in tally:
        fq, pq = [], []
        for a, _ in q:
            fq.append(tostr(mul(x, a)))
            w = rng.randrange(L); A, B = gpow(w), mul(w, a)
            c = hashq("decrypt|%s|%s|" % (el.fingerprint, tostr(X)), [A, B])
            pq.append({"challenge": str(c), "response": str((w - x * c) % L)})
        factors.append(fq); proofs.append(pq)
    return {"decryption_factors": factors, "decryption_proofs": proofs}

def result(el, tally, pds, bound):
    res = []
    for i, q in enumerate(tally):
        rq = []
        for j, (_, b) in enumerate(q):
            F = ZERO
            for pd in pds: F = add(F, ofstr(pd["decryption_factors"][i][j]))
            M = sub(b, F); m, acc = 0, ZERO
            while not eq(acc, M):
                m += 1; acc = add(acc, G)
                if m > bound: raise ValueError("discrete log out of bound")
            rq.append(m)
        res.append(rq)
    return res
