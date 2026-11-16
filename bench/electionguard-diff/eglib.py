"""ElectionGuard 2.0 primitives for the campaign (specification 2.0.0, as
implemented by electionguard-kotlin-multiplatform at the pinned commit):
the hash function H (HMAC-SHA-256 over fixed-width encodings, Section 5),
exponential ElGamal, the disjunctive Chaum–Pedersen range proof (3.3.5,
egk ChaumPedersen.kt makeChaumPedersenWithNonces) and the hashes of a
ballot (contest hash 0x23, confirmation code 0x24). Used to build forged
ballots; validated at start-up against the reference's own proofs
(selftest)."""
import glob, hashlib, hmac, json, os

def load(path): return json.load(open(path))
def ip(h): return int(h, 16)
def hx(x, width): return format(x, "0%dX" % (2 * width))   # egk writes fixed-width uppercase hex

class Group:
    def __init__(self, record):
        c = load(os.path.join(record, "constants.json"))
        self.p, self.q, self.g = ip(c["large_prime"]), ip(c["small_prime"]), ip(c["generator"])

def enc_p(x): return x.to_bytes(512, "big")
def enc_q(x): return x.to_bytes(32, "big")
def enc_int(n): return n.to_bytes(4, "big")

def H(key: bytes, parts) -> bytes:
    return hmac.new(key, b"".join(parts), hashlib.sha256).digest()
def Hq(G, key, parts): return int.from_bytes(H(key, parts), "big") % G.q

class Election:
    """the public data of a record that the forgeries need"""
    def __init__(self, record):
        self.G = Group(record)
        init = load(os.path.join(record, "election_initialized.json"))
        self.K = ip(init["joint_public_key"])
        self.HE = bytes.fromhex(init["extended_base_hash"])
        self.config = load(os.path.join(record, "election_config.json"))
        self.manifest = load(os.path.join(record, "manifest.json"))

    def encrypt(self, sigma, xi):        # (g^ξ, K^(σ+ξ))
        p = self.G.p
        return pow(self.G.g, xi, p), pow(self.K, (sigma + xi) % self.G.q, p)

    def range_challenge(self, alpha, beta, ab):
        return Hq(self.G, self.HE, [b"\x21", enc_p(self.K), enc_p(alpha), enc_p(beta)] + [enc_p(x) for x in ab])

    def range_proof(self, alpha, beta, vote, xi, limit, rng):
        """egk makeChaumPedersenWithNonces: the honest algorithm, run with the
        claimed vote ℓ and nonce ξ; a cheating prover runs it with a ℓ the
        ciphertext does not encrypt (every challenge is still the hash of the
        prover's own commitments)"""
        G = self.G; p, q, g, K = G.p, G.q, G.g, self.K
        us = [rng.randrange(q) for _ in range(limit + 1)]
        cs = [rng.randrange(q) for _ in range(limit + 1)]
        ab = []
        for j, u in enumerate(us):
            ab.append(pow(g, u, p))
            ab.append(pow(K, u if j == vote else ((vote - j) * cs[j] + u) % q, p))
        c = self.range_challenge(alpha, beta, ab)
        cl = (c - sum(cj for j, cj in enumerate(cs) if j != vote)) % q
        cfinal = [cl if j == vote else cj for j, cj in enumerate(cs)]
        return [{"challenge": hx(cj, 32), "response": hx((u - cj * xi) % q, 32)} for u, cj in zip(us, cfinal)]

    def verify_range(self, alpha, beta, proofs, limit):
        """egk ChaumPedersenRangeProofKnownNonce.verify (used only by the self-test)"""
        G = self.G; p, q, g, K = G.p, G.q, G.g, self.K
        if len(proofs) != limit + 1: return False
        ab = []
        for j, pr in enumerate(proofs):
            cj, vj = ip(pr["challenge"]), ip(pr["response"])
            ab.append(pow(g, vj, p) * pow(alpha, cj, p) % p)
            ab.append(pow(K, (vj - j * cj) % q, p) * pow(beta, cj, p) % p)
        return self.range_challenge(alpha, beta, ab) == sum(ip(pr["challenge"]) for pr in proofs) % q

    def contest_hash(self, seq, cts):
        return H(self.HE, [b"\x23", enc_int(seq), enc_p(self.K)] + [enc_p(x) for c in cts for x in c])

    def confirmation_code(self, chis, baux: bytes):
        return H(self.HE, [b"\x24"] + chis + [baux])

def ballots(record):
    return sorted(glob.glob(os.path.join(record, "encrypted_ballots", "*", "eballot-*.json")))

def selftest(record):
    """the hashes and the range-proof equations reproduce the reference's own ballots"""
    E = Election(record)
    for f in ballots(record)[:2]:
        b = load(f)
        chis = []
        for c in b["contests"]:
            cts = [(ip(s["encrypted_vote"]["pad"]), ip(s["encrypted_vote"]["data"])) for s in c["selections"]]
            chi = E.contest_hash(c["sequence_order"], cts)
            assert chi.hex().upper() == c["contest_hash"], "contest hash"
            chis.append(chi)
            for (a, bb), s in zip(cts, c["selections"]):
                assert E.verify_range(a, bb, s["proof"]["proofs"], len(s["proof"]["proofs"]) - 1), "range proof"
            A = B = 1
            for a, bb in cts: A, B = A * a % E.G.p, B * bb % E.G.p
            assert E.verify_range(A, B, c["proof"]["proofs"], c["votes_allowed"]), "selection-limit proof"
        assert E.confirmation_code(chis, bytes.fromhex(b["code_baux"])).hex().upper() == b["confirmation_code"], "confirmation code"
    return E
