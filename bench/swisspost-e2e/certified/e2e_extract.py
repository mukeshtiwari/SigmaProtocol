#!/usr/bin/env python3
"""The protocol wiring of the Swiss Post tally (Verifier Specification 1.7.1,
Algorithms 4.1 and 4.2; System Specification 1.6.1, Algorithms 6.1 and 6.10):
reads an election event's payloads (the layout of Post_E2E_DEV in the
e-voting testdata repository) and writes, for the certified driver
(src/Executable/Swissposte2e), every shuffle and decryption statement of
every ballot box with the inputs, keys and auxiliary information the
specification assigns to it, together with the protocol's own checks that
involve no proof (key combination, agreement of the control components on
the confirmed votes, payload identifiers, gamma' = gamma of the partial
decryptions, the decoded votes).

Trusted code: this file decides which ciphertexts each proof is about.

  online CC j = 1..4   shuffle   C_init (j = 1) or c_dec,j-1  ->  c_mix,j
                                 under CombinePublicKeys(EL_pk,j, ..., EL_pk,4, EB_pk)  (EL_pk for j = 1)
                       decrypt   c_mix,j -> c_dec,j under EL_pk,j, i_aux = (ee, bb, "MixDecOnline", "j")
  tally (CC 5)         shuffle   c_dec,4 -> c_mix,5 under EB_pk cut to delta
                       decrypt   c_mix,5 -> m under EB_pk cut, i_aux = (ee, bb, "MixDecOffline")

C_init: the confirmed votes of CC 1's ballot box payload ordered by
verification card ID, padded with two trivial encryptions
GetCiphertext(1, 1, EL_pk) when there are fewer than two. Shuffles use the
computation-optimized dimensions (m = 1, n = N) and the commitment key of
GetVerifiableCommitmentKey(n) (Algorithm 9.6, checked against the Swiss Post
test vectors at start-up).

usage: e2e_extract.py ELECTION_DIR OUT.json   (ELECTION_DIR contains D2/ and D3/)"""
import base64, glob, hashlib, json, os, sys

root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
ev, out = sys.argv[1], sys.argv[2]

# the payloads encode integers as IntegerToByteArray (Algorithm 3.9: unsigned, big-endian), not as
# Java's two's-complement BigInteger.toByteArray of the crypto-primitives test vectors; so does OUT.json
def dec(s): return int.from_bytes(base64.b64decode(s), "big")
def enc(v): return base64.b64encode(v.to_bytes(max(1, (v.bit_length() + 7) // 8), "big")).decode()
def dec_signed(s): return int.from_bytes(base64.b64decode(s), "big", signed=True)   # the test vectors
def load(f): return json.load(open(f))

# ---- RecursiveHashOfLength / RecursiveHashToZq (Algorithms 5.6, 5.7), GetVerifiableCommitmentKey (9.6) ----
def ibytes(z): return b"" if z == 0 else z.to_bytes((z.bit_length() + 7) // 8, "big")
def cut(b, n):
    L = (n + 7) // 8; b = bytearray(b[len(b) - L:])
    if n % 8: b[0] &= (1 << (n % 8)) - 1
    return bytes(b)
def rhl(l, v):
    L = (l + 7) // 8
    xof = lambda m: cut(hashlib.shake_256(m).digest(L), l)
    if isinstance(v, int): return xof(b"\x01" + ibytes(v))
    if isinstance(v, str): return xof(b"\x02" + v.encode())
    if isinstance(v, bytes): return xof(b"\x00" + v)
    return xof(b"\x03" + b"".join(rhl(l, w) for w in v))
def hash_to_zq(q, *vs):   # the values are hashed flat, (q, "RecursiveHash", v_0, ...), as the test vectors require
    return int.from_bytes(rhl(q.bit_length() + 256, [q, "RecursiveHash", *vs]), "big") % q
def commitment_key(p, q, g, nu):
    v, count, i = [], 0, 0
    while count <= nu:
        w = pow(hash_to_zq(q, "commitmentKey", i, count) + 1, 2, p)
        if w not in (1, g) and w not in v: v.append(w); count += 1
        i += 1
    return v[0], v[1:]
def selftest():
    res = os.path.join(root, "bench/crypto-primitives/src/test/resources")
    for t in load(os.path.join(res, "mixnet/get-verifiable-commitment-key.json")):
        c = t["context"]; p, q, g = dec_signed(c["p"]), dec_signed(c["q"]), dec_signed(c["g"])
        h, gs = commitment_key(p, q, g, t["input"]["k"])
        assert h == dec_signed(t["output"]["h"]) and gs == [dec_signed(x) for x in t["output"]["g"]], t["description"]
selftest()

# ---- the election event ----
# the layout of the testdata repository, or the flattened one of the Swiss Post Verifier's input
def first(*ds): return next((os.path.join(ev, d) for d in ds if os.path.isdir(os.path.join(ev, d))), os.path.join(ev, ds[0]))
setup = first("D2/secure-data-manager-setup/context", "D2/context")
tally = first("D3/secure-data-manager-tally/tally/ballotBoxes", "D3/tally/ballotBoxes")
spk = load(os.path.join(setup, "setupComponentPublicKeysPayload.json"))
grp = spk["encryptionGroup"]; p, q, g = dec(grp["p"]), dec(grp["q"]), dec(grp["g"])
ee = spk["electionEventId"]
K = spk["setupComponentPublicKeys"]
EL = [dec(x) for x in K["electionPublicKey"]]
EB = [dec(x) for x in K["electoralBoardPublicKey"]]
ccm = {c["nodeId"]: [dec(x) for x in c["ccmjElectionPublicKey"]] for c in K["combinedControlComponentPublicKeys"]}
def combine(*keys): return [eval_prod(xs) for xs in zip(*keys)]
def eval_prod(xs):
    r = 1
    for x in xs: r = r * x % p
    return r

statements, checks = [], []
def check(name, ok): checks.append({"name": name, "ok": bool(ok)})
check("setup: EL_pk = CombinePublicKeys(EL_pk,1..4, EB_pk)", sorted(ccm) == [1, 2, 3, 4] and EL == combine(*[ccm[j] for j in (1, 2, 3, 4)], EB))
for j in (1, 2, 3, 4):
    cp = load(os.path.join(setup, f"controlComponentPublicKeysPayload.{j}.json"))
    check(f"setup: CC {j} public key payload agrees with the setup component", cp["controlComponentPublicKeys"]["nodeId"] == j
          and [dec(x) for x in cp["controlComponentPublicKeys"]["ccmjElectionPublicKey"]] == ccm[j])

def ct(j): return [dec(j["gamma"])] + [dec(x) for x in j["phis"]]
def jct(c): return {"gamma": enc(c[0]), "phis": [enc(x) for x in c[1:]]}
def same_group(d): return dec(d["encryptionGroup"]["p"]) == p and dec(d["encryptionGroup"]["q"]) == q and dec(d["encryptionGroup"]["g"]) == g
cks = {}

def shuffle(bb, step, C, Cp, pk, arg):
    N = len(C)
    if len(Cp) != N or N < 2: check(f"{bb} {step}: |C'| = |C| >= 2", False); return
    if len(arg["c_A"]) != 1: check(f"{bb} {step}: m = 1 (computation-optimized)", False); return
    if N not in cks: cks[N] = commitment_key(p, q, g, N)
    h, gs = cks[N]
    statements.append({"kind": "shuffle", "desc": f"{bb} {step} shuffle", "pk": [enc(x) for x in pk], "h": enc(h), "gs": [enc(x) for x in gs],
                       "C": [jct(c) for c in C], "Cp": [jct(c) for c in Cp], "argument": arg})

def decryptions(bb, step, C, Cd, pk, proofs, aux):
    if len(Cd) != len(C) or len(proofs) != len(C): check(f"{bb} {step}: |C_dec| = |pi| = |C|", False); return
    for i, (c, cd, pr) in enumerate(zip(C, Cd, proofs)):
        if cd[0] != c[0] or len(cd) != len(c): check(f"{bb} {step} decryption {i}: gamma' = gamma", False); continue
        statements.append({"kind": "decryption", "desc": f"{bb} {step} decryption {i}", "g": enc(g), "pk": [enc(x) for x in pk],
                           "ciphertext": jct(c), "message": [enc(x) for x in cd[1:]], "proof": pr, "aux": aux})

for box in sorted(glob.glob(os.path.join(tally, "*"))):
    bb = os.path.basename(box)
    ccbb = {j: load(os.path.join(box, f"controlComponentBallotBoxPayload_{j}.json")) for j in (1, 2, 3, 4)}
    ccsh = {j: load(os.path.join(box, f"controlComponentShufflePayload_{j}.json")) for j in (1, 2, 3, 4)}
    tsh = load(os.path.join(box, "tallyComponentShufflePayload.json"))
    tvo = load(os.path.join(box, "tallyComponentVotesPayload.json"))
    for name, d, node in [*[(f"CC {j} ballot box", ccbb[j], j) for j in ccbb], *[(f"CC {j} shuffle", ccsh[j], j) for j in ccsh],
                          ("tally shuffle", tsh, None), ("tally votes", tvo, None)]:
        check(f"{bb}: {name} payload: election event, ballot box{', node' if node else ''}, group",
              d["electionEventId"] == ee and d["ballotBoxId"] == bb and (node is None or d["nodeId"] == node) and ("encryptionGroup" not in d or same_group(d)))
    # GetMixnetInitialCiphertexts (6.1), from CC 1's view; every CC must hold the same confirmed votes
    views = {j: sorted((v["contextIds"]["verificationCardId"], tuple(ct(v["encryptedVote"]))) for v in ccbb[j]["confirmedEncryptedVotes"]) for j in ccbb}
    check(f"{bb}: the four control components hold the same confirmed votes", all(views[j] == views[1] for j in views))
    vcs = [vc for vc, _ in views[1]]
    check(f"{bb}: verification card IDs distinct", len(set(vcs)) == len(vcs))
    cinit = [list(c) for _, c in views[1]]
    delta = len(cinit[0]) - 1 if cinit else len(ct(ccsh[1]["verifiableShuffle"]["shuffledCiphertexts"][0])) - 1
    if len(cinit) < 2:
        cinit += [[g] + [x for x in EL[:delta]]] * 2   # GetCiphertext(1, 1, EL_pk)
    prev = cinit
    for j in (1, 2, 3, 4):
        s = ccsh[j]
        pk = EL if j == 1 else combine(*[ccm[k] for k in range(j, 5)], EB)
        cmix = [ct(c) for c in s["verifiableShuffle"]["shuffledCiphertexts"]]
        shuffle(bb, f"CC {j}", prev, cmix, pk, s["verifiableShuffle"]["shuffleArgument"])
        dd = s["verifiableDecryptions"]
        cdec = [ct(c) for c in dd["ciphertexts"]]
        decryptions(bb, f"CC {j}", cmix, cdec, ccm[j], dd["decryptionProofs"], [ee, bb, "MixDecOnline", str(j)])
        prev = cdec
    EBcut = EB[:delta]
    cmix5 = [ct(c) for c in tsh["verifiableShuffle"]["shuffledCiphertexts"]]
    shuffle(bb, "tally", prev, cmix5, EBcut, tsh["verifiableShuffle"]["shuffleArgument"])
    vp = tsh["verifiablePlaintextDecryption"]
    msgs = [[dec(x) for x in m["message"]] for m in vp["decryptedVotes"]]
    decryptions(bb, "tally", cmix5, [[c[0]] + m for c, m in zip(cmix5, msgs)], EBcut, vp["decryptionProofs"], [ee, bb, "MixDecOffline"])
    # the decrypted votes: the plaintexts other than the trivial 1s are, in order, the products
    # of the listed votes' encoded voting options (VerifyProcessPlaintexts, Algorithm 4.3, processes
    # m in order; the decoding to voting options and the write-ins are not checked here)
    nc = len(views[1])
    real = [m[0] for m in msgs if any(x != 1 for x in m)]
    listed = [eval_prod(v) for v in tvo["decryptedVotes"]]
    check(f"{bb}: decrypted plaintexts = products of the listed votes, in order (N_C = {nc})",
          real == listed and len(listed) == nc and len(msgs) == (nc if nc >= 2 else nc + 2))

json.dump({"p": enc(p), "q": enc(q), "g": enc(g), "statements": statements, "checks": checks}, open(out, "w"))
print(f"{len(statements)} statements ({sum(s['kind'] == 'shuffle' for s in statements)} shuffles), "
      f"{len(checks)} protocol checks, {sum(not c['ok'] for c in checks)} failed")
for c in checks:
    if not c["ok"]: print("  FAILED:", c["name"])
