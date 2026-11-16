#!/usr/bin/env python3
"""Generates the cases of the differential campaign (deterministically, from
the fixtures and SEED): every case is a complete, hash-consistent Belenios
archive, written to WORK/cases/STAGE/NAME.bel, with its expected verdict
(accept, reject, or either when the specification leaves it open) in
WORK/cases/manifest.tsv.

  honest   the five fixtures (belenios-tool's own elections), and the same
           elections rebuilt from ballots of our Python prover (an
           independent implementation of the specification; there is no
           certified Belenios prover in this repository), with the tally,
           partial decryptions and result recomputed with the trustees' keys
  field    one random occurrence of every field of every document, mutated by
           type (points, scalars, integers, strings); mutated ballots are
           re-signed with the voter's credential, so they reach the proof checks
  struct   archive events (dropped, duplicated, reordered), JSON shapes
           (extra, missing, reordered fields; vectors one short or long),
           encodings (number types, whitespace, case, leading zeros, non-canonical
           and off-curve and low-order points, out-of-range scalars)
  forge    single-check forgeries with controls: every other check is satisfied
           with valid proofs (built with the voters' credentials and the
           trustees' private keys), and only the targeted check can reject;
           and Fiat-Shamir binding: honest statements whose challenge is
           computed from a hash input with one component changed or dropped

usage: cases.py FIXTURES_DIR WORK_DIR [SEED]"""
import json, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from belenios_lib import *

FIX, WORK = sys.argv[1], sys.argv[2]
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 1
OUT = os.path.join(WORK, "cases")
manifest = []

def emit(stage, name, arch, expect, note=""):
    d = os.path.join(OUT, stage); os.makedirs(d, exist_ok=True)
    p = os.path.join(d, name + ".bel"); arch.save(p)
    manifest.append((stage, name, expect, note))

def jint(v): return v if v < 2**30 else str(v)   # Belenios's integers: JSON numbers below 2^30, else strings

class Fixture:
    def __init__(self, name):
        self.name = name
        d = os.path.join(FIX, name)
        self.arch = Archive.load(os.path.join(d, name + ".bel"))
        self.el = Election(self.arch)
        self.privcreds = [l.split()[1] for l in open(os.path.join(d, "private_creds.txt")) if l.strip()]
        self.secrets = {tostr(gpow(secret(self.el.uuid, c))): secret(self.el.uuid, c) for c in self.privcreds}
        self.trustee_x = [int(json.load(open(os.path.join(d, f)))) for f in sorted(os.listdir(d)) if f.endswith(".privkey")]
        self.x = sum(self.trustee_x) % L

    def ballots(self): return [b for _, b in self.el.ballots()]

    def plain(self, b):
        """the 0/1 votes of ballot b, decrypted with the election secret"""
        out = []
        for a in b["answers"]:
            vs = []
            for c in a["choices"]:
                M = sub(ofstr(c["beta"]), mul(self.x, ofstr(c["alpha"])))
                m, acc = 0, ZERO
                while not eq(acc, M) and m < 1000: m += 1; acc = add(acc, G)
                vs.append(m if m < 1000 else None)
            out.append(vs)
        return out

    def rebuild(self, rng, ballots=None, tally_ballots=None, weights=None, num_tallied=None, total_weight=None,
                result_edit=None, pd_edit=None, el=None, end=True, split=None):
        """a complete archive with the given ballots (dicts, in casting order), the tally of
        tally_ballots (default last(ballots)) with weights, valid partial decryptions and result"""
        el = el or self.el
        arch = self.arch.copy()
        ballots = self.ballots() if ballots is None else ballots
        evs = [ev for ev in arch.event_list() if ev["type"] == "Setup"]
        for k, b in enumerate(ballots):
            if split is not None and k == split: evs.append({"height": 0, "type": "EndBallots"})
            evs.append({"height": 0, "type": "Ballot", "payload": arch.add_data(compact(b))})
        if end:
            evs.append({"height": 0, "type": "EndBallots"})
            tb = last(ballots) if tally_ballots is None else tally_ballots
            w = weights or el.weights
            tally = encrypted_tally(el, tb, w)
            th = arch.add_data(compact(tally_json(tally)))
            hdr = {"num_tallied": len(tb) if num_tallied is None else num_tallied,
                   "total_weight": jint(sum(w.get(b["credential"], 1) for b in tb)) if total_weight is None else total_weight,
                   "encrypted_tally": th}
            evs.append({"height": 0, "type": "EncryptedTally", "payload": arch.add_data(compact(hdr))})
            pds = [partial_decryption(el, tally, xt, rng) for xt in self.trustee_x]
            if pd_edit: pds = pd_edit(pds)
            for t, pd in enumerate(pds):
                ph = arch.add_data(compact(pd))
                evs.append({"height": 0, "type": "PartialDecryption", "payload": arch.add_data(compact({"owner": t + 1, "payload": ph}))})
            res = [[0] * len(q) for q in tally]
            for b in tb:
                for i, vs in enumerate(self.plain(b)):
                    for j, m in enumerate(vs): res[i][j] += (m or 0) * w.get(b["credential"], 1)
            for i, q in enumerate(tally):   # sanity: g^res = beta / F
                for j, (_, beta) in enumerate(q):
                    F = ZERO
                    for xt in self.trustee_x: F = add(F, mul(xt, q[j][0]))
                    assert eq(gpow(res[i][j]), sub(beta, F))
            res = [[jint(v) for v in q] for q in res]
            if result_edit: res = result_edit(res)
            evs.append({"height": 0, "type": "Result", "payload": arch.add_data(compact({"result": res}))})
        for h, e in enumerate(evs): e["height"] = h
        arch.set_events(evs)
        return arch

    def resign(self, b, rng, hash_override=None):
        Prover(self.el, rng).sign(b, self.secrets[b["credential"]], hash_override)
        return b

FIXTURES = ["demo", "multi", "single", "empty", "complex"]
fx = {n: Fixture(n) for n in FIXTURES}

# ---------------- honest ----------------
def stage_honest():
    rng = random.Random(SEED * 1000 + 1)
    for n in FIXTURES:
        emit("honest", n, fx[n].arch, "accept", "belenios-tool election")
    for n in ["demo", "multi", "single"]:
        f = fx[n]; pr = Prover(f.el, rng)
        # the same voters, votes and revotes, re-cast with our prover
        cred_of = {tostr(gpow(s)): c for c, s in ((c, secret(f.el.uuid, c)) for c in f.privcreds)}
        bs = [pr.ballot(cred_of[b["credential"]], f.plain(b)) for b in f.ballots()]
        emit("honest", n + "-python-prover", f.rebuild(rng, bs), "accept", "ballots, tally, decryptions and result of our Python prover")
    # edge votes: every allowed blank / boundary vote of multi
    f = fx["multi"]; pr = Prover(f.el, rng)
    edge = [[[1, 0, 0, 0], [1, 0, 0, 0], [0, 0]], [[1, 1, 1, 0], [0, 1, 1, 0], [1, 1]], [[0, 0, 0, 1], [0, 0, 1, 1], [0, 1]]]
    bs = [pr.ballot(c, v) for c, v in zip(f.privcreds, edge)]
    emit("honest", "multi-edge-votes", f.rebuild(rng, bs), "accept", "minimum, maximum and blank votes")

# ---------------- field mutants ----------------
def is_point(s): return isinstance(s, str) and len(s) == 64 and all(ch in "0123456789abcdef" for ch in s)
def is_scalar(s): return isinstance(s, str) and s.isdigit() and len(s) > 20

def leaves(x, path=()):
    if isinstance(x, dict):
        for k, v in x.items(): yield from leaves(v, path + (k,))
    elif isinstance(x, list):
        for i, v in enumerate(x): yield from leaves(v, path + (i,))
    else:
        yield path, x
def get(x, path):
    for p in path: x = x[p]
    return x
def put(x, path, v): get(x, path[:-1])[path[-1]] = v
def field(path): return "/".join("[]" if isinstance(p, int) else p for p in path)

def point_ops(s, rng):
    p0 = ofstr(s)
    return [("other point", tostr(gpow(rng.randrange(1, L)))), ("negated", tostr(neg(p0))), ("generator", tostr(G)),
            ("identity", "%064x" % 1), ("order-2 point", "%064x" % (P - 1)),
            ("non-canonical identity", "%064x" % (1 + P)), ("off the curve", "%064x" % 2),
            ("upper-case hex", s.upper()), ("one digit short", s[1:])]
def scalar_ops(s, rng):
    v = int(s)
    return [("+1", str((v + 1) % L)), ("zero", "0"), ("l", str(L)), ("+l", str(v + L)), ("-1", "-1"),
            ("random", str(rng.randrange(L))), ("as a JSON number", v), ("leading zero", "0" + s)]
def int_ops(v):
    v = int(v)
    return [("+1", jint(v + 1)), ("-1", jint(v - 1) if v > 0 else -1), ("as a string", str(v)), ("huge", str(2**64 + v))]

def mutate_doc(f, kind, h, obj, rng, rebuild_ballot):
    """the mutants of one document: one random occurrence of each field, by type"""
    by = {}
    for path, v in leaves(obj):
        by.setdefault(field(path), []).append((path, v))
    for fl, occ in sorted(by.items()):
        path, v = rng.choice(occ)
        if is_point(v):
            try: ofstr(v); ops = point_ops(v, rng)
            except ValueError:   # a document reference (SHA-256 hex), not a point
                ops = [("dangling reference", "%064x" % rng.getrandbits(256)),
                       ("reference to another document", rng.choice([n[:64] for n, _ in f.arch.entries if n.endswith(".data.json") and n[:64] != v]))]
        elif is_scalar(v): ops = scalar_ops(v, rng)
        elif isinstance(v, int) and not isinstance(v, bool): ops = int_ops(v)
        elif isinstance(v, str) and v.isdigit(): ops = int_ops(v)
        elif isinstance(v, bool): ops = [("negated", not v)]
        elif isinstance(v, str): ops = [("changed", v + "x"), ("empty", "")]
        else: continue
        for opname, nv in ops:
            o = json.loads(json.dumps(obj)); put(o, path, nv)
            if o == obj: continue
            yield f"{kind} {fl} {opname}", o

def stage_field():
    rng = random.Random(SEED * 1000 + 2)
    for n, cap in [("demo", None), ("multi", None), ("single", None), ("complex", 40)]:
        f = fx[n]; a = f.arch
        docs = [("election", f.el.setup["election"]), ("trustees", f.el.setup["trustees"]), ("credentials", f.el.setup["credentials"])]
        bh = a.payloads("Ballot"); docs.append(("ballot", rng.choice(bh)))
        th = a.payloads("EncryptedTally")[0]; docs.append(("tally header", th)); docs.append(("encrypted tally", a.doc(th)["encrypted_tally"]))
        ph = rng.choice(a.payloads("PartialDecryption")); docs.append(("partial decryption header", ph)); docs.append(("partial decryption", a.doc(ph)["payload"]))
        docs.append(("result", a.payloads("Result")[0]))
        cases = []
        for kind, h in docs:
            obj = a.doc(h)
            for name, o in mutate_doc(f, kind, h, obj, rng, None):
                if kind == "ballot" and not name.startswith("ballot signature"):
                    # re-signed with the voter's credential (when the credential is unchanged)
                    if o["credential"] in f.secrets:
                        o2 = json.loads(json.dumps(o)); f.resign(o2, rng)
                        cases.append((name + " (re-signed)", h, o2))
                        continue
                cases.append((name, h, o))
        if cap: cases = rng.sample(cases, min(cap, len(cases)))
        for i, (name, h, o) in enumerate(cases):
            arch = a.copy(); arch.replace_data(h, compact(o))
            emit("field", f"{n}-{i:03d}", arch, "reject", name)

# ---------------- structure and encoding ----------------
def stage_struct():
    rng = random.Random(SEED * 1000 + 3)
    for n in ["demo", "multi", "single"]:
        f = fx[n]; a = f.arch; evs = a.event_list()
        def with_events(name, es, expect="reject"):
            arch = a.copy(); es = [dict(e) for e in es]
            for h, e in enumerate(es): e["height"] = h
            arch.set_events(es); emit("struct", f"{n}-{name}", arch, expect, name)
        types = [e["type"] for e in evs]
        ib = [i for i, t in enumerate(types) if t == "Ballot"]; ie = types.index("EndBallots")
        ip = [i for i, t in enumerate(types) if t == "PartialDecryption"]
        with_events("EndBallots dropped", evs[:ie] + evs[ie + 1:])
        with_events("a Ballot event duplicated", evs[:ie] + [evs[ib[0]]] + evs[ie:])
        with_events("a Ballot after EndBallots", evs[:ib[-1]] + evs[ib[-1] + 1:ie + 1] + [evs[ib[-1]]] + evs[ie + 1:])
        with_events("a PartialDecryption dropped", evs[:ip[0]] + evs[ip[0] + 1:])
        with_events("a PartialDecryption duplicated", evs[:ip[-1] + 1] + [evs[ip[-1]]] + evs[ip[-1] + 1:])
        with_events("Result dropped (an election in progress)", evs[:-1], "either")
        with_events("Result duplicated", evs + [evs[-1]])
        with_events("EncryptedTally before EndBallots", evs[:ie] + [evs[ie + 1], evs[ie]] + evs[ie + 2:])
        if len(ip) > 1:
            with_events("PartialDecryptions reordered", evs[:ip[0]] + [evs[i] for i in reversed(ip)] + evs[ip[-1] + 1:], "either")
        if len(f.ballots()) >= 2:
            k = len(f.ballots()) // 2
            arch = f.rebuild(rng, split=k, tally_ballots=last(f.ballots()[k:]))
            emit("struct", f"{n}-ballots before a second EndBallots left out of the tally", arch, "reject",
                 "an EndBallots event after the first ballots; the tally, decryptions and result cover the later ballots only")
            arch = f.rebuild(rng, split=k)
            emit("struct", f"{n}-a second EndBallots, every ballot tallied", arch, "either", "an EndBallots event after the first ballots; all ballots tallied")
        # ballots: JSON shapes and encodings, re-signed
        b0h = a.payloads("Ballot")[0]; b0 = a.doc(b0h)
        def ballot_case(name, edit, expect="reject", sign=True, raw=None):
            b = json.loads(json.dumps(b0)); edit(b)
            if sign: f.resign(b, rng)
            arch = a.copy(); arch.replace_data(b0h, raw(b) if raw else compact(b))
            emit("struct", f"{n}-ballot {name}", arch, expect, "ballot " + name)
        ballot_case("extra field", lambda b: b.update({"extra": 1}))
        ballot_case("answers: one answer short", lambda b: b["answers"].pop())
        ballot_case("answers: last duplicated", lambda b: b["answers"].append(b["answers"][-1]))
        ballot_case("choices: one short", lambda b: b["answers"][0]["choices"].pop())
        ballot_case("choices: last duplicated", lambda b: b["answers"][0]["choices"].append(b["answers"][0]["choices"][-1]))
        ballot_case("individual proofs: one short", lambda b: b["answers"][0]["individual_proofs"].pop())
        ballot_case("overall proof: one short", lambda b: b["answers"][0]["overall_proof"].pop())
        ballot_case("overall proof: last duplicated", lambda b: b["answers"][0]["overall_proof"].append(b["answers"][0]["overall_proof"][-1]))
        qb = [i for i, q in enumerate(f.el.questions) if q.get("blank")]
        qn = [i for i, q in enumerate(f.el.questions) if not q.get("blank")]
        if qb: ballot_case("blank question without blank_proof", lambda b: b["answers"][qb[0]].pop("blank_proof"))
        if qb and qn: ballot_case("blank_proof on a non-blank question", lambda b: b["answers"][qn[0]].__setitem__("blank_proof", b["answers"][qb[0]]["blank_proof"]))
        ballot_case("fields reordered (signature over the reordered body)",
                    lambda b: [b.__setitem__(k, b.pop(k)) for k in ["election_hash", "election_uuid", "credential", "answers"]], "either")
        ballot_case("signature field first", lambda b: None, "either", raw=lambda b: compact({"signature": b["signature"], **{k: v for k, v in b.items() if k != "signature"}}))
        ballot_case("pretty-printed (signature over the compact body)", lambda b: None, "either", raw=lambda b: json.dumps(b, indent=1).encode())
        ballot_case("challenge as a JSON number", lambda b: b["answers"][0]["individual_proofs"][0][0].__setitem__("challenge", int(b["answers"][0]["individual_proofs"][0][0]["challenge"])), "either")
        ballot_case("signature challenge as a JSON number", lambda b: b["signature"]["proof"].__setitem__("challenge", int(b["signature"]["proof"]["challenge"])), "either", sign=False)
        ballot_case("unicode escape in election_uuid", lambda b: None, "either", raw=lambda b: compact(b).replace(b'"election_uuid":"' + f.el.uuid[0].encode(), b'"election_uuid":"\\u00' + ("%02x" % ord(f.el.uuid[0])).encode()))
        ballot_case("signature hash with base64 padding", lambda b: b["signature"].__setitem__("hash", b["signature"]["hash"] + "="), "either", sign=False)
        # documents: credentials, trustees, result encodings
        def doc_case(name, h, edit, expect="reject"):
            o = a.doc(h); o2 = edit(json.loads(json.dumps(o)))
            if o2 == o: return
            arch = a.copy(); arch.replace_data(h, compact(o2)); emit("struct", f"{n}-{name}", arch, expect, name)
        doc_case("credentials: one duplicated", f.el.setup["credentials"], lambda c: c + [c[0]])
        doc_case("credentials: one removed", f.el.setup["credentials"], lambda c: c[1:])
        doc_case("trustees: one duplicated", f.el.setup["trustees"], lambda t: t + [t[0]])
        doc_case("result: one entry short", a.payloads("Result")[0], lambda r: {"result": [q[:-1] for q in r["result"]]})
        doc_case("result: numbers as strings", a.payloads("Result")[0], lambda r: {"result": [[str(v) for v in q] for q in r["result"]]}, "either")
        doc_case("result: extra field", a.payloads("Result")[0], lambda r: {**r, "extra": 0})

# ---------------- single-check forgeries and Fiat-Shamir binding ----------------
def stage_forge():
    rng = random.Random(SEED * 1000 + 4)
    for n in ["demo", "multi", "single", "empty"]:
        f = fx[n]; el = f.el; bs = f.ballots(); pr = Prover(el, rng)
        if not bs and n != "empty": continue
        cred0 = f.privcreds[0]; s0 = secret(el.uuid, cred0); C0 = tostr(gpow(s0))
        mine = [b for b in bs if b["credential"] == C0]
        def default_vote(q):   # blank if allowed, else the first max(min, 1) answers
            n = len(q["answers"])
            if q.get("blank"): return [1] + [0] * n
            k = max(q.get("min", 0), 1); return [1] * k + [0] * (n - k)
        vote0 = f.plain(mine[-1]) if mine else [default_vote(q) for q in el.questions]
        def pair(check, ctrl, forged, note=""):
            emit("forge", f"{n}-{check}-control", ctrl, "accept", check + " (control)" + note)
            emit("forge", f"{n}-{check}", forged, "reject", check + note)
        def with_ballot(b, extra=False):
            """the election with ballot b added as the last ballot (or replacing nothing)"""
            return f.rebuild(rng, bs + [b])
        # signature.hash must be the hash of the ballot: a valid signature on another ballot's hash
        good = pr.ballot(cred0, vote0); other = pr.ballot(cred0, vote0)
        forged = json.loads(json.dumps(good)); f.resign(forged, rng, hash_override=other["signature"]["hash"])
        pair("signature hash binds the ballot", with_ballot(good), with_ballot(forged))
        # election_hash and election_uuid fields (proofs made with the true fingerprint)
        g2 = pr.ballot(cred0, vote0, election_hash=sha256_b64(b"another election"))
        pair("ballot election_hash", with_ballot(pr.ballot(cred0, vote0)), with_ballot(g2))
        g3 = pr.ballot(cred0, vote0, uuid="aaaaaaaaaaaaaa")
        pair("ballot election_uuid", with_ballot(pr.ballot(cred0, vote0)), with_ballot(g3))
        # proofs made for another election's fingerprint (S0), with the true election_hash field
        g4 = pr.ballot(cred0, vote0, S0_fingerprint=sha256_b64(b"another election"))
        pair("proofs bind the election fingerprint", with_ballot(pr.ballot(cred0, vote0)), with_ballot(g4))
        # an unlisted credential, with a valid signature
        stranger = "zzzzz-zzzzzz-zzzzz-zzzzzz"
        g5 = pr.ballot(stranger, vote0)
        pair("credential is listed", with_ballot(pr.ballot(cred0, vote0)), f.rebuild(rng, bs + [g5], tally_ballots=last(bs)))
        # the encrypted tally: a ballot left out, with valid decryptions and result
        if len(last(bs)) >= 2:
            pair("encrypted tally = product of the tallied ballots", f.rebuild(rng), f.rebuild(rng, tally_ballots=last(bs)[1:]))
        # last(B): the first ballot of a revoting credential tallied instead of its last
        creds = [b["credential"] for b in bs]
        rev = [c for c in creds if creds.count(c) > 1]
        if rev:
            first = {}
            for b in bs: first.setdefault(b["credential"], b)
            tb = [first[b["credential"]] if b["credential"] == rev[0] else b for b in last(bs)]
            pair("only the last ballot of a credential is tallied", f.rebuild(rng), f.rebuild(rng, tally_ballots=tb))
            pair("every ballot of a revoting credential tallied", f.rebuild(rng), f.rebuild(rng, tally_ballots=last(bs) + [first[rev[0]]]))
        # weights
        if len(bs):
            w = dict(el.weights); c = last(bs)[0]["credential"]; w[c] = w[c] + 1
            pair("ballots weighted by their credential", f.rebuild(rng), f.rebuild(rng, weights=w))
            pair("num_tallied", f.rebuild(rng), f.rebuild(rng, num_tallied=len(last(bs)) + 1))
            tw = sum(el.weights.get(b["credential"], 1) for b in last(bs))
            pair("total_weight", f.rebuild(rng), f.rebuild(rng, total_weight=jint(tw + 1)))
            pair("result is the decryption", f.rebuild(rng), f.rebuild(rng, result_edit=lambda r: [[(int(v) + 1) if i == 0 and j == 0 else v for j, v in enumerate(q)] for i, q in enumerate(r)]))
        # partial decryptions: owners swapped (each valid for the other trustee's key)
        if len(f.trustee_x) > 1:
            pair("partial decryption owner", f.rebuild(rng), f.rebuild(rng, pd_edit=lambda pds: [pds[1], pds[0]] + pds[2:]))
        # a ballot without valid proofs or signature, counted: encrypts 5 for the first answer
        # (maximum 1), random proofs, a random signature (nobody but the voter knows the credential)
        def garbage_ballot(cred, votes):
            b = pr.ballot(cred, votes); r, (al, be) = pr.encrypt(5)
            b["answers"][0]["choices"][0] = {"alpha": tostr(al), "beta": tostr(be)}
            rnd = lambda: str(rng.randrange(L))
            for a_ in b["answers"]:
                for p_ in a_["individual_proofs"]:
                    for x_ in p_: x_["challenge"], x_["response"] = rnd(), rnd()
                for x_ in a_["overall_proof"] + a_.get("blank_proof", []): x_["challenge"], x_["response"] = rnd(), rnd()
            b["signature"]["proof"] = {"challenge": rnd(), "response": rnd()}
            return b
        voted = {b["credential"] for b in bs}
        idle = [c for c in f.privcreds if tostr(gpow(secret(el.uuid, c))) not in voted]
        if idle:
            emit("forge", f"{n}-ballot stuffing: invalid ballot for a voter who did not vote", f.rebuild(rng, bs + [garbage_ballot(idle[0], vote0)]), "reject",
                 "a ballot with random proofs and signature for a listed voter who did not vote, encrypting 5 for an answer with maximum 1, tallied")
        if bs:
            emit("forge", f"{n}-vote override: invalid ballot under a voter's credential", f.rebuild(rng, bs + [garbage_ballot(cred0, vote0)]), "reject",
                 "a later ballot under voter 1's credential with random proofs and signature, encrypting 5 for an answer with maximum 1; it replaces voter 1's vote in the tally")
        # Fiat-Shamir binding: an honest ballot whose first individual proof has its challenge
        # computed from a hash input with one component changed or dropped (re-signed)
        honest_tf = lambda S0, al, be, pts: ("prove|%s|%s,%s|" % (S0, tostr(al), tostr(be)), pts)
        variants = [("FS: individual proof hash without S0", lambda S0, al, be, pts: ("prove||%s,%s|" % (tostr(al), tostr(be)), pts)),
                    ("FS: individual proof hash without the ciphertext", lambda S0, al, be, pts: ("prove|%s||" % S0, pts)),
                    ("FS: individual proof hash with another credential", lambda S0, al, be, pts: ("prove|%s|%s|%s,%s|" % (el.fingerprint, tostr(G), tostr(al), tostr(be)), pts)),
                    ("FS: individual proof hash with the announcements reversed", lambda S0, al, be, pts: ("prove|%s|%s,%s|" % (S0, tostr(al), tostr(be)), list(reversed(pts))))]
        for name, tf in [("FS control", honest_tf)] + variants:
            b = fs_ballot(f, pr, cred0, vote0, tf)
            emit("forge", f"{n}-{name}", with_ballot(b), "accept" if tf is honest_tf else "reject", name)

def fs_ballot(f, pr, cred, votes, tf):
    """an honest ballot whose first individual proof (question 0, choice 0) has its challenge
    computed from the hash input tf(S0, alpha, beta, announcements) (re-signed)"""
    el = f.el; s = secret(el.uuid, cred); C = tostr(gpow(s)); S0 = el.fingerprint + "|" + C
    orig_iprove = pr.iprove
    calls = {"n": 0}
    def iprove(prefix_S, alpha, beta, r, i, Ms, y=None):
        calls["n"] += 1
        if calls["n"] != 1: return orig_iprove(prefix_S, alpha, beta, r, i, Ms, y)
        y = y or el.y; k = len(Ms); cs, rs, As, Bs = [0] * k, [0] * k, [None] * k, [None] * k
        for j in range(k):
            if j == i: continue
            cs[j], rs[j] = pr.rand(), pr.rand()
            As[j] = add(gpow(rs[j]), mul(cs[j], alpha)); Bs[j] = add(mul(rs[j], y), mul(cs[j], sub(beta, gpow(Ms[j]))))
        w = pr.rand(); As[i] = gpow(w); Bs[i] = mul(w, y)
        prefix, pts = tf(prefix_S, alpha, beta, [x for j in range(k) for x in (As[j], Bs[j])])
        h = hashq(prefix, pts)
        cs[i] = (h - sum(cs[j] for j in range(k) if j != i)) % L; rs[i] = (w - r * cs[i]) % L
        return [{"challenge": str(cs[j]), "response": str(rs[j])} for j in range(k)]
    pr.iprove = iprove
    try:
        return pr.ballot(cred, votes)
    finally:
        pr.iprove = orig_iprove

stage_honest(); stage_field(); stage_struct(); stage_forge()
os.makedirs(OUT, exist_ok=True)
with open(os.path.join(OUT, "manifest.tsv"), "w") as m:
    for row in manifest: m.write("\t".join(row) + "\n")
from collections import Counter
print(f"{len(manifest)} cases:", dict(Counter(s for s, *_ in manifest)))
