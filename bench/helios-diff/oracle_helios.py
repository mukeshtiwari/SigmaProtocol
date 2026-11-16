#!/usr/bin/env python3
"""The deployed-side verdicts: Helios's own verification code (algs.py and
electionalgs.py of the pinned helios-server, imported unmodified) applied to
an election file in the IACR bulletin-board format, component by component,
as the certified diff.exe reports them:

  ballots[i]  EncryptedVote.verify(election): one answer per question, the
              election hash and UUID, and for every choice the group
              membership (1 < alpha, beta < p - 1, order q) and the
              disjunctive 0/1 proof (max None: approval, no overall proof)
  pk          the product of the trustees' y is the election key
  decryption  Tally.verify_decryption_proofs for every trustee, on the
              Tally.add_vote aggregate of the valid ballots
  pok         EGPublicKey.verify_sk_proof for every trustee
  tally       Tally.decrypt_from_factors equals the published result
  final       pk and decryption and pok and tally

The election object (p, q, g, the election key, one question of n answers,
the election hash and UUID) comes from the case's spec; the trustees'
declared group parameters are not used, as in Helios. An exception in
Helios's code while aggregating, verifying or decrypting rejects the
election (the components concerned are false, the note says where).

usage: oracle_helios.py CASES.json OUT.jsonl [WORKERS]   (CASES: [{"file", "spec"}, ...])"""
import json, os, sys, types
from concurrent.futures import ProcessPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import helios_stub

A = E = None
def init():
    global A, E
    A, _ = helios_stub.load()
    E = helios_stub.load.electionalgs

def read(path):
    ballots, extra = [], []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                (extra if line.startswith(";") else ballots).append(line)
    return ballots, extra

def verify(case):
    spec, path = case["spec"], case["file"]
    out = {"file": path, "parse": "ok", "ballots": [], "pk": False, "decryption": False, "pok": False, "tally": False, "final": False}
    ballot_lines, extra = read(path)
    pk = A.EGPublicKey()
    pk.p, pk.q, pk.g, pk.y = int(spec["p"]), int(spec["q"]), int(spec["g"]), int(spec["h"])
    n = int(spec["n"])
    election = types.SimpleNamespace(questions=[{"answers": ["a%d" % i for i in range(n)], "max": None, "min": 0}],
                                     hash=spec["election_hash"], uuid=spec["election_uuid"], public_key=pk)
    tally = E.Tally(election=election)
    note = []
    for line in ballot_lines:
        try:
            ev = E.EncryptedVote.fromJSONDict(json.loads(line)["vote"], pk)
            ok = ev.verify(election)
        except Exception as e:
            ok = False
        out["ballots"].append(bool(ok))
        if ok:
            try:
                tally.add_vote(ev, verify_p=False)
            except Exception as e:
                note.append("Tally.add_vote: %s" % type(e).__name__)
    try:
        trustees = json.loads(extra[0][1:])
        result = json.loads(extra[1][1:])
        y = 1
        for t in trustees: y = y * int(t["public_key"]["y"]) % pk.p
        out["pk"] = (y == pk.y)
        dec_ok = pok_ok = True
        for t in trustees:
            tpk = A.EGPublicKey(); tpk.p, tpk.q, tpk.g, tpk.y = pk.p, pk.q, pk.g, int(t["public_key"]["y"])
            pok = t["pok"]
            if not tpk.verify_sk_proof(A.DLogProof(int(pok["commitment"]), int(pok["challenge"]), int(pok["response"])),
                                       A.DLog_challenge_generator):
                pok_ok = False
            if not tally.verify_decryption_proofs(t["decryption_factors"], t["decryption_proofs"], tpk, A.EG_fiatshamir_challenge_generator):
                dec_ok = False
        out["decryption"], out["pok"] = dec_ok and not note, pok_ok
        # Helios's models hand the factors to decrypt_from_factors as integers (the stored JSON has strings)
        factors = [[[int(f) for f in q] for q in t["decryption_factors"]] for t in trustees]
        out["tally"] = not note and tally.decrypt_from_factors(factors, pk) == result
    except Exception as e:
        note.append("trustees/result: %s" % type(e).__name__)
        out["decryption"] = out["tally"] = False
    if note: out["parse"] = "; ".join(note)
    out["final"] = out["pk"] and out["decryption"] and out["pok"] and out["tally"]
    return out

if __name__ == "__main__":
    cases = json.load(open(sys.argv[1]))
    with ProcessPoolExecutor(int(sys.argv[3]) if len(sys.argv) > 3 else 4, initializer=init) as ex:
        res = list(ex.map(verify, cases, chunksize=4))
    with open(sys.argv[2], "w") as f:
        for r in res: f.write(json.dumps(r, sort_keys=True) + "\n")
