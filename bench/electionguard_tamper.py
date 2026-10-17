#!/usr/bin/env python3
"""Tamper with a copy of an ElectionGuard 2.0 JSON election record and run
the certified verifier on each copy; every copy must be rejected.

Usage: bench/electionguard_tamper.py RECORD_DIRECTORY [VERIFIER [TAMPER,...]]
"""
import json, os, shutil, subprocess, sys, tempfile

record = sys.argv[1]
verifier = sys.argv[2] if len(sys.argv) > 2 else "_build/default/src/Executable/Egverifier/main.exe"
only = sys.argv[3].split(",") if len(sys.argv) > 3 else None   # names of the tampers to run

def load(d, f): return json.load(open(os.path.join(d, f)))
def save(d, f, obj): json.dump(obj, open(os.path.join(d, f), "w"), indent=2)
def first_ballot(d):
    sub = os.path.join(d, "encrypted_ballots")
    for dev in sorted(os.listdir(sub)):
        for f in sorted(os.listdir(os.path.join(sub, dev))):
            if f.endswith(".json"): return os.path.join("encrypted_ballots", dev, f)
def flip_hex(h):
    """change the last hex digit, keeping the value in range"""
    last = h[-1]
    return h[:-1] + ("1" if last != "1" else "2")

def t_range_response(d):
    f = first_ballot(d); b = load(d, f)
    pf = b["contests"][0]["selections"][0]["proof"]["proofs"][1]
    pf["response"] = flip_hex(pf["response"]); save(d, f, b)
def t_range_challenge(d):
    f = first_ballot(d); b = load(d, f)
    pf = b["contests"][0]["selections"][1]["proof"]["proofs"][0]
    pf["challenge"] = flip_hex(pf["challenge"]); save(d, f, b)
def t_limit_proof(d):
    f = first_ballot(d); b = load(d, f)
    pf = b["contests"][1]["proof"]["proofs"][0]
    pf["response"] = flip_hex(pf["response"]); save(d, f, b)
def t_swap_selections(d):
    """swap two encrypted options (their proofs stay valid; the contest hash changes)"""
    f = first_ballot(d); b = load(d, f)
    s = b["contests"][0]["selections"]
    s[0]["encrypted_vote"], s[1]["encrypted_vote"] = s[1]["encrypted_vote"], s[0]["encrypted_vote"]
    s[0]["proof"], s[1]["proof"] = s[1]["proof"], s[0]["proof"]
    save(d, f, b)
def t_guardian_proof(d):
    i = load(d, "election_initialized.json")
    pf = i["guardians"][0]["coefficient_proofs"][1]
    pf["response"] = flip_hex(pf["response"]); save(d, "election_initialized.json", i)
def t_encrypted_tally(d):
    """replace one aggregate by another one (a valid group element)"""
    t = load(d, "encrypted_tally.json")
    s = t["contests"][0]["selections"]
    s[0]["encrypted_vote"]["pad"] = s[1]["encrypted_vote"]["pad"]; save(d, "encrypted_tally.json", t)
def t_decryption_proof(d):
    t = load(d, "tally.json")
    pf = t["contests"][0]["selections"][0]["proof"]
    pf["challenge"] = flip_hex(pf["challenge"]); save(d, "tally.json", t)
def t_decrypted_value(d):
    t = load(d, "tally.json")
    s = t["contests"][0]["selections"][0]
    s["tally"] = s["tally"] + 1; save(d, "tally.json", t)
def t_uncast_ballot(d):
    """a cast ballot marked as challenged is left out of the tally"""
    f = first_ballot(d); b = load(d, f)
    b["state"] = "CHALLENGED"; save(d, f, b)
def t_duplicate_ballot(d):
    f = first_ballot(d)
    shutil.copy(os.path.join(d, f), os.path.join(d, os.path.dirname(f), "eballot-copy.json"))

tampers = [t_range_response, t_range_challenge, t_limit_proof, t_swap_selections, t_guardian_proof,
           t_encrypted_tally, t_decryption_proof, t_decrypted_value, t_uncast_ballot, t_duplicate_ballot]
ok = True
for t in tampers:
    if only and t.__name__ not in only: continue
    with tempfile.TemporaryDirectory() as tmp:
        d = os.path.join(tmp, "record"); shutil.copytree(record, d)
        t(d)
        r = subprocess.run([verifier, d], capture_output=True, text=True)
        verdict = [l for l in r.stdout.splitlines() if "verified =" in l]
        rejected = r.returncode != 0
        print("%-22s rejected=%s  %s" % (t.__name__, rejected, verdict[0] if verdict else r.stdout.strip().splitlines()[-1:]))
        ok = ok and rejected
print("all tampered records rejected:", ok)
sys.exit(0 if ok else 1)
