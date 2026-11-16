#!/usr/bin/env python3
"""Protocol-level tampering of the Swiss Post synthetic election Post_E2E_DEV,
checked with the Swiss Post Verifier (VerifierCli.java, run_verifier.sh).

Each scenario edits a copy of the dataset (DATASET/D2/context,
DATASET/D3/{context,tally}), re-signs every payload it changed with the dev
key of the component that signs it (Tamper.java resign: the signatures of
the e-voting system, computed with its own domain classes), and runs the tally
verifications. Re-signing is what makes the attacks meaningful: a tampered
payload with a stale signature only tests the signature check. The control
scenarios re-sign unchanged payloads and must be accepted.

usage: tamper.py TESTDATA VERIFIER_CHECKOUT ORIGINAL_DATASET OUT_DIR [SCENARIO ...]
  writes OUT_DIR/<scenario>/ and OUT_DIR/manifest.json; needs JAVA_HOME = a JDK 25"""
import copy, json, os, random, re, shutil, subprocess, sys

testdata, verifier, original, out = map(os.path.abspath, sys.argv[1:5])
only = sys.argv[5:]
here = os.path.dirname(os.path.abspath(__file__))
java = os.path.join(os.environ["JAVA_HOME"], "bin", "java")
backend = os.path.join(verifier, "verifier-backend")
cp = f"{backend}/target/cli-classes:{backend}/target/classes:" + open(f"{backend}/cp.txt").read().strip()
rng = random.Random(1)

BB = "D3/tally/ballotBoxes"
BIG, SMALL = "9BDDA72166C38804716E38692DC5D9C1", "F65273320ACFE925B2617AA1AE52A550"   # 4 votes (2 write-ins), 3 votes
ONE, EMPTY = "0100B651C06A0EE6369B3E9102B8726D", "2599320309C96B2ACE2B4641960B088D"   # 1 vote, 0 votes

def p(bb, name): return f"{BB}/{bb}/{name}"
def load(d, rel): return json.load(open(os.path.join(d, rel)))
def save(d, rel, x): json.dump(x, open(os.path.join(d, rel), "w"), indent="\t")
def ech(d): return next(f"D3/tally/{f}" for f in os.listdir(os.path.join(d, "D3/tally")) if f.startswith("eCH-0222"))
CCB = lambda j: f"controlComponentBallotBoxPayload_{j}.json"
CCS = lambda j: f"controlComponentShufflePayload_{j}.json"
TCS, TCV = "tallyComponentShufflePayload.json", "tallyComponentVotesPayload.json"

def b64_add1(s, q):
    import base64
    v = (int.from_bytes(base64.b64decode(s), "big") + 1) % q
    return base64.b64encode(v.to_bytes(v.bit_length() // 8 + 1, "big")).decode()
def q_of(d, rel):
    import base64
    return int.from_bytes(base64.b64decode(load(d, rel)["encryptionGroup"]["q"]), "big")

# ---- scenarios: each edits directory d and returns the files to re-sign ----
S = {}
def scenario(name, desc, expect="reject"):
    def reg(f): S[name] = (desc, expect, f); return f
    return reg

@scenario("control-resign-unchanged", "every tally payload of one ballot box and the eCH-0222 file re-signed unchanged", "accept")
def _(d):
    return [p(BIG, f) for f in [CCB(j) for j in range(1, 5)] + [CCS(j) for j in range(1, 5)] + [TCS, TCV]] + [ech(d)]

@scenario("control-stale-signature", "a decoded vote changed WITHOUT re-signing: the signature check must catch it")
def _(d):
    x = load(d, p(BIG, TCV))
    i, j = next((i, j) for i in range(len(x["decodedVotes"])) for j in range(len(x["decodedVotes"])) if x["decodedVotes"][i] != x["decodedVotes"][j])
    x["decodedVotes"][i] = copy.deepcopy(x["decodedVotes"][j]); save(d, p(BIG, TCV), x)
    return []

@scenario("swap-ballot-box-folders", "the directories of two ballot boxes exchanged (contents untouched)")
def _(d):
    a, b = os.path.join(d, BB, BIG), os.path.join(d, BB, SMALL)
    os.rename(a, a + ".tmp"); os.rename(b, a); os.rename(a + ".tmp", b)
    return []

@scenario("swap-ballot-box-contents", "two ballot boxes exchanged, every ballotBoxId rewritten and every payload re-signed")
def _(d):
    a, b = os.path.join(d, BB, BIG), os.path.join(d, BB, SMALL)
    os.rename(a, a + ".tmp"); os.rename(b, a); os.rename(a + ".tmp", b)
    files = []
    for box in (BIG, SMALL):
        for f in [CCB(j) for j in range(1, 5)] + [CCS(j) for j in range(1, 5)] + [TCS, TCV]:
            x = load(d, p(box, f)); x["ballotBoxId"] = box
            save(d, p(box, f), x); files.append(p(box, f))
    return files

@scenario("cc-node-swap", "the shuffle payloads of control components 2 and 3 exchanged, nodeIds rewritten, re-signed with the swapped keys")
def _(d):
    x2, x3 = load(d, p(BIG, CCS(2))), load(d, p(BIG, CCS(3)))
    x2["nodeId"], x3["nodeId"] = 3, 2
    save(d, p(BIG, CCS(3)), x2); save(d, p(BIG, CCS(2)), x3)
    return [p(BIG, CCS(2)), p(BIG, CCS(3))]

@scenario("cc-shuffle-from-other-box", "control component 2's shuffle payload replaced by the one of another ballot box, relabelled and re-signed")
def _(d):
    x = load(d, p(SMALL, CCS(2))); x["ballotBoxId"] = BIG
    save(d, p(BIG, CCS(2)), x)
    return [p(BIG, CCS(2))]

@scenario("cc-shuffle-other-election", "control component 1's shuffle payload relabelled to another election event id, re-signed for it")
def _(d):
    x = load(d, p(SMALL, CCS(1))); x["electionEventId"] = "%032X" % rng.getrandbits(128)
    save(d, p(SMALL, CCS(1)), x)
    return [p(SMALL, CCS(1))]

def edit_confirmed(d, box, nodes, f):
    files = []
    for j in nodes:
        x = load(d, p(box, CCB(j))); x["confirmedEncryptedVotes"] = f(x["confirmedEncryptedVotes"])
        save(d, p(box, CCB(j)), x); files.append(p(box, CCB(j)))
    return files

@scenario("drop-confirmed-vote-all-cc", "a confirmed vote removed from the ballot box payloads of all four control components")
def _(d): return edit_confirmed(d, BIG, range(1, 5), lambda vs: vs[1:])

@scenario("duplicate-confirmed-vote-all-cc", "a confirmed vote duplicated in the ballot box payloads of all four control components")
def _(d): return edit_confirmed(d, BIG, range(1, 5), lambda vs: vs + [copy.deepcopy(vs[0])])

@scenario("drop-confirmed-vote-one-cc", "a confirmed vote removed from control component 2's ballot box payload only")
def _(d): return edit_confirmed(d, BIG, [2], lambda vs: vs[1:])

@scenario("foreign-confirmed-vote-all-cc", "a confirmed vote of another ballot box added to all four ballot box payloads")
def _(d):
    other = load(d, p(SMALL, CCB(1)))["confirmedEncryptedVotes"][0]
    return edit_confirmed(d, BIG, range(1, 5), lambda vs: vs + [copy.deepcopy(other)])

@scenario("reorder-confirmed-votes-all-cc", "the confirmed votes reversed in all four ballot box payloads (same set, other order); "
          "GetMixnetInitialCiphertexts (System Specification, Algorithm 6.1) orders them by verification card id, so this changes nothing", "accept")
def _(d): return edit_confirmed(d, BIG, range(1, 5), lambda vs: vs[::-1])

@scenario("votes-decoded-changed", "one decoded vote of the tally component's votes payload replaced by another voter's (decrypted primes unchanged)")
def _(d):
    x = load(d, p(BIG, TCV))
    i, j = next((i, j) for i in range(len(x["decodedVotes"])) for j in range(len(x["decodedVotes"])) if x["decodedVotes"][i] != x["decodedVotes"][j])
    x["decodedVotes"][i] = copy.deepcopy(x["decodedVotes"][j])
    save(d, p(BIG, TCV), x); return [p(BIG, TCV)]

@scenario("votes-vote-replaced", "one vote of the votes payload replaced by another voter's, consistently (primes, decoded votes, write-ins)")
def _(d):
    x = load(d, p(BIG, TCV))
    i, j = next((i, j) for i in range(len(x["decodedVotes"])) for j in range(len(x["decodedVotes"])) if x["decodedVotes"][i] != x["decodedVotes"][j])
    for k in ("decryptedVotes", "decodedVotes", "decodedWriteIns"): x[k][i] = copy.deepcopy(x[k][j])
    save(d, p(BIG, TCV), x); return [p(BIG, TCV)]

@scenario("votes-dropped", "one vote removed from the votes payload (primes, decoded votes, write-ins)")
def _(d):
    x = load(d, p(BIG, TCV))
    for k in ("decryptedVotes", "decodedVotes", "decodedWriteIns"): x[k] = x[k][1:]
    save(d, p(BIG, TCV), x); return [p(BIG, TCV)]

@scenario("votes-reordered", "the votes of the votes payload reversed (same multiset, other order than the decryptions)")
def _(d):
    x = load(d, p(BIG, TCV))
    for k in ("decryptedVotes", "decodedVotes", "decodedWriteIns"): x[k] = x[k][::-1]
    save(d, p(BIG, TCV), x); return [p(BIG, TCV)]

@scenario("votes-write-in-changed", "a decoded write-in of the votes payload changed")
def _(d):
    x = load(d, p(BIG, TCV))
    i = next(i for i, w in enumerate(x["decodedWriteIns"]) if w)
    x["decodedWriteIns"][i][0] = "Mallory Muster"
    save(d, p(BIG, TCV), x); return [p(BIG, TCV)]

@scenario("votes-write-in-added", "a write-in added to a vote of the votes payload that has a write-in slot left empty")
def _(d):
    x = load(d, p(BIG, TCV))
    i = next(i for i, w in enumerate(x["decodedWriteIns"]) if not w)
    x["decodedWriteIns"][i] = ["Mallory Muster"]
    save(d, p(BIG, TCV), x); return [p(BIG, TCV)]

@scenario("tally-plaintexts-swapped", "two decrypted votes of the tally component's shuffle payload exchanged (proofs untouched)")
def _(d):
    x = load(d, p(BIG, TCS)); m = x["verifiablePlaintextDecryption"]["decryptedVotes"]; m[0], m[1] = m[1], m[0]
    save(d, p(BIG, TCS), x); return [p(BIG, TCS)]

@scenario("tally-plaintexts-and-votes-swapped", "two decrypted votes exchanged in the tally shuffle payload and in the votes payload consistently")
def _(d):
    x = load(d, p(BIG, TCS)); m = x["verifiablePlaintextDecryption"]["decryptedVotes"]; m[0], m[1] = m[1], m[0]
    save(d, p(BIG, TCS), x)
    v = load(d, p(BIG, TCV))
    for k in ("decryptedVotes", "decodedVotes", "decodedWriteIns"): v[k][0], v[k][1] = v[k][1], v[k][0]
    save(d, p(BIG, TCV), v); return [p(BIG, TCS), p(BIG, TCV)]

@scenario("shuffle-argument-field", "control component 2's shuffle argument: multi-exponentiation response r + 1")
def _(d):
    x = load(d, p(BIG, CCS(2))); me = x["verifiableShuffle"]["shuffleArgument"]["multiExponentiationArgument"]
    me["r"] = b64_add1(me["r"], q_of(d, p(BIG, CCS(2))))
    save(d, p(BIG, CCS(2)), x); return [p(BIG, CCS(2))]

@scenario("decryption-proof-field", "control component 3's decryption proof of vote 0: response z_0 + 1")
def _(d):
    x = load(d, p(BIG, CCS(3))); z = x["verifiableDecryptions"]["decryptionProofs"][0]["z"]
    z[0] = b64_add1(z[0], q_of(d, p(BIG, CCS(3))))
    save(d, p(BIG, CCS(3)), x); return [p(BIG, CCS(3))]

@scenario("tally-reshuffle-fresh-key", "the tally component's mix-decryption redone: a valid new shuffle of the true input, decrypted under a fresh key with valid proofs for that key")
def _(d):
    run_tamper("remix", testdata, d, BIG, "wrong-key-all")
    return []

@scenario("cc-shuffle-missing", "control component 3's shuffle payload of a ballot box deleted")
def _(d):
    os.remove(os.path.join(d, p(BIG, CCS(3)))); return []

def ech_edit(d, f):
    path = os.path.join(d, ech(d)); x = open(path, encoding="utf-8").read(); open(path, "w", encoding="utf-8").write(f(x)); return [ech(d)]
BALLOT = re.compile(r"<eCH-0222:ballotRawData>.*?</eCH-0222:ballotRawData>", re.S)

@scenario("ech0222-answer-changed", "eCH-0222: the answer of one ballot changed to another answer of the same question")
def _(d):
    def f(x):
        ballots = BALLOT.findall(x)
        ans = lambda b: re.findall(r"<eCH-0155:answerIdentification>([^<]+)</eCH-0155:answerIdentification>", b)
        ids = sorted({a for b in ballots for a in ans(b)})
        b0 = ballots[0]; a0 = ans(b0)[0]; other = next(a for a in ids if a != a0)
        return x.replace(b0, b0.replace(a0, other, 1), 1)
    return ech_edit(d, f)

@scenario("ech0222-ballot-dropped", "eCH-0222: one ballot removed")
def _(d): return ech_edit(d, lambda x: x.replace(BALLOT.findall(x)[0], "", 1))

@scenario("ech0222-ballot-duplicated", "eCH-0222: one ballot duplicated")
def _(d): return ech_edit(d, lambda x: x.replace(BALLOT.findall(x)[0], BALLOT.findall(x)[0] * 2, 1))

@scenario("ech0222-voting-cards-count", "eCH-0222: countOfReceivedInvalidVotingCardsTotal changed from 0 to 1")
def _(d): return ech_edit(d, lambda x: x.replace("countOfReceivedInvalidVotingCardsTotal>0<", "countOfReceivedInvalidVotingCardsTotal>1<", 1))

@scenario("control-ech0222-resign", "eCH-0222 re-signed unchanged", "accept")
def _(d): return [ech(d)]

# ---- running ----
def run_tamper(*args):
    r = subprocess.run([java, "-cp", cp, "ch.post.it.evoting.verifier.backend.tamper.Tamper", *args], capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError((r.stdout + r.stderr)[-1500:])
    return r.stdout

def verify(d):
    r = subprocess.run([os.path.join(here, "run_verifier.sh"), verifier, testdata, d, "tally"], capture_output=True, text=True,
                       env=dict(os.environ))
    rows = [l.split("\t") for l in r.stdout.splitlines() if l.startswith("tally\t")]
    failed = [f"{x[1]} {x[3]} ({x[2]}){': ' + x[4][:160] if len(x) > 4 and x[4] else ''}" for x in rows if x[2] != "OK"]
    if not rows:
        failed = ["no verification ran: " + (r.stdout + r.stderr)[-300:]]
    return ("accept" if r.returncode == 0 and rows else "reject"), failed

os.makedirs(out, exist_ok=True)
manifest = []
for name, (desc, expect, f) in S.items():
    if only and name not in only: continue
    d = os.path.join(out, name)
    shutil.rmtree(d, ignore_errors=True); shutil.copytree(original, d)
    note = []
    files = f(d)
    if files:
        try:
            run_tamper("resign", testdata, d, *files)
        except Exception as e:
            # the domain classes refuse to build such a payload, so no component can sign it; the
            # Verifier reads payloads with the same classes: it runs on the edited, unsigned files
            msg = next((l for l in str(e).splitlines() if "Exception:" in l and "jackson" not in l), str(e).splitlines()[-1])
            note = [f"re-signing refused by the e-voting domain classes ({msg.strip()[:200]}); Verifier run on the unsigned edit"]
    verdict, failed = verify(d)
    failed = note + failed
    entry = {"name": name, "description": desc, "changed_files": files, "expected": expect,
             "verifier_verdict": verdict, "verifier_failed_steps": failed}
    manifest.append(entry)
    print(f"{'ok ' if verdict == expect else 'UNEXPECTED'}  {name:36} {verdict:6} {'; '.join(failed)[:200]}", flush=True)
json.dump(manifest, open(os.path.join(out, "manifest.json"), "w"), indent=2)
print(f"{len(manifest)} scenarios, {sum(e['verifier_verdict'] != e['expected'] for e in manifest)} unexpected")
