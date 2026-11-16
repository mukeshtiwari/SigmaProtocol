#!/usr/bin/env python3
"""Differential-testing campaign: the certified ElectionGuard 2.0 verifier
(src/Executable/Egverifier) against the verifier of the reference
implementation electionguard-kotlin-multiplatform (egk, RunVerifier), on
every case of four sources, each verdict of both recorded:

  1 honest     the fixture elections made with egk (gen_elections.sh) and
               egk's own test records
  2 field      one random occurrence of every field of every file of a
               record, mutated by type: elements of Z_p^r (times g, 1,
               inverse, random, swapped with a sibling), elements of Z_q
               (+1, 0, negated, random), hashes and byte strings (last digit
               changed, zero), integers (+1, 0), strings, booleans
  3 structure  encodings (lower case, leading zeros, wider), values outside
               the group or Z_q, lists one element short or long, a missing
               or an extra field, a field of the wrong type, ballot states,
               duplicated and replayed ballots
  4 forgery    each with a control built the same way with honest values:
               ballots of our prover (eglib.py) with Fiat–Shamir-consistent
               cheating range and selection-limit proofs, counted in a tally
               validly decrypted by the trustees; the base hashes H_P, H_M,
               H_B, H_E replaced by values that every later hash and proof
               of egk's own pipeline consistently uses; tallies that are not
               the product of the cast ballots, validly decrypted; and, on
               egk's chained record, ballots removed from, reordered in or
               left out of the confirmation chain

Every random choice of the script comes from --seed; egk's own encryptions
and proofs use SecureRandom, so the files differ between runs but not the
verdicts. Writes OUT/summary.tsv (one line per case) and OUT/details.tsv.

usage: campaign.py --jar EGK_ALL_JAR --java JAVA --ours MAIN_EXE --fixtures DIR --egk-data DIR --work DIR --out DIR [--seed N] [--jobs N] [--sources 1234]"""
import argparse, collections, concurrent.futures, copy, glob, json, os, random, re, shutil, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import eglib
from eglib import ip, hx, load

ap = argparse.ArgumentParser()
for a in ("--jar", "--java", "--ours", "--fixtures", "--egk-data", "--work", "--out"): ap.add_argument(a, required=True)
ap.add_argument("--seed", type=int, default=1); ap.add_argument("--jobs", type=int, default=4); ap.add_argument("--sources", default="1234")
A = ap.parse_args()
rng = random.Random(A.seed)
os.makedirs(A.work, exist_ok=True); os.makedirs(A.out, exist_ok=True)
CASES = os.path.join(A.work, "cases")
shutil.rmtree(CASES, ignore_errors=True); os.makedirs(CASES)

# ---------------------------------------------------------------- bases
# the generated fixtures, and egk's own workflow records (with their private data)
BASES = {n: os.path.join(A.fixtures, n) for n in ("small", "quorum", "multi", "medium", "chained-batch")}
for n in ("allAvailableJson", "someAvailableJson", "chainedJson"):
    BASES["egk-" + n] = os.path.join(A.egk_data, n)
MISSING = {"quorum": "2,4", "egk-someAvailableJson": None}   # missing guardians at tally decryption
def missing_of(base):
    if base in MISSING and MISSING[base]: return MISSING[base]
    return None

def save(path, obj): json.dump(obj, open(path, "w"), indent=2)
def public_copy(src, dst):
    """the published record: everything but private_data"""
    shutil.copytree(src, dst, ignore=shutil.ignore_patterns("private_data"))
    return dst

cases = []   # dicts: name, source, base, expected, dir
def add(name, source, base, expected, d, note=""):
    cases.append({"name": name, "source": source, "base": base, "expected": expected, "dir": d, "note": note})

def new_case(name, base):
    d = os.path.join(CASES, re.sub(r"[^A-Za-z0-9_.+-]", "_", name))
    return public_copy(BASES[base], d)

# ---------------------------------------------------------------- egk tools
def egk(*args):
    """an egk command-line program; its success is judged by the files it writes"""
    return subprocess.run([A.java, "-classpath", A.jar, *args], capture_output=True, text=True, cwd=A.work)   # egk writes egkServer.log into its cwd

SKIPPED = []   # (case, reason): cases whose construction failed in egk's tools

def trustees(base): return os.path.join(BASES[base], "private_data", "trustees")

def decrypt_tally(rec, base, trustee_dir=None):
    for f in glob.glob(os.path.join(rec, "tally.json")): os.remove(f)
    args = ["electionguard.cli.RunTrustedTallyDecryption", "-in", rec, "-trustees", trustee_dir or trustees(base), "-out", rec]
    if missing_of(base): args += ["-missing", missing_of(base)]
    egk(*args)
    if not os.path.exists(os.path.join(rec, "tally.json")): raise RuntimeError("egk wrote no tally.json in " + rec)

def decrypt_challenged(rec, base, trustee_dir=None):
    shutil.rmtree(os.path.join(rec, "challenged_ballots"), ignore_errors=True)
    egk("electionguard.cli.RunTrustedBallotDecryption", "-in", rec, "-trustees", trustee_dir or trustees(base), "-out", rec, "-nthreads", "1")

def ballot_files(rec): return eglib.ballots(rec)

def recompute_encrypted_tally(rec, include=lambda b: b["state"] == "CAST", extra=None):
    """the encrypted tally as the product of the ballots selected by include;
    extra: (contest index, selection index, (a, b)) multiplied into it"""
    G = eglib.Group(rec); p = G.p
    et = load(os.path.join(rec, "encrypted_tally.json"))
    prod = {}
    ids = []
    for f in ballot_files(rec):
        b = load(f)
        if not include(b): continue
        ids.append(b["ballot_id"])
        for c in b["contests"]:
            for s in c["selections"]:
                k = (c["contest_id"], s["selection_id"]); a, bb = prod.get(k, (1, 1))
                prod[k] = (a * ip(s["encrypted_vote"]["pad"]) % p, bb * ip(s["encrypted_vote"]["data"]) % p)
    for ci, c in enumerate(et["contests"]):
        for si, s in enumerate(c["selections"]):
            a, bb = prod.get((c["contest_id"], s["selection_id"]), (1, 1))
            if extra and extra[0] == ci and extra[1] == si:
                a, bb = a * extra[2][0] % p, bb * extra[2][1] % p
            s["encrypted_vote"] = {"pad": hx(a, 512), "data": hx(bb, 512)}
    et["cast_ballot_ids"] = ids
    save(os.path.join(rec, "encrypted_tally.json"), et)

# ---------------------------------------------------------------- source 1: honest
if "1" in A.sources:
    for b in BASES:
        if b == "chained-batch": continue   # a protocol case (source 4)
        add(f"honest {b}", "1-honest", b, "accept", new_case(f"honest-{b}", b))

# ---------------------------------------------------------------- source 2: field mutants
P_KEYS = None
def leaves(x, path=()):
    if isinstance(x, dict):
        for k, v in x.items(): yield from leaves(v, path + (k,))
    elif isinstance(x, list):
        if x and all(isinstance(v, int) and not isinstance(v, bool) for v in x) and len(x) > 4:
            yield path, "bytes-list"   # baux0
            return
        for i, v in enumerate(x): yield from leaves(v, path + (i,))
    else:
        yield path, kind_of(path, x)

HEX = re.compile(r"^[0-9A-Fa-f]+$")
def kind_of(path, v):
    name = next((p for p in reversed(path) if isinstance(p, str)), "")
    if isinstance(v, bool): return "bool"
    if isinstance(v, int): return "int"
    if isinstance(v, str) and HEX.match(v):
        if len(v) == 1024: return "P"
        if len(v) == 64: return "Q" if name in ("challenge", "response") else "H"
        if len(v) > 8: return "bytes"
    if isinstance(v, str): return "str"
    return None

def get(x, path):
    for p in path: x = x[p]
    return x
def put(x, path, v): get(x, path[:-1])[path[-1]] = v
def field_name(fkind, path): return fkind + ":" + "/".join("[]" if isinstance(p, int) else p for p in path)

# fields no verification step of the specification reads (metadata, names, labels kept only for
# display, the unproved contest data of a cast ballot, the plaintext contest data of a challenged
# ballot, the ballot's own copy of votes_allowed, sequence orders, cast_ballot_ids, B_aux,0 when
# the codes are not chained): a change may be accepted by both
UNCHECKED = re.compile(r"metadata|timestamp|encrypting_device|created|name|ballot_style|encrypted_sn|"
                       r"eballot:.*encrypted_contest_data|contact_information|geopolitical|parties|candidates|start_date|end_date|"
                       r"spec_version|election_scope_id|type$|electoral_district|ballot_title|ballot_subtitle|tally_id|"
                       r"tally:id$|vote_variation|number_elected|over_votes|write_ins|status|eballot:ballot_id|"
                       r"eballot:contests/\[\]/votes_allowed|guardian_id|sequence_order|cast_ballot_ids|election_config:baux0|numBytes")

def file_kinds(rec):
    """(kind, relative file) of every published JSON file; ballots and challenged ballots are one kind each"""
    out = []
    for f in sorted(glob.glob(os.path.join(rec, "*.json"))): out.append((os.path.basename(f)[:-5], os.path.relpath(f, rec)))
    for f in ballot_files(rec): out.append(("eballot", os.path.relpath(f, rec)))
    for f in sorted(glob.glob(os.path.join(rec, "encrypted_ballots", "*", "ballot_chain.json"))): out.append(("ballot_chain", os.path.relpath(f, rec)))
    for f in sorted(glob.glob(os.path.join(rec, "challenged_ballots", "*.json"))): out.append(("dballot", os.path.relpath(f, rec)))
    return out

def field_mutants(base):
    rec = BASES[base]; G = eglib.Group(rec); p, q, g = G.p, G.q, G.g
    occ = collections.defaultdict(list)
    for fk, rel in file_kinds(rec):
        if fk == "constants": continue   # parameters: covered by source 3
        doc = load(os.path.join(rec, rel))
        for path, k in leaves(doc):
            if k: occ[field_name(fk, path)].append((rel, path, k))
    n = 0
    for fname, lst in sorted(occ.items()):
        rel, path, k = rng.choice(lst)
        doc = load(os.path.join(rec, rel)); v = get(doc, path) if k != "bytes-list" else get(doc, path)
        ops = []
        if k == "P":
            x = ip(v)
            ops = [("times g", hx(x * g % p, 512)), ("1", hx(1, 512)), ("inverse", hx(pow(x, -1, p), 512)),
                   ("random", hx(pow(g, rng.randrange(1, q), p), 512))]
            sib = [r for r in lst if r[0] == rel and r[1][:-1] == path[:-1] and r[1] != path and get(doc, r[1]) != v]
            if sib: ops.append(("swap with sibling", ("swap", rng.choice(sib)[1])))
        elif k == "Q":
            x = ip(v); ops = [("+1", hx((x + 1) % q, 32)), ("0", hx(0, 32)), ("negated", hx((-x) % q, 32)), ("random", hx(rng.randrange(q), 32))]
        elif k in ("H", "bytes"):
            last = v[-1]; ops = [("last digit changed", v[:-1] + ("1" if last != "1" else "2")), ("zero", "0" * len(v))]
        elif k == "int":
            ops = [("+1", v + 1), ("0", 0)] if v != 0 else [("+1", v + 1)]
        elif k == "str":
            ops = [("changed", v + "x")]
        elif k == "bool":
            ops = [("flipped", not v)]
        elif k == "bytes-list":
            vv = list(v); vv[0] = (vv[0] + 1) % 256; ops = [("first byte +1", vv)]
        for opname, nv in ops:
            d = new_case(f"field {base} {fname} {opname}", base)
            doc2 = load(os.path.join(d, rel))
            if isinstance(nv, tuple) and nv[0] == "swap":
                a, b = get(doc2, path), get(doc2, nv[1]); put(doc2, path, b); put(doc2, nv[1], a)
            else:
                put(doc2, path, nv)
            if doc2 == load(os.path.join(rec, rel)): shutil.rmtree(d); continue
            save(os.path.join(d, rel), doc2)
            exp = "either" if UNCHECKED.search(fname) and not (fname == "election_config:baux0" and load(os.path.join(rec, "election_config.json")).get("chain_confirmation_codes")) else "reject"
            add(f"field {base} {fname} {opname}", "2-field", base, exp, d); n += 1
    return n

if "2" in A.sources:
    for b in ("small", "quorum", "multi"): field_mutants(b)

# ---------------------------------------------------------------- source 3: structure and encoding
def structural(base):
    rec = BASES[base]; G = eglib.Group(rec); p, q = G.p, G.q
    def case(name, edit, expected="reject", note=""):
        d = new_case(f"structure {base} {name}", base)
        edit(d); add(f"structure {base} {name}", "3-structure", base, expected, d, note)
    def edit_json(rel_glob, fn):
        def e(d):
            f = sorted(glob.glob(os.path.join(d, rel_glob)))[0]; doc = load(f); fn(doc); save(f, doc)
        return e
    B = "encrypted_ballots/*/eballot-*.json"
    sel0 = lambda b: b["contests"][0]["selections"][0]
    # encodings of the same value
    case("element in lower case", edit_json(B, lambda b: sel0(b)["encrypted_vote"].__setitem__("pad", sel0(b)["encrypted_vote"]["pad"].lower())), "either")
    case("scalar in lower case", edit_json(B, lambda b: sel0(b)["proof"]["proofs"][0].__setitem__("response", sel0(b)["proof"]["proofs"][0]["response"].lower())), "either")
    case("element with an extra leading 00", edit_json(B, lambda b: sel0(b)["encrypted_vote"].__setitem__("pad", "00" + sel0(b)["encrypted_vote"]["pad"])), "either")
    case("element with leading zero digits stripped", edit_json(B, lambda b: sel0(b)["encrypted_vote"].__setitem__("pad", sel0(b)["encrypted_vote"]["pad"].lstrip("0") or "0")), "either",
         "a no-op unless the value starts with 0")
    case("scalar with leading zero digits stripped", edit_json(B, lambda b: sel0(b)["proof"]["proofs"][0].__setitem__("challenge", sel0(b)["proof"]["proofs"][0]["challenge"].lstrip("0") or "0")), "either")
    # values outside the group or Z_q
    for nm, val in [("0", 0), ("p", p), ("p - 1 (not in the subgroup)", p - 1), ("element + p", None), ("2 (not in the subgroup)", 2)]:
        def e(b, val=val):
            x = ip(sel0(b)["encrypted_vote"]["pad"]); v = x + p if val is None else val
            sel0(b)["encrypted_vote"]["pad"] = format(v, "X").rjust(1024, "0")
        case(f"element := {nm}", edit_json(B, e))
    for nm, fn in [("q", lambda x: q), ("scalar + q", lambda x: x + q), ("2^256 - 1", lambda x: 2**256 - 1)]:
        def e(b, fn=fn):
            pf = sel0(b)["proof"]["proofs"][0]; pf["response"] = format(fn(ip(pf["response"])), "X").rjust(64, "0")
        case(f"scalar := {nm}", edit_json(B, e))
    case("joint public key := p - 1", edit_json("election_initialized.json", lambda i: i.__setitem__("joint_public_key", hx(p - 1, 512))))
    case("decrypted tally b_over_m := p - 1", edit_json("tally.json", lambda t: t["contests"][0]["selections"][0].__setitem__("b_over_m", hx(p - 1, 512))))
    # lists one element short or long
    lists = [("ballot: a selection dropped", B, lambda b: b["contests"][0]["selections"].pop()),
             ("ballot: a selection duplicated", B, lambda b: b["contests"][0]["selections"].append(copy.deepcopy(b["contests"][0]["selections"][-1]))),
             ("ballot: a contest dropped", B, lambda b: b["contests"].pop()),
             ("ballot: a contest duplicated", B, lambda b: b["contests"].append(copy.deepcopy(b["contests"][-1]))),
             ("ballot: a range-proof branch dropped", B, lambda b: sel0(b)["proof"]["proofs"].pop()),
             ("ballot: a range-proof branch duplicated", B, lambda b: sel0(b)["proof"]["proofs"].append(copy.deepcopy(sel0(b)["proof"]["proofs"][-1]))),
             ("ballot: a selection-limit branch dropped", B, lambda b: b["contests"][0]["proof"]["proofs"].pop()),
             ("initialized: a guardian dropped", "election_initialized.json", lambda i: i["guardians"].pop()),
             ("initialized: a guardian duplicated", "election_initialized.json", lambda i: i["guardians"].append(copy.deepcopy(i["guardians"][-1]))),
             ("initialized: a coefficient proof dropped", "election_initialized.json", lambda i: i["guardians"][0]["coefficient_proofs"].pop()),
             ("encrypted tally: a selection dropped", "encrypted_tally.json", lambda t: t["contests"][0]["selections"].pop()),
             ("encrypted tally: a contest dropped", "encrypted_tally.json", lambda t: t["contests"].pop()),
             ("encrypted tally: a cast ballot id dropped", "encrypted_tally.json", lambda t: t["cast_ballot_ids"].pop()),
             ("encrypted tally: a cast ballot id duplicated", "encrypted_tally.json", lambda t: t["cast_ballot_ids"].append(t["cast_ballot_ids"][0])),
             ("tally: a selection dropped", "tally.json", lambda t: t["contests"][0]["selections"].pop()),
             ("tally: a contest dropped", "tally.json", lambda t: t["contests"].pop())]
    for nm, rel, fn in lists: case(nm, edit_json(rel, fn), "either" if "cast ballot id" in nm else "reject")
    # fields missing, extra, of the wrong type
    case("ballot: a range proof missing", edit_json(B, lambda b: sel0(b).pop("proof")))
    case("ballot: an extra unknown field", edit_json(B, lambda b: b.__setitem__("unknown_field", 1)), "accept")
    case("tally: a count as a string", edit_json("tally.json", lambda t: t["contests"][0]["selections"][0].__setitem__("tally", str(t["contests"][0]["selections"][0]["tally"]))), "either")
    case("config: quorum := number of guardians + 1", edit_json("election_config.json", lambda c: c.__setitem__("quorum", c["number_of_guardians"] + 1)))
    case("constants: generator := g^2", edit_json("constants.json", lambda c: c.__setitem__("generator", hx(pow(ip(c["generator"]), 2, ip(c["large_prime"])), 512))))
    # ballot states
    def first_cast(d):
        return next(f for f in ballot_files(d) if load(f)["state"] == "CAST")
    def state_case(nm, st, expected):
        def e(d):
            f = first_cast(d); b = load(f); b["state"] = st; save(f, b)
        case(f"a cast ballot's state := {st}", e, expected)
    state_case("", "SPOILED", "reject"); state_case("", "UNKNOWN", "reject"); state_case("", "CHALLENGED", "reject"); state_case("", "cast", "reject")
    # duplicated and replayed ballots
    def dup(d):
        f = first_cast(d); shutil.copy(f, os.path.join(os.path.dirname(f), "eballot-zz-copy.json"))
    case("a cast ballot duplicated (same id, second file)", dup)
    def replay(d):
        other = "multi" if base != "multi" else "small"
        f = next(f for f in ballot_files(BASES[other]) if load(f)["state"] == "CAST")
        shutil.copy(f, os.path.join(os.path.dirname(ballot_files(d)[0]), "eballot-zz-replayed.json"))
    case("a cast ballot of another election added", replay)

if "3" in A.sources:
    for b in ("small",): structural(b)

# ---------------------------------------------------------------- source 4: forgeries and protocol
def forged_ballot(base, rec, votes, claims, rng, ballot_id, limit_claims=None):
    """a cast ballot made by our prover: votes[i][j] is what option j of contest i
    encrypts, claims[i][j] the value the range proof is run with (the witness);
    the selection-limit proof of contest i is run with limit_claims[i] (default:
    the sum of the claims)"""
    E = eglib.Election(rec); G = E.G; p, q = G.p, G.q
    tmpl = load(next(f for f in ballot_files(rec) if load(f)["state"] == "CAST"))
    b = copy.deepcopy(tmpl); b["ballot_id"] = ballot_id
    manifest_c = sorted(E.manifest["contests"], key=lambda c: c["sequence_order"])
    chis = []
    for ci, c in enumerate(sorted(b["contests"], key=lambda c: c["sequence_order"])):
        L = c["votes_allowed"]
        opt_limit = manifest_c[ci].get("option_selection_limit", 1)
        cts, xis = [], []
        for sj, s in enumerate(sorted(c["selections"], key=lambda s: s["sequence_order"])):
            xi = rng.randrange(q); a, bb = E.encrypt(votes[ci][sj], xi)
            s["encrypted_vote"] = {"pad": hx(a, 512), "data": hx(bb, 512)}
            s["proof"] = {"proofs": E.range_proof(a, bb, claims[ci][sj], xi, opt_limit, rng)}
            cts.append((a, bb)); xis.append(xi)
        A_ = B_ = 1
        for a, bb in cts: A_, B_ = A_ * a % p, B_ * bb % p
        lc = sum(claims[ci]) if limit_claims is None else limit_claims[ci]
        c["proof"] = {"proofs": E.range_proof(A_, B_, lc, sum(xis) % q, L, rng)}
        chi = E.contest_hash(c["sequence_order"], cts); c["contest_hash"] = chi.hex().upper(); chis.append(chi)
    b["confirmation_code"] = E.confirmation_code(chis, bytes.fromhex(b["code_baux"])).hex().upper()
    b["state"] = "CAST"
    return b

def counted(base, rec, ballot):
    """add the ballot as cast, recompute the encrypted tally and decrypt it with the trustees"""
    save(os.path.join(os.path.dirname(ballot_files(rec)[0]), f"eballot-{ballot['ballot_id']}.json"), ballot)
    recompute_encrypted_tally(rec)
    decrypt_tally(rec, base)

def shape(rec):
    b = load(next(f for f in ballot_files(rec) if load(f)["state"] == "CAST"))
    return [len(c["selections"]) for c in sorted(b["contests"], key=lambda c: c["sequence_order"])], \
           [c["votes_allowed"] for c in sorted(b["contests"], key=lambda c: c["sequence_order"])]

def ballot_forgeries(base):
    widths, limits = shape(BASES[base])
    honest = [[1 if j == 0 else 0 for j in range(w)] for w in widths]
    scen = []
    # (name, votes, claims, limit claims): votes = what is encrypted, claims = the witnesses of the proofs
    over = copy.deepcopy(honest); over[0][0] = 2
    scen.append(("option encrypts 2, range and limit proofs claim 1 (overvote)", over, honest, None))
    # vote transfer: option a encrypts -1 (it has votes in the tally, which stays non-negative),
    # option b encrypts +1; the contest sums to 0, so only a's range proof cheats
    t = load(os.path.join(BASES[base], "tally.json"))
    c0 = sorted(t["contests"], key=lambda c: c["contest_id"])[0]
    counts = [s["tally"] for s in c0["selections"]]
    if widths[0] >= 2 and max(counts) >= 1:
        a = counts.index(max(counts)); b2 = (a + 1) % widths[0]
        tr = copy.deepcopy(honest); tr[0] = [0] * widths[0]; tr[0][a] = -1; tr[0][b2] = 1
        cl = copy.deepcopy(tr); cl[0][a] = 0
        scen.append(("vote transfer: an option encrypts -1 (range proof claims 0), another +1", tr, cl, [0] + [sum(r) for r in honest[1:]]))
    if widths[0] >= 2 and limits[0] == 1:
        two = copy.deepcopy(honest); two[0][1] = 1   # two options of a one-vote contest: range proofs honest
        scen.append(("two options of a 1-vote contest, limit proof claims 1", two, two, [1] + [sum(r) for r in honest[1:]]))
    for nm, votes, claims, lclaims in scen:
        for kind in ("control", "forgery"):
            d = new_case(f"forgery {base} ballot: {nm} | {kind}", base)
            if kind == "control":
                b = forged_ballot(base, d, honest, honest, rng, "zz-forged")
            else:
                b = forged_ballot(base, d, votes, claims, rng, "zz-forged", lclaims)
            counted(base, d, b)
            add(f"forgery {base} ballot: {nm} | {kind}", "4-forgery", base, "accept" if kind == "control" else "reject", d)

def tally_forgeries(base):
    rec = BASES[base]
    def mk(name, expected, fn):
        nm = f"forgery {base} tally: {name}"; d = new_case(nm, base)
        try: fn(d)
        except RuntimeError as e: SKIPPED.append((nm, str(e)[:200])); shutil.rmtree(d); return
        add(nm, "4-forgery", base, expected, d)
    mk("re-decrypted unchanged | control", "accept", lambda d: decrypt_tally(d, base))
    def inflate(d):
        E = eglib.Election(d); xi = rng.randrange(E.G.q)
        recompute_encrypted_tally(d, extra=(0, 0, E.encrypt(1, xi))); decrypt_tally(d, base)
    mk("encrypted tally times Enc(1), validly decrypted | forgery", "reject", inflate)
    def spoiled_in(d):
        recompute_encrypted_tally(d, include=lambda b: True); decrypt_tally(d, base)
    if any(load(f)["state"] == "SPOILED" for f in ballot_files(rec)):
        mk("a challenged ballot counted, validly decrypted | forgery", "reject", spoiled_in)
    def drop_from_tally(d):
        first = next(load(f)["ballot_id"] for f in ballot_files(d) if load(f)["state"] == "CAST")
        recompute_encrypted_tally(d, include=lambda b: b["state"] == "CAST" and b["ballot_id"] != first); decrypt_tally(d, base)
    mk("a cast ballot left out of the tally (file kept), validly decrypted | forgery", "reject", drop_from_tally)
    def delete_ballot(d):
        f = next(f for f in ballot_files(d) if load(f)["state"] == "CAST"); os.remove(f)
        recompute_encrypted_tally(d); decrypt_tally(d, base)
    chained = load(os.path.join(rec, "election_config.json")).get("chain_confirmation_codes")
    mk("a cast ballot deleted, tally recomputed and decrypted", "reject" if chained else "accept", delete_ballot)
    def decrypt_cast(d):   # a cast ballot decrypted as if challenged: its decryption published
        f = next(f for f in ballot_files(d) if load(f)["state"] == "CAST"); bid = load(f)["ballot_id"]
        r = egk("electionguard.cli.RunTrustedBallotDecryption", "-in", d, "-trustees", trustees(base), "-out", d, "-challenged", bid, "-nthreads", "1")
        if not os.path.exists(os.path.join(d, "challenged_ballots", f"dballot-{bid}.json")):
            err = next((l.strip() for l in (r.stdout + r.stderr).splitlines() if "Exception" in l), "no decryption written")
            raise RuntimeError(f"egk RunTrustedBallotDecryption: {err}")
    mk("a cast ballot's decryption published as a challenged ballot", "reject", decrypt_cast)
    def substitute_challenged(d, honest):
        """the published decryption of a challenged ballot S: honest = S's own, re-made
        by egk; otherwise that of another ciphertext Y with other choices (our prover,
        honest proofs), decrypted by egk in a scratch copy and relabelled with S's id.
        A device that encrypts a wrong vote could pass a voter's challenge this way."""
        sp = next(load(f) for f in ballot_files(d) if load(f)["state"] == "SPOILED")
        sid = sp["ballot_id"]
        scratch = d + ".scratch"; shutil.copytree(d, scratch)
        if honest:
            oid = sid
        else:
            pub = load(os.path.join(d, "challenged_ballots", f"dballot-{sid}.json"))
            val = {(c["contest_id"], s["selection_id"]): s["tally"] for c in pub["contests"] for s in c["selections"]}
            shown = [[val[(c["contest_id"], s["selection_id"])] for s in sorted(c["selections"], key=lambda s: s["sequence_order"])]
                     for c in sorted(sp["contests"], key=lambda c: c["sequence_order"])]
            other = [r[-1:] + r[:-1] for r in shown]   # other choices: each contest rotated,
            for r, r0 in zip(other, shown):              # or, where that changes nothing, one option chosen
                if r == r0: r[:] = [1] + [0] * (len(r) - 1) if r0[0] == 0 else [0, 1] + [0] * (len(r) - 2)
            if other == shown: raise RuntimeError("no other choices")
            oid = "zz-other"
            b = forged_ballot(base, scratch, other, other, rng, oid); b["state"] = "SPOILED"
            save(os.path.join(os.path.dirname(ballot_files(scratch)[0]), f"eballot-{oid}.json"), b)
        egk("electionguard.cli.RunTrustedBallotDecryption", "-in", scratch, "-trustees", trustees(base), "-out", scratch, "-challenged", oid, "-nthreads", "1")
        src = os.path.join(scratch, "challenged_ballots", f"dballot-{oid}.json")
        if not os.path.exists(src): raise RuntimeError("egk wrote no decryption")
        dec = load(src); dec["id"] = sid
        save(os.path.join(d, "challenged_ballots", f"dballot-{sid}.json"), dec)
        shutil.rmtree(scratch)
    if glob.glob(os.path.join(rec, "challenged_ballots", "*.json")):
        mk("a challenged ballot's decryption re-made | control", "accept", lambda d: substitute_challenged(d, True))
        mk("a challenged ballot's published decryption is that of another ciphertext (other choices) | forgery", "reject",
           lambda d: substitute_challenged(d, False))
    def drop_challenged(d):
        fs = sorted(glob.glob(os.path.join(d, "challenged_ballots", "*.json")))
        if fs: os.remove(fs[0])
    if glob.glob(os.path.join(rec, "challenged_ballots", "*.json")):
        mk("a challenged ballot's decryption missing", "either", drop_challenged)

def hash_forgeries(base):
    """egk's pipeline (key ceremony when H_P changes, encryption of the voters' input ballots,
    the same challenges, accumulation, decryption) on a configuration whose base hash is
    replaced; every later hash and proof uses the replaced value consistently"""
    rec = BASES[base]
    spoiled_ids = [load(f)["ballot_id"] for f in ballot_files(rec) if load(f)["state"] == "SPOILED"]
    def pipeline(d, which):
        work = d + ".work"; shutil.rmtree(d)
        kc = os.path.join(work, "kc"); os.makedirs(kc)
        for f in ("constants.json", "manifest.json", "election_config.json", "election_initialized.json"):
            shutil.copy(os.path.join(rec, f), kc)
        cfg = load(os.path.join(kc, "election_config.json")); init = load(os.path.join(kc, "election_initialized.json"))
        E = eglib.Election(rec)
        hp = bytes.fromhex(cfg["parameter_base_hash"]); K = E.K
        n, k = cfg["number_of_guardians"], cfg["quorum"]
        rnd = lambda: bytes(rng.randrange(256) for _ in range(32))
        trustee_dir = trustees(base)
        if which == "H_P":
            hp = rnd(); cfg["parameter_base_hash"] = hp.hex().upper()
        if which in ("H_P", "H_M"):
            hm = rnd() if which == "H_M" else eglib.H(hp, [b"\x01", len(open(os.path.join(kc, "manifest.json"), "rb").read()).to_bytes(4, "big") + open(os.path.join(kc, "manifest.json"), "rb").read()])
            cfg["manifest_hash"] = hm.hex().upper()
        if which in ("H_P", "H_M", "H_B"):
            hb = rnd() if which == "H_B" else eglib.H(hp, [b"\x02", bytes.fromhex(cfg["manifest_hash"]), eglib.enc_int(n), eglib.enc_int(k)])
            cfg["election_base_hash"] = hb.hex().upper()
        save(os.path.join(kc, "election_config.json"), cfg)
        if which == "H_P":   # the guardians' proofs hash H_P: a new key ceremony on the forged configuration
            cdir = os.path.join(work, "config"); os.makedirs(cdir)
            for f in ("constants.json", "manifest.json", "election_config.json"): shutil.copy(os.path.join(kc, f), cdir)
            trustee_dir = os.path.join(work, "trustees"); shutil.rmtree(kc); os.makedirs(kc)
            egk("electionguard.cli.RunTrustedKeyCeremony", "-in", cdir, "-trustees", trustee_dir, "-out", kc)
            init = load(os.path.join(kc, "election_initialized.json")); K = ip(init["joint_public_key"])
        if which in ("H_P", "H_M", "H_B", "H_E"):
            he = rnd() if which == "H_E" else eglib.H(bytes.fromhex(load(os.path.join(kc, "election_config.json"))["election_base_hash"]), [b"\x12", eglib.enc_p(K)])
            init["extended_base_hash"] = he.hex().upper()
        save(os.path.join(kc, "election_initialized.json"), init)
        egk("electionguard.cli.RunBatchEncryption", "-in", kc, "-ballots", os.path.join(rec, "private_data", "input"), "-out", d,
            "-device", "device42", "-nthreads", "1", "--cleanOutput")
        for f in ballot_files(d):
            b = load(f)
            if b["ballot_id"] in spoiled_ids: b["state"] = "SPOILED"; save(f, b)
        egk("electionguard.cli.RunAccumulateTally", "-in", d, "-out", d)
        decrypt_tally(d, base, trustee_dir)
        if spoiled_ids: decrypt_challenged(d, base, trustee_dir)
        for f in ("manifest.json", "election_config.json", "constants.json"):
            if not os.path.exists(os.path.join(d, f)): shutil.copy(os.path.join(kc, f), d)
        shutil.rmtree(work)
        # egk recomputes nothing from the configuration: the forged value must be in the record
        if which != "control":
            got = {"H_P": load(os.path.join(d, "election_config.json"))["parameter_base_hash"],
                   "H_M": load(os.path.join(d, "election_config.json"))["manifest_hash"],
                   "H_B": load(os.path.join(d, "election_config.json"))["election_base_hash"],
                   "H_E": load(os.path.join(d, "election_initialized.json"))["extended_base_hash"]}[which]
            return got
    for which in ("control", "H_E", "H_B", "H_M", "H_P"):
        name = f"forgery {base} base hash: " + ("egk pipeline re-run | control" if which == "control" else f"{which} replaced, used consistently | forgery")
        d = new_case(name, base)
        pipeline(d, which)
        add(name, "4-forgery", base, "accept" if which == "control" else "reject", d)

def chain_forgeries(base):
    """egk's chained record: the confirmation chain of Section 3.4.3 (7.D–7.G)"""
    rec = BASES[base]; E = eglib.Election(rec)
    cfg = load(os.path.join(rec, "election_config.json")); baux0 = bytes(cfg["baux0"])
    def chain_file(d): return glob.glob(os.path.join(d, "encrypted_ballots", "*", "ballot_chain.json"))[0]
    def close(d, ids):
        """rewrite ballot_chain.json for these ballot ids (the last code and the closing hash recomputed)"""
        cf = chain_file(d); ch = load(cf)
        last = load(os.path.join(os.path.dirname(cf), f"eballot-{ids[-1]}.json"))["confirmation_code"]
        ch["ballot_ids"] = ids; ch["last_confirmation_code"] = last
        ch["closing_hash"] = eglib.H(E.HE, [b"\x24", bytes.fromhex(last) + baux0 + b"CLOSE"]).hex().upper()
        save(cf, ch)
    def mk(name, expected, fn, note=""):
        d = new_case(f"protocol {base} chain: {name}", base); fn(d); add(f"protocol {base} chain: {name}", "4-protocol", base, expected, d, note)
    ids = load(chain_file(rec))["ballot_ids"]
    mk("closing hash recomputed, unchanged | control", "accept", lambda d: close(d, ids))
    def drop_middle(d):
        mid = ids[len(ids) // 2]; os.remove(os.path.join(os.path.dirname(chain_file(d)), f"eballot-{mid}.json"))
        close(d, [i for i in ids if i != mid]); recompute_encrypted_tally(d); decrypt_tally(d, base)
    mk("a cast ballot removed from the middle of the chain, tally recomputed and decrypted", "reject", drop_middle)
    def orphan_last(d):
        last = ids[-1]; close(d, ids[:-1])
        st = load(os.path.join(os.path.dirname(chain_file(d)), f"eballot-{last}.json"))["state"]
        recompute_encrypted_tally(d, include=lambda b: b["state"] == "CAST" and b["ballot_id"] != last); decrypt_tally(d, base)
    mk("the last ballot left out of the chain and the tally (file kept, closing hash recomputed)", "reject", orphan_last,
       "the ballot is published, so its voter finds the confirmation code, but it is not counted")
    def reorder(d):
        ids2 = list(ids); ids2[0], ids2[1] = ids2[1], ids2[0]; close(d, ids2)
    mk("two ballots swapped in the chain order (closing hash recomputed)", "reject", reorder)
    def bad_close(d):
        cf = chain_file(d); ch = load(cf); h = ch["closing_hash"]; ch["closing_hash"] = h[:-1] + ("1" if h[-1] != "1" else "2"); save(cf, ch)
    mk("closing hash changed", "reject", bad_close)
    def no_chain(d): os.remove(chain_file(d))
    mk("ballot_chain.json removed", "reject", no_chain)

if "4" in A.sources:
    for b in ("small", "quorum", "multi"): ballot_forgeries(b)
    for b in ("small", "quorum"): tally_forgeries(b)
    tally_forgeries("egk-chainedJson")
    for b in ("small",): hash_forgeries(b)
    chain_forgeries("egk-chainedJson")
    add("protocol chained-batch: configuration chains the codes, the ballots do not (egk RunBatchEncryption)", "4-protocol", "chained-batch",
        "reject", new_case("protocol chained-batch", "chained-batch"), "egk's batch encryption does not chain; it writes no ballot_chain.json")

# ---------------------------------------------------------------- run both verifiers
STEP = re.compile(r"^\s*([0-9][0-9.,]*)\.\s+(\w+)\s*=?\s*(Ok\(true|Ok\(false|Err|true|false)", re.M)
def run_egk(d):
    t0 = time.time()
    r = subprocess.run([A.java, "-classpath", A.jar, "electionguard.cli.RunVerifier", "-in", d, "-nthreads", "1"], capture_output=True, text=True, cwd=A.work)
    out = r.stdout + r.stderr
    m = re.search(r"verify allOK = (true|false)", out)
    fails = [f"{s} {n}" for s, n, v in STEP.findall(out) if v in ("false", "Ok(false", "Err")]
    if not m:
        err = next((l.strip() for l in out.splitlines() if "rror" in l or "xception" in l), out.strip().splitlines()[-1] if out.strip() else "no output")
        return "error", [err[:160]], time.time() - t0
    return ("accept" if m.group(1) == "true" else "reject"), fails, time.time() - t0

def run_ours(d):
    t0 = time.time()
    r = subprocess.run([A.ours, d], capture_output=True, text=True)
    out = r.stdout + r.stderr
    fails = [re.sub(r"\s+false$", "", l.strip()) for l in r.stdout.splitlines() if re.search(r"\sfalse$", l) and "verified" not in l]
    fails += [l.strip() for l in r.stdout.splitlines() if l.startswith("MALFORMED") or "rejected" in l
              or re.match(r"Invalid votes : \[[1-9]", l)]
    if r.returncode == 0: return "accept", fails, time.time() - t0
    if not re.search(r"verified = false", out):
        fails = fails + [(out.strip().splitlines() or ["no output"])[-1][:160]]
        return "error", fails, time.time() - t0
    return "reject", fails, time.time() - t0

def run_case(c):
    e, ef, et = run_egk(c["dir"]); o, of, ot = run_ours(c["dir"])
    return c, e, ef, et, o, of, ot

t0 = time.time()
with concurrent.futures.ThreadPoolExecutor(A.jobs) as ex:
    results = list(ex.map(run_case, cases))
acc = lambda v: v == "accept"
rows, details = [], []
for c, e, ef, et, o, of, ot in sorted(results, key=lambda r: r[0]["name"]):
    agree = acc(e) == acc(o)
    meets = c["expected"] == "either" or (acc(e) == (c["expected"] == "accept") and acc(o) == (c["expected"] == "accept"))
    rows.append([c["name"], c["source"], c["base"], c["expected"], e, o, "agree" if agree else "DISAGREE", "as expected" if meets else "UNEXPECTED"])
    details.append(rows[-1] + ["; ".join(ef)[:400], "; ".join(of)[:400], f"{et:.1f}", f"{ot:.1f}", c["note"]])
hdr = ["case", "source", "base", "expected", "egk", "certified", "comparison", "expectation"]
with open(os.path.join(A.out, "summary.tsv"), "w") as f:
    f.write("\t".join(hdr) + "\n"); f.writelines("\t".join(r) + "\n" for r in rows)
with open(os.path.join(A.out, "details.tsv"), "w") as f:
    f.write("\t".join(hdr + ["egk failed steps", "certified failed checks", "egk s", "certified s", "note"]) + "\n")
    f.writelines("\t".join(r) + "\n" for r in details)
tally = collections.Counter((r[1], r[4] if r[4] != "error" else "error(reject)", r[5] if r[5] != "error" else "error(reject)", r[6]) for r in rows)
print(f"{len(rows)} cases in {time.time() - t0:.0f} s")
for k, n in sorted(tally.items()): print("  " + "  ".join(k) + f"  {n}")
for r in rows:
    if r[6] != "agree" or r[7] != "as expected": print("  " + " | ".join(r))
for nm, why in SKIPPED: print(f"  SKIPPED (construction failed in egk): {nm}: {why}")
with open(os.path.join(A.out, "skipped.tsv"), "w") as f: f.writelines(f"{nm}\t{why}\n" for nm, why in SKIPPED)
print(f"{sum(r[6] != 'agree' for r in rows)} disagreements, {sum(r[7] != 'as expected' for r in rows)} unexpected verdicts, {len(SKIPPED)} skipped")
