#!/usr/bin/env python3
"""Differential-testing campaign of Verificatum's own verifier vmnv against
our certified verifier (src/Executable/Vmnverifier) on a mixing session
produced by vmn. Every case is one tampered copy of a proof directory; both
verifiers run on it, and the verdicts are compared.

Sources of cases:
  honest        the untouched session (both must accept)
  field         one byte-tree leaf of each proof file changed, by type:
                a group element (times g, to 1, to a random element), an
                exponent/scalar (+1, 0, a random value) and an opaque leaf
                (last byte flipped)
  structural    a proof array one element short or long, a ciphertext list
                truncated, a byte tree made malformed, an element put out of
                the group, a scalar put out of range
  protocol      two output ciphertexts of a server swapped; a server's output
                list replaced by another server's; the permutation commitment
                of one server used by another; CorrectIndices changed
  forge-pos     the PoSCommitment of server 1 replaced by server 2's while
                keeping server 1's A' (targets a verifier that derives a
                proof's challenge from a commitment it does not bind)

usage: campaign.py SESSION_DIR VMNV OURS OUT [--ours-before BIN]
  SESSION_DIR has protInfo.xml and default/; VMNV and OURS are the two
  verifier commands; OUT receives summary.tsv and the mutated copies."""
import os, shutil, subprocess, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import vmnlib as V

sess, vmnv, ours, out = sys.argv[1:5]
ours_before = None
if "--ours-before" in sys.argv:
    ours_before = sys.argv[sys.argv.index("--ours-before") + 1]
os.makedirs(out, exist_ok=True)
grp = V.Group(os.path.join(sess, "protInfo.xml"))
p, q, g = grp.p, grp.q, grp.g

GROUP_FILES = {"FullPublicKey.bt", "Ciphertexts.bt", "Plaintexts.bt"}   # leaves are group elements
PROOF = "default/proofs"

def classify(name):
    """how the leaves of a proof file should be mutated: 'group', 'scalar' or 'opaque'"""
    if name in ("PoSReply01.bt", "PoSReply02.bt", "DecrFactReply01.bt", "DecrFactReply02.bt", "DecrFactReply03.bt"):
        return "scalar"
    if name == "PolynomialInExponent.bt" or name.startswith(("Ciphertexts", "DecryptionFactors", "PermutationCommitment",
                                                              "PoSCommitment", "DecrFactCommitment", "FullPublicKey", "Plaintexts")):
        return "group"
    return "opaque"

def leaves(t, path=()):
    if t[0] == "leaf":
        yield path
    else:
        for i, c in enumerate(t[1]):
            yield from leaves(c, path + (i,))

def get(t, path):
    for i in path: t = t[1][i]
    return t

def setleaf(t, path, b):
    if not path:
        return ("leaf", b)
    i = path[0]; cs = list(t[1]); cs[i] = setleaf(cs[i], path[1:], b); return (t[0], cs)

def mutate_leaf(kind, b, which):
    x = V.of_bytes(b); k = len(b)
    if kind == "group":
        ops = {"times_g": (x * g) % p, "to_1": 1, "to_rand": pow(g, 7919 + which, p)}
    elif kind == "scalar":
        ops = {"plus_1": (x + 1), "to_0": 0, "to_rand": (x ^ (0x9e37 + which))}
    else:
        bb = bytearray(b); bb[-1] ^= 0x01; return bytes(bb)
    name = list(ops)[which % len(ops)]
    v = ops[name]
    try:
        return V.to_bytes(k, v)
    except OverflowError:
        return V.to_bytes(k + 1, v)

def make_copy(name):
    d = os.path.join(out, name)
    shutil.rmtree(d, ignore_errors=True)
    shutil.copytree(sess, d)
    return d

cases = []   # (name, kind, edit) ; edit(dir) mutates the copy in place
cases.append(("honest", "honest", lambda d: None))

# field mutants: one leaf per proof file, one mutation of the fitting type
for fn in sorted(os.listdir(os.path.join(sess, PROOF))) + ["FullPublicKey.bt", "Ciphertexts.bt", "Plaintexts.bt"]:
    if not fn.endswith(".bt"): continue
    sub = PROOF if fn not in GROUP_FILES else "default"
    kind = classify(fn)
    nmut = 3 if kind in ("group", "scalar") else 1
    for w in range(nmut):
        def edit(d, fn=fn, sub=sub, kind=kind, w=w):
            path = os.path.join(d, sub, fn)
            t = V.bt_load(path); ls = list(leaves(t))
            lf = ls[(w * 7) % len(ls)]
            t = setleaf(t, lf, mutate_leaf(kind, get(t, lf)[1], w))
            V.bt_save(path, t)
        cases.append(("field-%s-%s-%d" % (fn[:-3], kind, w), "field", edit))

# structural / encoding
def drop_last(d, fn):
    path = os.path.join(d, PROOF, fn); t = V.bt_load(path)
    if t[0] == "node" and t[1] and t[1][-1][0] == "leaf":
        V.bt_save(path, ("node", t[1][:-1]))
def dup_last(d, fn):
    path = os.path.join(d, PROOF, fn); t = V.bt_load(path)
    if t[0] == "node" and t[1]:
        V.bt_save(path, ("node", t[1] + [t[1][-1]]))
for fn in ["DecryptionFactors01.bt", "PoSReply01.bt", "PermutationCommitment01.bt"]:
    cases.append(("struct-drop-%s" % fn[:-3], "structural", lambda d, fn=fn: drop_last(d, fn)))
    cases.append(("struct-dup-%s" % fn[:-3], "structural", lambda d, fn=fn: dup_last(d, fn)))
def truncate_bytetree(d):
    path = os.path.join(d, PROOF, "PoSCommitment01.bt")
    b = open(path, "rb").read(); open(path, "wb").write(b[:len(b) - 10])
cases.append(("struct-malformed-bytetree", "structural", truncate_bytetree))
def elem_out_of_group(d):
    path = os.path.join(d, "default", "Ciphertexts.bt"); t = V.bt_load(path)
    lf = next(leaves(t)); V.bt_save(path, setleaf(t, lf, V.to_bytes(grp.kp, 3)))   # 3 is not a QR mod p
cases.append(("struct-elem-nonmember", "structural", elem_out_of_group))
def scalar_out_of_range(d):
    path = os.path.join(d, PROOF, "PoSReply01.bt"); t = V.bt_load(path)
    lf = next(leaves(t)); V.bt_save(path, setleaf(t, lf, V.to_bytes(grp.kq, q)))   # scalar = q, out of [0,q)
cases.append(("struct-scalar-oor", "structural", scalar_out_of_range))

# protocol tampering
def swap_two_outputs(d):
    path = os.path.join(d, PROOF, "Ciphertexts02.bt"); t = V.bt_load(path)
    us, vs = t[1]
    for comp in (us, vs):
        comp[1][0], comp[1][1] = comp[1][1], comp[1][0]
    V.bt_save(path, t)
cases.append(("proto-swap-two-outputs", "protocol", swap_two_outputs))
def replace_output_list(d):
    shutil.copy(os.path.join(d, PROOF, "Ciphertexts01.bt"), os.path.join(d, PROOF, "Ciphertexts02.bt"))
cases.append(("proto-replace-output-list", "protocol", replace_output_list))
def share_perm_commitment(d):
    shutil.copy(os.path.join(d, PROOF, "PermutationCommitment02.bt"), os.path.join(d, PROOF, "PermutationCommitment01.bt"))
cases.append(("proto-share-perm-commitment", "protocol", share_perm_commitment))
def flip_correct_indices(d):
    path = os.path.join(d, PROOF, "CorrectIndices.bt"); t = V.bt_load(path)
    b = bytearray(t[1]); b[-1] ^= 0x01; V.bt_save(path, ("leaf", bytes(b)))
cases.append(("proto-correct-indices", "protocol", flip_correct_indices))

# targeted forgery: give server 1 the PoSCommitment of server 2 but keep server 1's A'
# (A' is the first child). A verifier that keys the challenge on A' alone would then
# hash server 2's commitments while checking server 1, so B/B'/C'/D'/F' go unbound.
def forge_shared_poscommitment(d):
    p1 = os.path.join(d, PROOF, "PoSCommitment01.bt")
    p2 = os.path.join(d, PROOF, "PoSCommitment02.bt")
    t1 = V.bt_load(p1); t2 = V.bt_load(p2)
    forged = ("node", [t1[1][0]] + t2[1][1:])   # server 1's A', server 2's b, a', b', c', d', f'
    V.bt_save(p1, forged)
cases.append(("forge-pos-shared-commitment", "forge-pos", forge_shared_poscommitment))

def run_vmnv(d):
    # vmnv needs a configured random source (for temporary randomness); it is
    # irrelevant to the deterministic verification. VERIFICATUM_RANDOM_SOURCE
    # / _SEED are set by run.sh and inherited here.
    r = subprocess.run([vmnv, "-sloppy", "-wd", os.path.join(out, ".vmnvwd"), "-a", "file",
                        os.path.join(d, "protInfo.xml"), os.path.join(d, "default")],
                       capture_output=True, text=True)
    if "random source" in (r.stdout + r.stderr):
        raise SystemExit("vmnv has no random source; set VERIFICATUM_RANDOM_SOURCE/_SEED (run.sh does)")
    return r.returncode == 0

def run_ours(binary, d):
    r = subprocess.run([binary, os.path.join(d, "protInfo.xml"), os.path.join(d, "default")], capture_output=True, text=True)
    return r.returncode == 0, (r.stdout.strip().splitlines() or [""])[-1][:80]

summary = []
disagree = 0
for name, kind, edit in cases:
    d = make_copy(name)
    edit(d)
    vo = run_vmnv(d)
    oo, omsg = run_ours(ours, d)
    expect_accept = (kind == "honest")
    agree = vo == oo
    disagree += not agree
    extra = ""
    if ours_before:
        bo, _ = run_ours(ours_before, d)
        extra = "\t" + ("accept" if bo else "reject")
    summary.append("%s\t%s\t%s\t%s\t%s%s\t%s" % (
        name, kind, "accept" if vo else "reject", "accept" if oo else "reject",
        "AGREE" if agree else "DISAGREE", extra, omsg))

hdr = "case\tkind\tvmnv\tours\tcompare" + ("\tours_before" if ours_before else "") + "\tours_msg"
open(os.path.join(out, "summary.tsv"), "w").write(hdr + "\n" + "\n".join(summary) + "\n")
print(hdr)
for line in summary: print(line)
print("%d cases, %d disagreements" % (len(cases), disagree))
sys.exit(1 if disagree else 0)
