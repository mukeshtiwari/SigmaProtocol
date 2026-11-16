#!/usr/bin/env python3
"""The IVXV differential campaign (verdict comparison only).

  shuffle   Verificatum 3.1.0 shuffling sessions, three verifiers: Verificatum's
            vmnv, IVXV's auditor shuffle verifier (IvxvShuffleDiff, as MixerTool)
            and the certified verifier (Ivxvdiff/main.exe shuffle)
  dec       IVXV decryption proofs (Java ElGamalDecryptionProof), IVXV's auditor
            path (IvxvDecDiff verify) and the certified verifier (main.exe dec)
  go        IVXV Go core decryption proofs (tivi.io/core PublicKey.Verify),
            ivxvgo verify and the certified verifier (main.exe nizkp)

Sources: honest (deployed provers), controls (our independent provers, incl.
degenerate inputs), false statements (our provers on a wrong witness, every
challenge derived from the transcript), field mutants by type, structural and
encoding mutants. Every random choice is seeded by SEED; inputs that a
deployed prover draws its own randomness for are read from fixtures/.

usage: campaign.py WORK  (WORK prepared by run.sh)"""
import concurrent.futures, copy, json, os, random, re, shutil, subprocess, sys, collections
here = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, here)
import ivxvlib as L

W = os.path.abspath(sys.argv[1]); SEED = int(os.environ.get("SEED", "1")); JOBS = int(os.environ.get("JOBS", "4"))
root = os.path.abspath(os.path.join(here, "..", ".."))
OURS = os.path.join(root, "_build/default/src/Executable/Ivxvdiff/main.exe")
VMN = os.path.join(W, "vmn-install"); VMN_SRC = os.path.join(W, "vmn-src/verificatum-vmn-3.1.0")
JDK21 = os.environ["JDK21"]; JDK25 = os.environ["JDK25"]
IVXV_CP = os.path.join(W, "drivers-classes") + ":" + os.path.join(W, "ivxv/auditor/build/install/auditor/lib/*")
GOBIN = os.path.join(W, "go/ivxvgo")
CASES = os.path.join(W, "cases"); RES = os.path.join(here, "results")
os.makedirs(CASES, exist_ok=True); os.makedirs(RES, exist_ok=True)
rng = random.Random(SEED)
desc = open(os.path.join(here, "group.txt")).read().strip()
gt = L.bt_dec(bytes.fromhex(desc.split("::")[-1]))[0]
P, Q, G = (L.ival(z) for z in gt[1][1][1][:3])

def sh(cmd, **kw): return subprocess.run(cmd, capture_output=True, text=True, **kw)

# ================================================================ shuffles
SESSIONS = [("n2", 2, 1, 5), ("n5", 5, 1, 5), ("n10", 10, 1, 5), ("n24", 24, 1, 5),
            ("k2", 7, 2, 5),      # two mix-servers: IVXV verifies server 01 only
            ("w1", 5, 1, 1)]      # key width 1: IVXV's reader requires 5
def gen_sessions():
    env = {**os.environ, "JAVA_HOME": JDK25, "PATH": JDK25 + "/bin:" + os.environ["PATH"]}
    for name, n, k, kw in SESSIONS:
        out = os.path.join(W, "sessions", name)
        if not os.path.isdir(out):
            r = sh([os.path.join(here, "gen_session.sh"), VMN, VMN_SRC, out, str(n), str(k), str(kw), f"ivxv-{SEED}-{name}"], env=env)
            if r.returncode: sys.exit(r.stdout + r.stderr)

def copy_session(src, name):
    d = os.path.join(CASES, "shuffle", name)
    if os.path.exists(d): shutil.rmtree(d)
    os.makedirs(d); shutil.copy(os.path.join(src, "protInfo.xml"), d); shutil.copytree(os.path.join(src, "default"), os.path.join(d, "default"))
    return d

def leaves(t, path=()):
    if t[0] == "L": yield path; return
    for i, c in enumerate(t[1]): yield from leaves(c, path + (i,))
def tget(t, path):
    for i in path: t = t[1][i]
    return t
def tset(t, path, new):
    if not path: return new
    c = list(t[1]); c[path[0]] = tset(c[path[0]], path[1:], new); return ("N", c)

FILES = ["Ciphertexts.bt", "ShuffledCiphertexts.bt", "FullPublicKey.bt", "proofs/Ciphertexts01.bt",
         "proofs/PermutationCommitment01.bt", "proofs/PoSCommitment01.bt", "proofs/PoSReply01.bt"]
def shuffle_cases():
    cases = []   # (name, dir, expected, source, description)
    for name, n, k, kw in SESSIONS:
        base = os.path.join(W, "sessions", name)
        d = copy_session(base, f"{name}-honest")
        exp = "accept" if (k == 1 and kw == 5) else "ivxv-config"
        cases.append((f"{name}-honest", d, exp, "honest", f"vmn session N={n} servers={k} keywidth={kw}"))
        if k != 1 or kw != 5: continue
        S = L.Session(os.path.join(d, "protInfo.xml"), os.path.join(d, "default"))
        def prover(tag, src, expect, what, pi=None, s=None, r=None, wout=None, prove_pi=None, prove_s=None):
            dd = copy_session(base, f"{name}-{tag}")
            S2 = L.Session(os.path.join(dd, "protInfo.xml"), os.path.join(dd, "default"))
            pi = pi if pi is not None else rng.sample(range(n), n)
            s = s if s is not None else [[rng.randrange(Q) for _ in range(kw)] for _ in range(n)]
            r = r if r is not None else [rng.randrange(Q) for _ in range(n)]
            wout = wout if wout is not None else S2.shuffle(rng, pi, s)
            S2.prove(rng, wout, prove_pi if prove_pi is not None else pi, r, prove_s if prove_s is not None else s)
            cases.append((f"{name}-{tag}", dd, expect, src, what))
        prover("ours-honest", "control", "accept", "our prover, honest")
        prover("ours-identity", "control", "accept", "our prover, identity permutation", pi=list(range(n)))
        prover("ours-norerand", "control", "accept", "our prover, no re-encryption", s=[[0] * kw for _ in range(n)])
        pi = rng.sample(range(n), n); s = [[rng.randrange(Q) for _ in range(kw)] for _ in range(n)]
        bad = [list(x) for x in s]; bad[0][0] = (bad[0][0] + 1) % Q
        prover("false-rerand", "false", "reject", "statement re-encrypted with s_0+1, witness s", pi=pi, s=s, wout=S.shuffle(rng, pi, bad))
        if n >= 2:
            dup = list(pi); dup[1] = dup[0]                        # two inputs to one output: not a permutation
            inv = [0] * n
            for i in range(n): inv[dup[i]] = i
            wnp = [S.cmul(S.enc1(s[j]), S.w[inv[j]]) for j in range(n)]
            prover("false-notperm", "false", "reject", "witness is not a permutation", pi=pi, s=s, wout=wnp, prove_pi=dup)
            other = list(pi)
            while other == pi: other = rng.sample(range(n), n)
            prover("false-othershuffle", "false", "reject", "statement is another shuffle", pi=pi, s=s, wout=S.shuffle(rng, other, s))
        w2 = S.shuffle(rng, pi, s); u, v = w2[0]; w2[0] = (u, [v[0] * G % P] + v[1:])
        prover("false-plaintext", "false", "reject", "plaintext of output 0 multiplied by g", pi=pi, s=s, wout=w2)
        # field mutants: one random occurrence of every field of every file
        for f in FILES:
            t = L.bt_load(os.path.join(base, "default", f))
            # fields: PoSReply/PoSCommitment by top-level child and depth, the others by depth
            byfield = collections.defaultdict(list)
            for path in leaves(t): byfield[(path[0] if f.startswith("proofs/PoS") and path else None, len(path))].append(path)
            scalar = f.endswith("PoSReply01.bt")
            for key, paths in sorted(byfield.items(), key=lambda kv: str(kv[0])):
                path = rng.choice(paths); x = L.ival(tget(t, path)); k_ = len(tget(t, path)[1])
                ops = ([("+1", (x + 1) % Q), ("zero", 0), ("negated", (-x) % Q), ("random", rng.randrange(Q))] if scalar else
                       [("times g", x * G % P), ("one", 1), ("inverse", pow(x, -1, P)), ("random", pow(G, rng.randrange(Q), P))])
                for opn, nv in ops:
                    if nv == x: continue
                    tag = f"{f.replace('/', '_')}-{key[0] if key[0] is not None else ''}d{key[1]}-{opn.replace(' ', '')}"
                    dd = copy_session(base, f"{name}-m-{tag}")
                    L.bt_save(os.path.join(dd, "default", f), tset(t, path, L.leaf(k_, nv)))
                    if f == "proofs/Ciphertexts01.bt":   # keep the last server's output equal to ShuffledCiphertexts
                        shutil.copy(os.path.join(dd, "default", f), os.path.join(dd, "default", "ShuffledCiphertexts.bt"))
                    cases.append((f"{name}-m-{tag}", dd, "reject", "field", f"{f} leaf {path}: {opn}"))
        # single-check isolation of the B equations: k_B is a reply (not hashed), so changing
        # k_B,i breaks only the equation B_i^v B'_i = g^{k_B,i} B_{i-1}^{k_E,i} (B_{-1} = h_0)
        rep_t = L.bt_load(os.path.join(base, "default", "proofs/PoSReply01.bt"))
        for idx in sorted({0, 1, n - 1}):
            kb = L.ival(rep_t[1][1][1][idx]); k_ = len(rep_t[1][1][1][idx][1])
            for opn, nv in [("+1", (kb + 1) % Q), ("random", rng.randrange(Q))]:
                dd = copy_session(base, f"{name}-single-kB{idx}-{opn}")
                L.bt_save(os.path.join(dd, "default", "proofs/PoSReply01.bt"), tset(rep_t, (1, idx), L.leaf(k_, nv)))
                cases.append((f"{name}-single-kB{idx}-{opn}", dd, "reject", "single-check",
                              f"k_B,{idx} {opn}: only the B equation at index {idx} fails"))
        # structural and encoding mutants
        def struct_case(tag, what, fn, expect="reject"):
            dd = copy_session(base, f"{name}-s-{tag}"); fn(os.path.join(dd, "default")); cases.append((f"{name}-s-{tag}", dd, expect, "structural", what))
        def edit(f, g_):
            def fn(dd):
                t = L.bt_load(os.path.join(dd, f)); L.bt_save(os.path.join(dd, f), g_(t))
            return fn
        def both_outputs(g_):
            def fn(dd):
                for f in ("ShuffledCiphertexts.bt", "proofs/Ciphertexts01.bt"):
                    t = L.bt_load(os.path.join(dd, f)); L.bt_save(os.path.join(dd, f), g_(t))
            return fn
        def swap_outputs(t):   # swap ciphertexts 0 and 1 in every component array
            def sw(node):
                if node[0] == "N" and node[1] and node[1][0][0] == "L":
                    c = list(node[1]); c[0], c[1] = c[1], c[0]; return ("N", c)
                return ("N", [sw(x) for x in node[1]])
            return sw(t)
        if n >= 2: struct_case("swap-outputs", "two output ciphertexts swapped", both_outputs(swap_outputs))
        pc = "proofs/PermutationCommitment01.bt"; pos = "proofs/PoSCommitment01.bt"; rep = "proofs/PoSReply01.bt"
        struct_case("u-drop", "permutation commitment one element short", edit(pc, lambda t: ("N", t[1][:-1])))
        struct_case("u-dup", "permutation commitment one element long", edit(pc, lambda t: ("N", t[1] + [t[1][-1]])))
        struct_case("B-drop", "B one element short", edit(pos, lambda t: tset(t, (0,), ("N", t[1][0][1][:-1]))))
        struct_case("kE-dup", "k_E one element long", edit(rep, lambda t: tset(t, (4,), ("N", t[1][4][1] + [t[1][4][1][-1]]))))
        struct_case("kF-drop", "k_F one component short", edit(rep, lambda t: tset(t, (5,), ("N", t[1][5][1][:-1]))))
        struct_case("pk-width", "public key one component short", edit("FullPublicKey.bt", lambda t: ("N", [("N", c[1][:-1]) for c in t[1]])))
        lp = lambda t, path: tget(t, path)
        def setv(f, path, val, width=None):
            def g_(t):
                k_ = width if width is not None else len(lp(t, path)[1])
                return tset(t, path, ("L", val.to_bytes(k_, "big", signed=True)))
            return edit(f, g_)
        a_path = (1,)   # A' in PoSCommitment
        A1 = L.ival(lp(L.bt_load(os.path.join(base, "default", pos)), a_path))
        struct_case("A-p", "A' := p", setv(pos, a_path, P))
        struct_case("A-zero", "A' := 0", setv(pos, a_path, 0))
        struct_case("A-nonsquare", "A' := p - A' (not in G_q)", setv(pos, a_path, P - A1))
        struct_case("A-plus-p", "A' := A' + p (non-reduced)", setv(pos, a_path, A1 + P, width=L.width_of(A1 + P)))
        struct_case("A-negative", "A' := -A'", setv(pos, a_path, -A1))
        struct_case("A-leading-zero", "A' with an extra leading zero byte", setv(pos, a_path, A1, width=len(lp(L.bt_load(os.path.join(base, "default", pos)), a_path)[1]) + 1))
        kA = L.ival(lp(L.bt_load(os.path.join(base, "default", rep)), (0,)))
        struct_case("kA-q", "k_A := k_A + q", setv(rep, (0,), kA + Q, width=L.width_of(kA + Q)))
        struct_case("kA-negative", "k_A := k_A - q", setv(rep, (0,), kA - Q))
        struct_case("trailing", "trailing byte after the PoSReply byte tree",
                    lambda dd: open(os.path.join(dd, rep), "ab").write(b"\x00"))
        struct_case("truncated", "PoSCommitment byte tree truncated",
                    lambda dd: open(os.path.join(dd, pos), "r+b").truncate(os.path.getsize(os.path.join(dd, pos)) - 1))
        struct_case("auxsid", "auxsid changed (the prefix ρ changes)", lambda dd: open(os.path.join(dd, "auxsid"), "w").write("other"))
        struct_case("type-mixing", "session type 'mixing'", lambda dd: open(os.path.join(dd, "type"), "w").write("mixing"))
        struct_case("input-swap", "two input ciphertexts swapped", edit("Ciphertexts.bt", swap_outputs) if n >= 2 else (lambda dd: None))
    return cases

def run_shuffle(cases):
    env25 = {**os.environ, "JAVA_HOME": JDK25, "VERIFICATUM_RANDOM_SOURCE": os.path.join(W, "vmnv_rs"),
             "VERIFICATUM_RANDOM_SEED": os.path.join(W, "vmnv_rseed")}
    def vmnv(c):
        # vmnv 3.1.0 exits 0 on a shuffling session whose proofs fail: it prints "Verify proof
        # of shuffle... failed.", replaces the party's output by its input and reports "Too few
        # proofs are valid!" through failInfo, which only prints. Its verdict is therefore read
        # from its (verbose) output; the exit status is recorded separately.
        r = sh([os.path.join(VMN, "bin/vmnv"), "-shuffle", "-e", "-v", os.path.join(c[1], "protInfo.xml"), os.path.join(c[1], "default")], env=env25)
        out = r.stdout + r.stderr
        lines = out.strip().splitlines()
        failed = [l for l in lines if l.rstrip().endswith("failed.") or l.startswith("-->")]
        verdict = "accept" if r.returncode == 0 and not failed else "reject"
        msg = (failed[-1] if failed else (lines[-1] if lines else "")).strip()
        msg = re.sub(r"after\s+\d+h\s+\d+m\s+\d+s\s+\(\d+ ms\)", "after (time)", msg)[:120]   # deterministic tables
        return verdict, msg, r.returncode
    def ours(c):
        r = sh([OURS, "shuffle", os.path.join(c[1], "protInfo.xml"), os.path.join(c[1], "default")])
        return "accept" if r.returncode == 0 else "reject", (r.stdout.strip().splitlines() or [""])[-1][:120]
    lst = os.path.join(W, "shuffle-cases.tsv")
    open(lst, "w").write("".join(f"{os.path.join(c[1], 'protInfo.xml')}\t{os.path.join(c[1], 'default')}\n" for c in cases))
    r = sh([JDK21 + "/bin/java", "-cp", IVXV_CP, "ee.ivxv.audit.shuffle.IvxvShuffleDiff", lst])
    iv = [l for l in r.stdout.splitlines()]
    assert len(iv) == len(cases), r.stderr[-2000:]
    with concurrent.futures.ThreadPoolExecutor(JOBS) as ex:
        vm = list(ex.map(vmnv, cases)); ou = list(ex.map(ours, cases))
    rows = []
    for c, a, b, o in zip(cases, vm, iv, ou):
        nt, th = b.split("\t")
        ivv = "accept" if nt.split("|")[0] == "true" else "reject"
        ivt = "accept" if th.split("|")[0] == "true" else "reject"
        rows.append(dict(component="shuffle", name=c[0], source=c[3], expected=c[2], desc=c[4], vmnv=a[0], ivxv=ivv, ivxv_threaded=ivt, ours=o[0],
                         vmnv_exit=a[2], vmnv_msg=a[1], ivxv_msg=(nt.split("|") + [""])[1][:120], ours_msg=o[1]))
    return rows

# ===================================================== Java decryption proofs
EIDS = ["", "KOV2025", "E" * 300]
def dec_statements():
    st = []
    for i in range(12):
        x = rng.randrange(1, Q); y = pow(G, x, P); m = pow(G, rng.randrange(Q), P); r = rng.randrange(Q)
        st.append((P, G, EIDS[i % 3], x, pow(G, r, P), m * pow(y, r, P) % P))
    return st
def dec_cases():
    fx = os.path.join(here, "fixtures", "dec-statements.tsv"); fp = os.path.join(here, "fixtures", "dec-proofs.tsv")
    if not os.path.exists(fp) or os.environ.get("REGEN"):
        os.makedirs(os.path.dirname(fx), exist_ok=True)
        open(fx, "w").write("".join("\t".join(map(str, s)) + "\n" for s in dec_statements()))
        r = sh([JDK21 + "/bin/java", "-cp", IVXV_CP, "ee.ivxv.common.crypto.elgamal.IvxvDecDiff", "prove", fx])
        if r.returncode: sys.exit(r.stderr)
        open(fp, "w").write(r.stdout)
    sts = [l.rstrip("\n").split("\t") for l in open(fx)]
    prs = [l.split() for l in open(fp)]
    cases = []   # (name, (pk, ct, msg, proof) hex, expected, source, desc)
    enc = lambda p, g, eid, y, c1, c2, d, a, b, s: (L.ivxv_pk_bytes(p, g, eid, y).hex(), L.ivxv_ct_bytes(c1, c2).hex(),
                                                   L.der_int(d).hex(), L.der_seq(L.der_int(a), L.der_int(b), L.der_int(s)).hex())
    for i, (st, pr) in enumerate(zip(sts, prs)):
        p, g, eid, x, c1, c2 = int(st[0]), int(st[1]), st[2], int(st[3]), int(st[4]), int(st[5])
        y = pow(g, x, p); d = c2 * pow(pow(c1, x, p), -1, p) % p
        cases.append((f"d{i}-honest", tuple(pr), "accept", "honest", f"IVXV provableDecrypt, eid len {len(eid)}"))
        a, b, s = L.dec_prove(rng, p, Q, g, eid, x, c1, c2, d)
        cases.append((f"d{i}-ours", enc(p, g, eid, y, c1, c2, d, a, b, s), "accept", "control", "our prover"))
        if i == 0:   # degenerate statements
            for tag, (xx, cc1, cc2, what) in {"one-blind": (x, 1, d, "c1 = 1 (randomness 0)"), "plain-one": (x, c1, pow(c1, x, p), "plaintext 1"),
                                               "x-one": (1, c1, c2, "secret key 1")}.items():
                yy = pow(g, xx, p); dd_ = cc2 * pow(pow(cc1, xx, p), -1, p) % p
                aa, bb, ss = L.dec_prove(rng, p, Q, g, eid, xx, cc1, cc2, dd_)
                cases.append((f"d{i}-ours-{tag}", enc(p, g, eid, yy, cc1, cc2, dd_, aa, bb, ss), "accept", "control", what))
        # false statements, every challenge from the transcript
        a, b, s = L.dec_prove(rng, p, Q, g, eid, x, c1, c2, d * g % p)
        cases.append((f"d{i}-false-plaintext", enc(p, g, eid, y, c1, c2, d * g % p, a, b, s), "reject", "false", "plaintext d*g (only c1^s = a (c2/d)^k fails)"))
        x2 = rng.randrange(1, Q); d2 = c2 * pow(pow(c1, x2, p), -1, p) % p
        a, b, s = L.dec_prove(rng, p, Q, g, eid, x, c1, c2, d2, wrong_x=x2)
        cases.append((f"d{i}-false-key", enc(p, g, eid, y, c1, c2, d2, a, b, s), "reject", "false", "decrypted under another key (only g^s = b y^k fails)"))
        if i < 2:   # values outside the group / non-reduced, with consistent proofs
            for tag, dd_, what in [("d-neg", (p - d) % p, "plaintext p - d (not in G_q), proof with its challenge"),
                                   ("d-plus-p", d + p, "plaintext d + p (non-reduced), proof with its challenge")]:
                t = rng.randrange(Q); aa, bb = pow(c1, t, p), pow(g, t, p)
                k = L.dec_challenge(L.dec_prefix(p, g, eid, y, c1, c2, dd_), aa, bb, Q)
                ss = (t + k * x) % Q
                cases.append((f"d{i}-ns-{tag}", enc(p, g, eid, y, c1, c2, dd_, aa, bb, ss), "either", "false", what))
            t = rng.randrange(Q); aa, bb = pow(c1, t, p) + p, pow(g, t, p)
            k = L.dec_challenge(L.dec_prefix(p, g, eid, y, c1, c2, d), aa, bb, Q); ss = (t + k * x) % Q
            cases.append((f"d{i}-ns-a-plus-p", enc(p, g, eid, y, c1, c2, d, aa, bb, ss), "either", "false", "announcement a + p (non-reduced), proof with its challenge"))
        # field mutants of the honest IVXV proof
        pp, gg, ee, yy, cc1, cc2, dd_, aa, bb, ss = L.parse_dec_case(*pr)
        fields = dict(y=yy, c1=cc1, c2=cc2, d=dd_, a=aa, b=bb)
        for fname, val in fields.items():
            for opn, nv in [("times g", val * g % p), ("one", 1), ("inverse", pow(val, -1, p)), ("random", pow(g, rng.randrange(Q), p))]:
                if nv == val: continue
                vals = dict(fields); vals[fname] = nv
                cases.append((f"d{i}-m-{fname}-{opn.replace(' ', '')}", enc(pp, gg, ee, vals["y"], vals["c1"], vals["c2"], vals["d"], vals["a"], vals["b"], ss),
                              "reject", "field", f"{fname}: {opn}"))
        for opn, nv in [("+1", (ss + 1) % Q), ("zero", 0), ("negated", (-ss) % Q), ("random", rng.randrange(Q))]:
            cases.append((f"d{i}-m-s-{opn}", enc(pp, gg, ee, yy, cc1, cc2, dd_, aa, bb, nv), "reject", "field", f"s: {opn}"))
        cases.append((f"d{i}-m-eid", enc(pp, gg, ee + "X", yy, cc1, cc2, dd_, aa, bb, ss), "reject", "field", "election identifier changed"))
        cases.append((f"d{i}-m-swap-ab", enc(pp, gg, ee, yy, cc1, cc2, dd_, bb, aa, ss), "reject", "field", "a and b swapped"))
        if i == 0:   # encodings of the honest proof
            pk_, ct_, msg_, pf_ = pr
            ab = bytes.fromhex(pf_)
            cases.append((f"d{i}-e-trailing", (pk_, ct_, msg_, pf_ + "00"), "reject", "structural", "trailing byte after the proof"))
            cases.append((f"d{i}-e-s-plus-q", enc(pp, gg, ee, yy, cc1, cc2, dd_, aa, bb, ss + Q), "either", "structural", "s + q (same residue)"))
            cases.append((f"d{i}-e-s-neg", enc(pp, gg, ee, yy, cc1, cc2, dd_, aa, bb, ss - Q), "either", "structural", "s - q (same residue)"))
            content = dd_.to_bytes(dd_.bit_length() // 8 + 1, "big", signed=True)   # the minimal two's complement bytes
            cases.append((f"d{i}-e-msg-nonminimal", (pk_, ct_, L.tlv(0x02, b"\x00" + content).hex(), pf_),
                          "either", "structural", "plaintext INTEGER with an extra leading zero byte"))
            cases.append((f"d{i}-e-wrong-oid", (pk_, ct_.replace(L.der_oid(L.OID_MODP).hex(), L.der_oid("1.3.6.1.4.1.99999.1").hex()), msg_, pf_),
                          "reject", "structural", "ciphertext OID of the EC scheme"))
            cases.append((f"d{i}-e-d-zero", (pk_, ct_, L.der_int(0).hex(), pf_), "reject", "structural", "plaintext 0"))
            cases.append((f"d{i}-e-d-p", (pk_, ct_, L.der_int(p).hex(), pf_), "reject", "structural", "plaintext p"))
    return cases

def run_dec(cases):
    lst = os.path.join(W, "dec-cases.tsv")
    open(lst, "w").write("".join("\t".join(c[1]) + "\n" for c in cases))
    r = sh([JDK21 + "/bin/java", "-cp", IVXV_CP, "ee.ivxv.common.crypto.elgamal.IvxvDecDiff", "verify", lst])
    iv = r.stdout.splitlines(); assert len(iv) == len(cases), r.stderr[-2000:]
    js, idx = [], []
    for i, c in enumerate(cases):
        try:
            p, g, eid, y, c1, c2, d, a, b, s = L.parse_dec_case(*c[1])
            js.append({k: str(v) for k, v in dict(g=g, y=y, c1=c1, c2=c2, d=d, a=a, b=b, s=s).items()} |
                      {"prefix": L.dec_prefix(p, g, eid, y, c1, c2, d).hex(), "p": str(p)}); idx.append(i)
        except (L.DerError, ValueError, UnicodeDecodeError) as e:
            pass
    jf = os.path.join(W, "dec-cases.json"); json.dump(js, open(jf, "w"))
    r2 = sh([OURS, "dec", jf]); oo = r2.stdout.splitlines(); assert len(oo) == len(js), r2.stderr
    ours = ["false\tparser: DER"] * len(cases)
    for i, o in zip(idx, oo): ours[i] = o
    # the group of the case must be the certified one; main.exe checks membership in it
    for i, c in enumerate(cases):
        if i in idx:
            pv = int(js[idx.index(i)]["p"])
            if pv != P: ours[i] = "false\tparser: not the certified group"
    rows = []
    for c, a, o in zip(cases, iv, ours):
        rows.append(dict(component="dec", name=c[0], source=c[3], expected=c[2], desc=c[4],
                         ivxv="accept" if a.split("\t")[0] == "true" else "reject", ours="accept" if o.split("\t")[0] == "true" else "reject",
                         ivxv_msg=(a.split("\t") + [""])[1][:120], ours_msg=(o.split("\t") + [""])[1][:120]))
    return rows

# ========================================================== Go core proofs
def go_cases():
    p, q = L.P14, L.Q14
    st = []
    for i, salt in enumerate([None, b"", b"\x01\x02\x03", b"ivxv-diff" * 10, None, b"s"]):
        x = rng.randrange(1, q); y = pow(2, x, p); m = pow(2, rng.randrange(q), p); r = rng.randrange(q)
        st.append((x, pow(2, r, p), m * pow(y, r, p) % p, rng.randrange(1, q), salt))
    f = os.path.join(W, "go-statements.tsv")
    open(f, "w").write("".join(f"{x}\t{c1}\t{c2}\t{s}\t{'-' if salt is None else salt.hex()}\n" for x, c1, c2, s, salt in st))
    r = sh([GOBIN, "prove", f]); prs = [l.split("\t") for l in r.stdout.splitlines()]
    assert len(prs) == len(st), r.stderr
    cases = []   # (name, (pk, proof, salt), expected, source, desc)
    sx = lambda salt: "-" if salt is None else salt.hex()
    gp = lambda y, c1, c2, d, e, s: (L.der_int(y).hex(), L.go_proof_der(c1, c2, d, e, s).hex())
    for i, ((x, c1, c2, _, salt), (pk, pf)) in enumerate(zip(st, prs)):
        y = pow(2, x, p); d = c2 * pow(pow(c1, x, p), -1, p) % p
        cases.append((f"g{i}-honest", (pk, pf, sx(salt)), "accept", "honest", f"Go Prove, salt {sx(salt)[:12]}"))
        e, s = L.go_prove(rng, x, c1, c2, d, salt)
        cases.append((f"g{i}-ours", (*gp(y, c1, c2, d, e, s), sx(salt)), "accept", "control", "our prover"))
        cases.append((f"g{i}-false-salt", (pk, pf, (salt or b"").hex() + "aa"), "reject", "false", "verified with another salt"))
        e, s = L.go_prove(rng, x, c1, c2, d * 2 % p, salt)
        cases.append((f"g{i}-false-plaintext", (*gp(y, c1, c2, d * 2 % p, e, s), sx(salt)), "reject", "false", "plaintext d*g"))
        x2 = rng.randrange(1, q); d2 = c2 * pow(pow(c1, x2, p), -1, p) % p
        e, s = L.go_prove(rng, x, c1, c2, d2, salt, wrong_x=x2)
        cases.append((f"g{i}-false-key", (*gp(y, c1, c2, d2, e, s), sx(salt)), "reject", "false", "decrypted under another key"))
        yy, cc1, cc2, dd, ee, ss = L.go_parse_proof(pk, pf)
        vals = dict(y=yy, c1=cc1, c2=cc2, d=dd)
        for fname, val in vals.items():
            for opn, nv in [("times g", val * 2 % p), ("one", 1), ("inverse", pow(val, -1, p)), ("random", pow(2, rng.randrange(q), p))]:
                if nv == val: continue
                v2 = dict(vals); v2[fname] = nv
                cases.append((f"g{i}-m-{fname}-{opn.replace(' ', '')}", (*gp(v2["y"], v2["c1"], v2["c2"], v2["d"], ee, ss), sx(salt)), "reject", "field", f"{fname}: {opn}"))
        for fname in ("e", "s"):
            for opn, f_ in [("+1", lambda v: (v + 1) % q), ("zero", lambda v: 0), ("negated", lambda v: (-v) % q), ("random", lambda v: rng.randrange(q))]:
                e2, s2 = (f_(ee), ss) if fname == "e" else (ee, f_(ss))
                cases.append((f"g{i}-m-{fname}-{opn}", (*gp(yy, cc1, cc2, dd, e2, s2), sx(salt)), "reject", "field", f"{fname}: {opn}"))
        if i == 0:   # encodings of the honest proof: same group elements, other integers
            for tag, (y_, c1_, c2_, d_, e_, s_), what in [
                    ("y-plus-p", (yy + p, cc1, cc2, dd, ee, ss), "public key y + p (non-reduced)"),
                    ("c1-plus-p", (yy, cc1 + p, cc2, dd, ee, ss), "ciphertext c1 + p (non-reduced)"),
                    ("d-plus-p", (yy, cc1, cc2, dd + p, ee, ss), "decryption d + p (non-reduced)"),
                    ("c1-negative", (yy, cc1 - p, cc2, dd, ee, ss), "c1 - p (negative, same residue)"),
                    ("s-plus-q", (yy, cc1, cc2, dd, ee, ss + q), "response s + q"),
                    ("e-plus-q", (yy, cc1, cc2, dd, ee + q, ss), "challenge e + q"),
                    ("d-nonsquare", (yy, cc1, cc2, p - dd, ee, ss), "decryption p - d (not in G_q)"),
                    ("d-zero", (yy, cc1, cc2, 0, ee, ss), "decryption 0"),
                    ("d-p", (yy, cc1, cc2, p, ee, ss), "decryption p")]:
                cases.append((f"g{i}-e-{tag}", (*gp(y_, c1_, c2_, d_, e_, s_), sx(salt)), "either", "structural", what))
            cases.append((f"g{i}-e-trailing", (pk, pf + "00", sx(salt)), "reject", "structural", "trailing byte after the proof"))
    return cases

def run_go(cases):
    lst = os.path.join(W, "go-cases.tsv")
    open(lst, "w").write("".join("\t".join(c[1]) + "\n" for c in cases))
    r = sh([GOBIN, "verify", lst]); gv = r.stdout.splitlines(); assert len(gv) == len(cases), r.stderr
    js, idx = [], []
    for i, c in enumerate(cases):
        pk, pf, salt = c[1]
        try:
            y, c1, c2, d, e, s = L.go_parse_proof(pk, pf)
            js.append({k: str(v) for k, v in dict(y=y, c1=c1, c2=c2, d=d, e=e, s=s).items()} |
                      {"prefix": L.go_prefix(y, c1, c2, d).hex(), "suffix": L.go_suffix(None if salt == "-" else bytes.fromhex(salt)).hex()}); idx.append(i)
        except (L.DerError, ValueError):
            pass
    jf = os.path.join(W, "go-cases.json"); json.dump(js, open(jf, "w"))
    r2 = sh([OURS, "nizkp", jf]); oo = r2.stdout.splitlines(); assert len(oo) == len(js), r2.stderr
    ours = ["false\tparser: DER"] * len(cases)
    for i, o in zip(idx, oo): ours[i] = o
    return [dict(component="go", name=c[0], source=c[3], expected=c[2], desc=c[4],
                 ivxv="accept" if a.split("\t")[0] == "true" else "reject", ours="accept" if o.split("\t")[0] == "true" else "reject",
                 ivxv_msg=(a.split("\t") + [""])[1][:120], ours_msg=(o.split("\t") + [""])[1][:120])
            for c, a, o in zip(cases, gv, ours)]

# =============================================================== reporting
def report(rows):
    cols = ["component", "name", "source", "expected", "vmnv", "ivxv", "ivxv_threaded", "ours", "vmnv_exit", "desc", "vmnv_msg", "ivxv_msg", "ours_msg"]
    for comp in ("shuffle", "dec", "go"):
        with open(os.path.join(RES, f"{comp}.tsv"), "w") as f:
            f.write("\t".join(cols) + "\n")
            for r in rows:
                if r["component"] == comp: f.write("\t".join(str(r.get(c, "")) for c in cols) + "\n")
    summ = collections.Counter()
    for r in rows:
        vs = [r[k] for k in ("vmnv", "ivxv", "ivxv_threaded", "ours") if k in r]
        agree = len(set(vs)) == 1
        summ[(r["component"], r["source"], r["expected"], "/".join(f"{k}={r[k]}" for k in ("vmnv", "ivxv", "ivxv_threaded", "ours") if k in r), "agree" if agree else "DISAGREE")] += 1
    with open(os.path.join(RES, "summary.tsv"), "w") as f:
        f.write("component\tsource\texpected\tverdicts\tcomparison\tcases\n")
        for k, n in sorted(summ.items()): f.write("\t".join(k) + f"\t{n}\n")
    zero_fail = [r["name"] for r in rows if r.get("vmnv_exit") == 0 and r.get("vmnv") == "reject"]
    with open(os.path.join(RES, "summary.tsv"), "a") as f:
        f.write(f"shuffle\tvmnv exit status 0 on a rejected session\t-\t-\t-\t{len(zero_fail)}\n")
    print(open(os.path.join(RES, "summary.tsv")).read())
    print("disagreements and unexpected verdicts:")
    for r in rows:
        vs = {k: r[k] for k in ("vmnv", "ivxv", "ivxv_threaded", "ours") if k in r}
        unexpected = r["expected"] in ("accept", "reject") and any(v != r["expected"] for v in vs.values())
        if len(set(vs.values())) > 1 or unexpected:
            print(f"  {r['component']:7} {r['name']:40} expected={r['expected']:11} " + " ".join(f"{k}={v}" for k, v in vs.items()) + f"  {r['desc']}")
            for k in ("vmnv_msg", "ivxv_msg", "ours_msg"):
                if r.get(k): print(f"{'':10}{k}: {r[k]}")

if __name__ == "__main__":
    gen_sessions()
    rows = run_shuffle(shuffle_cases()) + run_dec(dec_cases()) + run_go(go_cases())
    report(rows)
