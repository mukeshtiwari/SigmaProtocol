"""Export one Belenios shuffle as (a) a one-shuffle .bel archive for
belenios-tool and (b) a flat .dat for the certified Terelius-Wikström verifier
driver (Executable/Belenioshuffleverifier), so the SAME proof is checked by
both. The .dat maps the Belenios proof onto the public data, announcement,
challenge and response of Crypto/ShuffleTW.v (see rocq_tw.md):

  public      g, pk, h0 = get_generator(-1), hs = get_generator(0..n-1),
              us = cc (permutation commitment), es = uu (batching vector),
              Bs = cc_hat (bridging), ws = input, ws' = output
  announcement A'=t3, C'=t1, D'=t2, B'=tt_hat, F'=(t42,t41)
  challenge    c
  response     [s3; s1; s2; s4] ++ ss_hat ++ ss2

usage: export_tw.py FIXTURE.bel OUT_PREFIX SEED honest|torsion2|torsion8
"""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mix_lib import *

fixture, prefix, seed, mode = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
arch = Archive.load(fixture); el = Election(arch)
rng = random.Random(seed)
ee = nh_input(arch, el)[0]
n = len(ee)
ee2, rr2, psi = gen_shuffle(rng, el.y, ee)
if mode == "torsion2": ee2[0] = (ee2[0][0], add(ee2[0][1], T2))
elif mode == "torsion8": ee2[0] = (ee2[0][0], add(ee2[0][1], T8))
elif mode != "honest": sys.exit("bad mode")
pf = gen_shuffle_proof(rng, el.fingerprint, el.y, ee, ee2, rr2, psi)
(t1, t2, t3, (t41, t42), tt_hat), (s1, s2, s3, s4, ss_hat, ss2), cc, cc_hat = pf

# the batching vector uu that the verifier derives (es), recomputed as in check
uu = nizkp_challenges(n, "shuffle-challenges|" + el.fingerprint + "|"
                      + str_egs(ee) + str_egs(ee2) + str_elts(cc))
str2 = str_elts([t1, t2, t3, t41, t42]) + str_elts(tt_hat)
str3 = str_egs(ee) + str_egs(ee2) + str_elts(cc) + str_elts(cc_hat) + tostr(el.y)
c = nizkp_challenge("shuffle-challenge|" + el.fingerprint + "|" + str2 + str3)

hs = [get_generator(i) for i in range(n)]
h0 = get_generator(-1)

def ph(p): return tostr(p)
def hexs(ps): return " ".join(ph(p) for p in ps)
def decs(xs): return " ".join(str(x % L) for x in xs)

lines = [
    "n %d" % n,
    "g %s" % ph(G),
    "pk %s" % ph(el.y),
    "h0 %s" % ph(h0),
    "hs %s" % hexs(hs),
    "us %s" % hexs(cc),
    "Bs %s" % hexs(cc_hat),
    "es %s" % decs(uu),
    "ws_a %s" % hexs([a for a, _ in ee]),
    "ws_b %s" % hexs([b for _, b in ee]),
    "wsp_a %s" % hexs([a for a, _ in ee2]),
    "wsp_b %s" % hexs([b for _, b in ee2]),
    "Ap %s" % ph(t3),
    "Cp %s" % ph(t1),
    "Dp %s" % ph(t2),
    "Bp %s" % hexs(tt_hat),
    "F1 %s" % ph(t42),
    "F2 %s" % ph(t41),
    "c %d" % (c % L),
    "resp %s" % decs([s3, s1, s2, s4] + ss_hat + ss2),
]
open(prefix + ".dat", "w").write("\n".join(lines) + "\n")
with_shuffles(arch, [(1, compact(shuffle_json([ee2], [pf])))], end=False).save(prefix + ".bel")
port = check_shuffle_proof(el.fingerprint, el.y, ee, ee2, pf)
sub = all(is_subgroup(a) and is_subgroup(b) for a, b in ee2)
print("mode=%s seed=%d port_accepts=%s output_in_subgroup=%s" % (mode, seed, port, sub))
