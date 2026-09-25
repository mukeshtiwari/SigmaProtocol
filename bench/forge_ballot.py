"""Usage: python3 forge_ballot.py IACR2024.txt IACR2024-forged.txt ../src/Examples/HeliosTallyIns.v

Forge a Helios ballot whose first choice encrypts 5 (not 0 or 1) with a
disjunctive proof whose per-branch challenges were chosen by the forger.
The verification equations hold for both branches, so any verifier that does
not recompute the overall challenge as SHA-1(A0,B0,A1,B1) accepts it."""
import json, re, random, sys
src, dst = sys.argv[1], sys.argv[2]
ins = open(sys.argv[3]).read()
def const(name):
    return int(re.search(r"Definition %s : Z :=\s*([0-9]+)" % name, ins).group(1))
p, q, g, h = const("p"), const("q"), const("gval"), const("hval2024")
random.seed(2027)
lines = open(src).read().split("\n")
d = json.loads(lines[0])
ans = d["vote"]["answers"][0]
r = random.randrange(1, q)
alpha = pow(g, r, p)
beta = pow(g, 5, p) * pow(h, r, p) % p
ans["choices"][0] = {"alpha": str(alpha), "beta": str(beta)}
proofs = []
for m in (1, g):
    c, rr = random.randrange(1, q), random.randrange(1, q)
    A = pow(g, rr, p) * pow(alpha, q - c, p) % p
    beta_over_m = beta * pow(m, p - 2, p) % p
    B = pow(h, rr, p) * pow(beta_over_m, q - c, p) % p
    assert pow(g, rr, p) == A * pow(alpha, c, p) % p
    assert pow(h, rr, p) == B * pow(beta_over_m, c, p) % p
    proofs.append({"challenge": str(c), "commitment": {"A": str(A), "B": str(B)}, "response": str(rr)})
ans["individual_proofs"][0] = proofs
lines[0] = json.dumps(d)
open(dst, "w").write("\n".join(lines))
print("forged ballot written; first choice encrypts g^5; sub-challenges sum =", (int(proofs[0]["challenge"]) + int(proofs[1]["challenge"])) % q)
