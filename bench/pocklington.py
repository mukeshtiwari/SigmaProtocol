#!/usr/bin/env python3
"""Generate a Coqprime Pocklington certificate for a prime, certifying
recursively every prime factor it uses. Requires sympy.

Two output styles. The default uses Coqprime.PrimalityTest.PocklingtonCertificat,
whose checker computes with Rocq's Z (no axioms; fine up to a few hundred
bits, as fiat-crypto's Spec/Curve25519.v does). With --bignum the
certificate uses Coqprime.PocklingtonRefl, whose checker computes with
Bignums (faster for large primes but depends on the primitive-integer
axioms Uint63Axioms.*).

usage: pocklington.py EXPRESSION LEMMA_NAME > file.v
  e.g. pocklington.py "2**256-189" prime_q_eg > src/Examples/primeQEG.v

For each prime N the certificate uses the largest prime-power factors of
N - 1 (always including the power of 2) until their product F1 satisfies
the bound of Coqprime's test_pock, N < ((2 F1 + r + 1) F1 + r) F1 + 1 with
r = (N - 1) / F1 mod 2 F1, and a witness a with a^(N-1) = 1 and
gcd(a^((N-1)/p) - 1, N) = 1 for every prime p of the factorisation."""
import sys, math
from sympy import factorint, isprime
from sympy.ntheory.primetest import isprime as sp_isprime
def isqrt(n): return math.isqrt(n)
def certificate(N, certs, order):
    """append certificates for N and all needed primes to certs (dict), order list"""
    if N in certs: return
    if N in (2, 3):
        certs[N] = ('proof', N); order.append(N); return
    Nm1 = N - 1
    fac = factorint(Nm1)   # full factorisation
    # choose F1: include the full power of 2, then largest primes until condition holds
    primes = sorted(fac.items(), key=lambda kv: -kv[0])
    dec = [(2, fac[2])]
    F1 = 2**fac[2]
    def ok(F1):
        R1 = Nm1 // F1
        if R1 % 2 == 0: return False
        s, r = divmod(R1, 2*F1)
        return N < ((2*F1 + r + 1)*F1 + r)*F1 + 1
    for p, e in primes:
        if p == 2: continue
        if ok(F1): break
        dec.append((p, e)); F1 *= p**e
    assert ok(F1), "insufficient factorisation"
    R1 = Nm1 // F1
    s, r = divmod(R1, 2*F1)
    x = r*r - 8*s
    if s == 0: sqrt = 1
    elif x < 0: sqrt = 1
    else:
        sq = isqrt(x)
        assert sq*sq != x, "perfect square: composite?"
        sqrt = sq
    # witness a
    a = 2
    while True:
        if pow(a, Nm1, N) == 1:
            prod = 1
            for p, _ in dec:
                prod = prod * (pow(a, Nm1//p, N) - 1) % N
            if math.gcd(prod, N) == 1: break
        a += 1
    certs[N] = ('pock', N, a, dec, sqrt); order.append(N)
    for p, _ in dec:
        certificate(p, certs, order)
bignum = "--bignum" in sys.argv
sys.argv = [a for a in sys.argv if a != "--bignum"]

def emit(N, name):
    certs = {}; order = []
    certificate(N, certs, order)
    # a certificate must come after every certificate whose factorisation uses it
    order = sorted(order, reverse=True)
    lines = []
    for n in order:
        c = certs[n]
        if c[0] == 'proof': lines.append("Proof_certif %d %s%d" % (n, "prime" if bignum else "prime_", n))
        else:
            _, n, a, dec, sqrt = c
            dec2 = sorted(dec, key=lambda pe: -pe[0])
            lines.append("Pock_certif %d %d (%s nil) %d" % (n, a, "".join("(%d, %d)::" % pe for pe in dec2), sqrt))
    head = certs[N]
    body = " ::\n   ".join(lines[1:])
    if bignum:
        return "From Coqprime Require Import PocklingtonRefl.\nLocal Open Scope positive_scope.\n\nLemma %s : prime %d.\nProof.\n apply (Pocklington_refl\n  (%s)\n  (%s ::\n   nil)).\n vm_cast_no_check (refl_equal true).\nQed.\n" % (name, N, lines[0], body)
    return "From Stdlib Require Import ZArith Znumtheory List. Import ListNotations.\nFrom Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.\nLocal Open Scope positive_scope.\n\nLemma %s : prime %d.\nProof.\n simple refine (Pocklington_refl\n  (%s)\n  (%s ::\n   nil) _).\n vm_cast_no_check (@eq_refl bool true).\nQed.\n" % (name, N, lines[0], body)
if __name__ == '__main__':
    N = eval(sys.argv[1]); name = sys.argv[2]
    print(emit(N, name))
