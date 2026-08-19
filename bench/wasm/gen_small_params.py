#!/usr/bin/env python3
"""Generate small Schnorr-group parameters (p = k*q + 1, generator g of the
order-q subgroup, public key h = g^x) plus fixed benchmark randomness,
formatted as Rocq definitions for WasmBenchSmallDefs.v."""
import random

random.seed(42)

def is_prime(n, rounds=64):
    if n < 2:
        return False
    for sp in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if n % sp == 0:
            return n == sp
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for _ in range(rounds):
        a = random.randrange(2, n - 1)
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True

def gen_group(qbits, pbits):
    while True:
        q = random.getrandbits(qbits) | (1 << (qbits - 1)) | 1
        if not is_prime(q):
            continue
        # find even k so that p = k*q + 1 is prime and has pbits bits
        kbits = pbits - qbits
        for _ in range(20000):
            k = (random.getrandbits(kbits) | (1 << (kbits - 1))) & ~1
            p = k * q + 1
            if p.bit_length() == pbits and is_prime(p):
                # generator of the order-q subgroup
                for h0 in range(2, 100):
                    g = pow(h0, k, p)
                    if g != 1:
                        assert pow(g, q, p) == 1
                        return p, q, k, g
        # retry with a new q

def emit(name, qbits, pbits, n=7):
    p, q, k, g = gen_group(qbits, pbits)
    x = random.randrange(1, q)          # secret key
    h = pow(g, x, p)                    # public key
    rs = [random.randrange(1, q) for _ in range(n)]
    cs = [random.randrange(1, q) for _ in range(n)]
    uscs = [[random.randrange(1, q) for _ in range(3)] for _ in range(n)]
    ms = [1, 0, 1, 0, 1, 1, 0][:n]
    print(f"(* ---- {name}: {pbits}-bit p, {qbits}-bit q ---- *)")
    print(f"q := {q}")
    print(f"p := {p}")
    print(f"k := {k}")
    print(f"g := {g}")
    print(f"h := {h}  (* = g^{x} mod p *)")
    print(f"rs := {rs}")
    print(f"cs := {cs}")
    print(f"uscs := {uscs}")
    print(f"ms := {ms}")
    print()

emit("small64", 32, 64)
emit("small128", 64, 128)
emit("small256", 128, 256)
