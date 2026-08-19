#!/usr/bin/env python3
"""Verify an IACR Helios election using Helios's own Python crypto code
(helios/crypto/algs.py from the pinned helios-server submodule, imported
verbatim), as a baseline for the certified OCaml verifier.

Performs the same checks as the certified verifier
(src/Executable/HeliosVerifiercode):
  1. every ballot's per-candidate disjunctive 0/1 encryption proofs,
  2. homomorphic aggregation of the valid ballots,
  3. each trustee's Chaum-Pedersen decryption proofs on the aggregate,
  4. each trustee's Schnorr proof of knowledge of their secret key,
  5. product of trustee public keys == election public key,
  6. g^tally == aggregate_beta / product of decryption factors.

The helios package itself is Django-tainted (helios/__init__.py reads
Django settings), so this script builds a stub package in a temp dir --
empty __init__ files and a one-line to_json (copied from
helios_auth/utils.py) -- and symlinks helios/crypto/algs.py and
helios/crypto/utils.py from the submodule unmodified.

Setup (needs the helios-server submodule and pycryptodome):
  git submodule update --init bench/helios-server
  uv venv .venv-helios --python 3.13
  uv pip install -p .venv-helios/bin/python pycryptodome

Usage:
  .venv-helios/bin/python verify_iacr_python.py \
      ../src/Executable/HeliosDatacode/IACR2024.txt <expected-pk-y>
where <expected-pk-y> is the election public key (decimal), e.g. hval2024
or hval2023 from src/Examples/HeliosTallyIns.v.
"""
import json
import os
import sys
import tempfile
import time

# ---- build the stub package around the submodule's crypto code -------------
HELIOS_SERVER = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             'helios-server')
stub_root = tempfile.mkdtemp(prefix='helios_stub_')
os.makedirs(os.path.join(stub_root, 'helios', 'crypto'))
open(os.path.join(stub_root, 'helios', '__init__.py'), 'w').close()
open(os.path.join(stub_root, 'helios', 'crypto', '__init__.py'), 'w').close()
with open(os.path.join(stub_root, 'helios', 'utils.py'), 'w') as f:
    f.write('import json\n\ndef to_json(d):\n'
            '    return json.dumps(d, sort_keys=True)\n')
for mod in ['algs.py', 'utils.py']:
    os.symlink(os.path.join(HELIOS_SERVER, 'helios', 'crypto', mod),
               os.path.join(stub_root, 'helios', 'crypto', mod))
sys.path.insert(0, stub_root)

from helios.crypto.algs import (EGPublicKey, EGPlaintext, EGCiphertext,
                                EGZKProof, EGZKDisjunctiveProof, DLogProof,
                                EG_disjunctive_challenge_generator,
                                EG_fiatshamir_challenge_generator,
                                DLog_challenge_generator)
from Crypto.Util.number import inverse

data_file = sys.argv[1]
expected_y = int(sys.argv[2])

t_start = time.perf_counter()

# ---- parse the bulletin-board dump ------------------------------------------
ballot_lines, extra = [], []
with open(data_file) as f:
    for line in f:
        line = line.strip()
        if not line:
            continue
        (extra if line.startswith(';') else ballot_lines).append(line)
trustees = json.loads(extra[0][1:])
result = json.loads(extra[1][1:])[0]

ballots = [json.loads(l) for l in ballot_lines]
t_parsed = time.perf_counter()

# ---- election public key from the trustees ----------------------------------
pk0 = trustees[0]['public_key']
pk = EGPublicKey()
pk.p, pk.q, pk.g = int(pk0['p']), int(pk0['q']), int(pk0['g'])
pk.y = 1
for t in trustees:
    pk.y = (pk.y * int(t['public_key']['y'])) % pk.p
pk_consistent = (pk.y == expected_y)

n_candidates = len(ballots[0]['vote']['answers'][0]['choices'])
plaintexts = [EGPlaintext(1, pk), EGPlaintext(pk.g, pk)]

# ---- 1+2: verify each ballot, homomorphically aggregate the valid ones ------
agg = [[1, 1] for _ in range(n_candidates)]  # (alpha, beta) per candidate
n_valid = n_invalid = 0
for b in ballots:
    answer = b['vote']['answers'][0]
    ok = len(answer['choices']) == n_candidates
    cts = []
    if ok:
        for i, ch in enumerate(answer['choices']):
            ct = EGCiphertext(int(ch['alpha']), int(ch['beta']), pk)
            proof = EGZKDisjunctiveProof.from_dict(
                answer['individual_proofs'][i])
            if not ct.verify_disjunctive_encryption_proof(
                    plaintexts, proof, EG_disjunctive_challenge_generator):
                ok = False
                break
            cts.append(ct)
    if ok:
        n_valid += 1
        for i, ct in enumerate(cts):
            agg[i][0] = (agg[i][0] * ct.alpha) % pk.p
            agg[i][1] = (agg[i][1] * ct.beta) % pk.p
    else:
        n_invalid += 1
t_ballots = time.perf_counter()

# ---- 3+4: trustee decryption proofs and proofs of knowledge -----------------
trustee_ok = True
for t in trustees:
    ty = int(t['public_key']['y'])
    tpk = EGPublicKey()
    tpk.p, tpk.q, tpk.g, tpk.y = pk.p, pk.q, pk.g, ty
    pok = t['pok']
    if not tpk.verify_sk_proof(
            DLogProof(int(pok['commitment']), int(pok['challenge']),
                      int(pok['response'])), DLog_challenge_generator):
        trustee_ok = False
    for i in range(n_candidates):
        proof = EGZKProof.fromJSONDict(t['decryption_proofs'][0][i])
        factor = int(t['decryption_factors'][0][i])
        # DH tuple g, alpha, y, dec_factor (as in Tally.verify_decryption_proofs)
        if not proof.verify(pk.g, agg[i][0], ty, factor, pk.p, pk.q,
                            EG_fiatshamir_challenge_generator):
            trustee_ok = False

# ---- 6: plaintext tally consistency ------------------------------------------
tally_ok = True
for i in range(n_candidates):
    prod_factors = 1
    for t in trustees:
        prod_factors = (prod_factors * int(t['decryption_factors'][0][i])) % pk.p
    m = (agg[i][1] * inverse(prod_factors, pk.p)) % pk.p
    if pow(pk.g, int(result[i]), pk.p) != m:
        tally_ok = False
t_end = time.perf_counter()

print(f"file: {data_file}")
print(f"ballots: {len(ballots)} (valid {n_valid}, invalid {n_invalid}), "
      f"candidates: {n_candidates}, trustees: {len(trustees)}")
print(f"pk product consistent: {pk_consistent}, trustee proofs ok: {trustee_ok}, "
      f"tally consistent: {tally_ok}")
print(f"parse:                {t_parsed - t_start:8.2f} s")
print(f"ballot verification:  {t_ballots - t_parsed:8.2f} s")
print(f"trustees + tally:     {t_end - t_ballots:8.2f} s")
print(f"total:                {t_end - t_start:8.2f} s")
