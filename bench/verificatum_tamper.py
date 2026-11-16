#!/usr/bin/env python3
"""Tamper tests for the certified Verificatum verifier: copies of a proof
directory with one byte-tree leaf changed, each of which the verifier must
reject. Byte trees: leaf = 01 | bytes4(len) | data, node = 00 | bytes4(n) | children.

usage: bench/verificatum_tamper.py protInfo.xml PROOF_DIRECTORY [VERIFIER]"""
import sys, os, shutil, struct, subprocess, tempfile

protinfo, src = sys.argv[1], sys.argv[2]
verifier = sys.argv[3] if len(sys.argv) > 3 else "_build/default/src/Executable/Vmnverifier/main.exe"

def decode(b, pos=0):
    tag = b[pos]; n = struct.unpack('>I', b[pos+1:pos+5])[0]; pos += 5
    if tag == 1: return ('leaf', bytearray(b[pos:pos+n])), pos + n
    cs = []
    for _ in range(n):
        c, pos = decode(b, pos); cs.append(c)
    return ('node', cs), pos
def encode(t):
    if t[0] == 'leaf': return b'\x01' + struct.pack('>I', len(t[1])) + bytes(t[1])
    return b'\x00' + struct.pack('>I', len(t[1])) + b''.join(encode(c) for c in t[1])
def load(d, name):
    t, _ = decode(open(os.path.join(d, name), 'rb').read()); return t
def save(d, name, t): open(os.path.join(d, name), 'wb').write(encode(t))
def flip(leaf):   # change the last byte of a leaf (keeps the value in range for elements < modulus)
    leaf[1][-1] ^= 0x01

def t_shuffle_response(d):     # k_E,0 of the first server
    t = load(d, 'proofs/PoSReply01.bt'); flip(t[1][4][1][0]); save(d, 'proofs/PoSReply01.bt', t)
def t_shuffle_commitment(d):   # A' of the second server
    t = load(d, 'proofs/PoSCommitment02.bt'); flip(t[1][1]); save(d, 'proofs/PoSCommitment02.bt', t)
def t_output_list(d):          # a ciphertext of L_1: the proof of server 1 no longer matches its output
    t = load(d, 'proofs/Ciphertexts01.bt'); flip(t[1][0][1][0]); save(d, 'proofs/Ciphertexts01.bt', t)
def t_swap_outputs(d):         # two ciphertexts of the final list swapped: a permutation, but not the proved one
    t = load(d, 'proofs/Ciphertexts02.bt')
    for comp in t[1]: comp[1][0], comp[1][1] = comp[1][1], comp[1][0]
    save(d, 'proofs/Ciphertexts02.bt', t)
def t_permutation_commitment(d):
    t = load(d, 'proofs/PermutationCommitment01.bt'); flip(t[1][0]); save(d, 'proofs/PermutationCommitment01.bt', t)
def t_decryption_factor(d):
    t = load(d, 'proofs/DecryptionFactors02.bt'); flip(t[1][0]); save(d, 'proofs/DecryptionFactors02.bt', t)
def t_decryption_reply(d):
    t = load(d, 'proofs/DecrFactReply03.bt'); flip(t); save(d, 'proofs/DecrFactReply03.bt', t)
def t_plaintext(d):
    t = load(d, 'Plaintexts.bt'); flip(t[1][0]); save(d, 'Plaintexts.bt', t)
def t_public_key(d):
    t = load(d, 'FullPublicKey.bt'); flip(t[1][1]); save(d, 'FullPublicKey.bt', t)

tampers = [t_shuffle_response, t_shuffle_commitment, t_output_list, t_swap_outputs, t_permutation_commitment,
           t_decryption_factor, t_decryption_reply, t_plaintext, t_public_key]
allok = True
for t in tampers:
    with tempfile.TemporaryDirectory() as tmp:
        d = os.path.join(tmp, 'default'); shutil.copytree(src, d); t(d)
        r = subprocess.run([verifier, protinfo, d], capture_output=True, text=True)
        rejected = r.returncode != 0
        allok &= rejected
        last = (r.stdout.strip().splitlines() or [''])[-1]
        print('%-26s rejected=%-5s %s' % (t.__name__, rejected, last[:90]))
print('all tampered proofs rejected:', allok)
