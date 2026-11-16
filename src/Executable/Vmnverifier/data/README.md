Proofs of the Verificatum mix-net (VMN 3.1.0, https://www.verificatum.org),
produced with the `demo/mixnet` scripts of the verificatum-vmn sources in
pure-Java mode: three mix-servers, threshold two, non-interactive proofs
with SHA-256 random oracles, key width 1, ciphertext width 1, no
pre-computation. The group is the one of `Examples/HeliosTallyIns.v`
(2048-bit p, 256-bit q, Pocklington certificates in `Examples/primeP.v` and
`primeQ.v`), passed to the demo as
`vog -gen ModPGroup -explic -roenc <p> <g> <q>`; Verificatum's own
verifier `vmnv` accepted both proofs.

- `demo/`: 10 ciphertexts (`protInfo.xml`, and the proof directory
  `default/` with the input ciphertexts, public key, plaintexts and the
  `proofs/` subdirectory).
- `demo1000/`: 1000 ciphertexts, same configuration.

Verify with `main.exe protInfo.xml default`. `bench/verificatum_tamper.py`
produces proofs with one byte-tree leaf changed and checks that each is
rejected.
