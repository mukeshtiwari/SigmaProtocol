# Running Belenios shuffles on the extracted Rocq verifier

The torsion finding ([FINDINGS.md](FINDINGS.md)) is argued against the
prime-order *model* of this repository's certified verifier. This note closes
the gap by running the actual **extracted** Terelius–Wikström verifier on the
same Belenios shuffle proofs, and shows exactly where the soundness guarantee
lives.

## How

`Crypto/ShuffleTW.v`'s `tw_verify` is parametric over any
`vector_space` and takes its Fiat–Shamir challenges as oracle parameters. The
driver [Executable/Belenioshuffleverifier](/src/Executable/Belenioshuffleverifier/main.ml)
links two already-extracted libraries of this repository — the Ed25519 group
instance from `Belenioslib` and the parametric `ShuffleTW.tw_verify` from
`Verificatumlib` — and calls

```
tw_verify Zl.one Zl.mul Ed.gid Ed.ginv Ed.gop Ed.gpow_fast Ed.coq_Gdec N public transcript
```

so the verdict comes from the extracted certified term itself, at the group
Belenios actually uses. [export_tw.py](export_tw.py) maps a Belenios shuffle
onto that statement (the mapping is in its header: `A'=t3, C'=t1, D'=t2,
B'=tt_hat, F'=(t42,t41)`, response `[s3;s1;s2;s4]++ss_hat++ss2`) and writes the
same proof both as a `.bel` for `belenios-tool` and a `.dat` for this driver.
Build and run via [run.sh](run.sh); results in [results/rocq.tsv](results).

The mapping relies on `ShuffleTW.mk_public` taking the bridging base `h0` and
the commitment generators `hs` independently (Belenios uses
`get_generator(-1)` for `h0` and `get_generator(0..n-1)` for `hs`; the
Verificatum instance happens to reuse `hs[0]`, which is why the dedicated
driver is needed rather than `verify_pos_ins`).

## Result (EXT_SEEDS=50)

| mode | cases | extracted `tw_verify` accepts | output off-subgroup | belenios-tool accepts |
|---|---|---|---|---|
| honest | 3 | 3 | 0 | 3 |
| torsion (order 2) | 50 | 29 | 50 | 12 |
| torsion (order 8) | 50 | 8 | 50 | 2 |

- **Honest.** The extracted `tw_verify` accepts belenios-tool's own shuffles
  (and the port's). The certified verifier and Belenios's prover agree — a
  cross-validation of both implementations of the TW algebra.
- **Torsion.** Every tampered output is off the prime-order subgroup. The
  extracted `tw_verify`, run directly on these points, still accepts a
  parity-dependent fraction — and it agrees with the independent Python port
  case for case, confirming that is the true behaviour of the TW *algebra*,
  not an artefact. belenios-tool accepts a smaller fraction (its libsodium
  arithmetic diverges on off-subgroup points).

## What this shows

In Coq the Ed25519 group type is the order-*l* subgroup, so `tw_verify`'s
soundness theorem only ever speaks about subgroup elements; a torsion point
cannot be formed. Extraction erases that proof, and the driver here feeds the
bare algebra a torsion point on purpose — and it is accepted a fraction of the
time, exactly like Belenios. So the certified verifier's soundness does not
come from the algebra rejecting bad points; it comes from the **driver**
enforcing subgroup membership at the trusted boundary
(`Executable/Beleniosverifier/parsing/ast.ml` checks order *l* on every parsed
point, so it would reject all 100 torsion cases — `output off-subgroup = 50/50`
in both rows). Belenios reaches the same TW algebra through
`check_shuffle_proof`, which never applies that check to its ciphertexts — the
one missing guard.
