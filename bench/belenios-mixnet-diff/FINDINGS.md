# Finding: the Belenios shuffle verifier does not subgroup-check its ciphertexts

## Summary

`check_shuffle_proof` in Belenios 3.2.0's
[mixnet.ml](../belenios-diff/_work/belenios/src/lib/v1/mixnet.ml) applies the
subgroup test `G.check` to the proof commitments it reads, but never to the
ciphertext arguments `ee` (the input) or `ee'` (the shuffled output). On
Ed25519, whose full curve has cofactor 8, a mix server can therefore output a
ciphertext that is **not in the prime-order subgroup** — an honest
re-encryption plus a low-order (torsion) point — and still produce a shuffle
proof that `belenios-tool election verify` accepts, with a probability that
depends on a Fiat–Shamir challenge (26/100 seeds for a point of order 2,
2/100 for order 8 in the campaign; see [results/torsion.tsv](results)).

This is a verifier-soundness gap relative to this repository's certified
mix-net verifier, which is defined and proved over a prime-order group where
no such point exists.

## Where

```ocaml
(* mixnet.ml, check_shuffle_proof *)
Array.for_all G.check [| t1; t2; t3; t41; t42 |]
&& ...
&& Array.for_all G.check cc
&& Array.for_all G.check cc_hat
&& Array.for_all G.check tt_hat
&& ...
```

`G.check` ([ed25519_pure.ml](../belenios-diff/_work/belenios/src/lib/core/ed25519_pure.ml))
is a full subgroup test: on the curve, canonical, and `l·P = 0`. It is
applied to the proof commitments (`t1..t42`, `cc`, `cc_hat`, `tt_hat`) but to
none of the ciphertexts `ee`, `ee'`. Belenios subgroup-checks ciphertexts
everywhere else:

- ballots — `question_nh.ml:76`, `G.check alpha && G.check beta`;
- the encrypted tally and the decryption factors — `election.ml:302, 315`,
  through `check_ciphertext`.

The shuffle verifier is the single place a group element reaches a check and
is not tested for subgroup membership.

## Why a torsion point passes with ~constant probability

The only verification equations that mention the output `ee'` are those for
`t41` and `t42`, where the outputs appear raised to the response coordinates
`ss'`:

```
t41' = (∏ ee'_i.beta ^ ss'_i) · (beta'^c · y^{s4})^{-1}
t42' = (∏ ee'_i.alpha ^ ss'_i) · (alpha'^c · g^{s4})^{-1}
```

Let `ee'_0.beta = honest_beta · T` with `T` of order 2. The honest part
cancels against the prover's `t41` as usual; the torsion part contributes
`T^{ss'_0 − ω'_0} = T^{c·u'_0}`, which is the identity exactly when `c·u'_0`
is even. The challenge `c` and the batching exponent `u'_0` are derived from
hashes, so this parity is satisfied for a fraction of seeds — not all, not
none — which is the signature of a low-order-point malleability and matches
the observed 26 % (order 2) and 2 % (order 8).

Two consequences, measured by the extended campaign ([campaign_ext.py](campaign_ext.py)):

- **The torsion survives an honest chain.** An honest re-encryption is
  `(α·g^r, β·pk^r)`; `g^r` and `pk^r` are subgroup elements, so they do not
  cancel a torsion component. A point injected by one mixer therefore reaches
  the end of the chain still outside the subgroup (250/250 cases). The chain's
  shuffle check is nonetheless accepted for a fraction that falls the earlier
  the taint is injected, because every shuffle downstream of the taint must
  also pass with a torsion-carrying input — so a malicious **last** mixer has
  the best odds.
- **Order 2 does not get harder with more tainted outputs.** Tainting *j*
  outputs with the same order-2 point contributes `T^{Σ c·u'_i}`, whose parity
  is a single bit of the challenge regardless of *j*; the acceptance rate is
  flat in *j* (≈12/50 for j = 1, 2, 3). An order-8 point imposes a mod-8
  condition that compounds and vanishes quickly.

The independent Python port in [mix_lib.py](mix_lib.py) accepts a larger
fraction than `belenios-tool`, because the real tool's arithmetic (libsodium
`crypto_scalarmult_ed25519_noclamp` refuses a non-subgroup base and Belenios
falls back to its pure implementation, which exponentiates by the scalar
reduced mod *l*) imposes extra constraints on when the torsion cancels. The
port is faithful on honest, subgroup inputs — it accepts both of the
fixture's genuine shuffles — and the finding is reported from the real tool,
not the port.

## The certified side

This has been checked on the extracted code, not only argued from the model:
the extracted `tw_verify` at Ed25519 (driver
[Executable/Belenioshuffleverifier](/src/Executable/Belenioshuffleverifier/main.ml))
accepts belenios-tool's honest shuffles, and when fed the torsion cases with
the subgroup proof erased it accepts the same parity-dependent fraction as
Belenios — so the certified verifier's protection is the driver's parse-time
order-*l* check, which rejects all of them, not the algebra. See
[ROCQ.md](ROCQ.md).

This repository's certified mix-net verifier
([VerificatumVerifier.v](/src/Backend/VerificatumVerifier.v) over
[ShuffleTW.v](/src/Crypto/ShuffleTW.v)) implements the same Terelius–Wikström
proof, but over an abstract group that is a `vector_space` over a field — a
group of prime order. In that model a torsion point does not exist, and the
soundness theorems (`verify_pos_accepting`, `verify_shuffling_spec`) hold
under the standing assumption that every ciphertext is a subgroup element.
The verifier's drivers enforce exactly that assumption at the trusted
boundary: the Verificatum driver parses byte-tree points into the group, and
the Belenios driver's parser
([ast.ml](/src/Executable/Beleniosverifier/parsing/ast.ml)) rejects any point
that is not canonical and of order *l*. So the certified pipeline rejects
every output that this campaign feeds past Belenios's shuffle check.

## Scope and impact

- It is a soundness bug in `election verify`'s **shuffle check**: an auditor
  can be shown "all checks passed" for an archive whose shuffle output is
  malformed. The shuffle verdict (proof of correct mixing, and the basis for
  blaming a misbehaving mix server) is a security-relevant output on its own.
- It does not, by itself, give a result forgery through `belenios-tool`'s own
  decryptor: `compute_factor`/`check_result` call `check_ciphertext` on the
  final tally, so a torsion point surviving to the **last** shuffle output is
  caught at decryption (`Invalid ciphertext`), and honest re-encryption by a
  later mixer preserves a torsion component rather than removing it. The
  `decrypt` control confirms this: adding a torsion point to a published
  decryption factor or to an encrypted-tally ciphertext is rejected, because
  the decryption path subgroup-checks both (`check_factor`'s `G.check f`,
  `check_result`'s `check_ciphertext`). The shuffle check is the only place
  the test is missing.
- The clean fix is to `G.check` the shuffle's input and output ciphertexts in
  `check_shuffle_proof`, matching Belenios's own treatment of ballots and the
  tally.

Observed on Belenios 3.2.0 (commit `50a79aed0d34d77a406958dd5a8cb77fe2f32b30`),
the version pinned by `bench/belenios-diff`.
