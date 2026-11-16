# Differential testing of Helios

Compares the verdicts of Helios's own verification code and of the
certified Helios verifier on honest, mutated, malformed and tampered
elections, component by component (each ballot, the key product, the
trustees' decryption proofs and proofs of knowledge, the published tally).

```sh
bench/helios-diff/run.sh --twice            # SEED=1; WORK_DIR defaults to bench/helios-diff/work
```

writes `results/verdicts.tsv` (one line per case) and `results/summary.tsv`,
and with `--twice` reruns everything from scratch and checks that the two
verdict tables are byte-identical. `--no-iacr` skips the two IACR elections
(the slow part: about 4 min each in Helios's Python); `--regen-booth`
regenerates the booth fixtures (needs Node).

## The two sides

- **Helios** (deployed): `bench/helios-server` pinned at
  `88621e3196961ec03fe54bbd3a1c2196e715e9a2` (checked by `run.sh`). The
  oracle (`oracle_helios.py`) imports `helios/crypto/algs.py`, `utils.py`
  and `electionalgs.py` unmodified (through a stub package, since
  `helios/__init__.py` needs Django) and runs Helios's own path:
  `EncryptedVote.verify` per ballot (number of answers, election hash and
  UUID, group membership, the disjunctive 0/1 proofs), `Tally.add_vote`,
  `Tally.verify_decryption_proofs`, `EGPublicKey.verify_sk_proof`, the key
  product, and `Tally.decrypt_from_factors` against the published result.
  The election object (group, key, one approval question with n answers,
  hash, UUID) is the case's spec. Ballots also come from the Helios booth
  JavaScript (`gen_booth.js`, `heliosbooth/js` of the same commit).
- **Certified**: `src/Executable/HeliosVerifiercode/diff.exe`
  (`compute_final_count_ins` of `HeliosTallyIns.v`, the IACR verifier's
  parser) and `prove.exe` (the certified ballot prover of
  `HeliosFrontendIns.v`, with Helios's SHA-1 challenges per candidate).

## Cases (SEED = 1)

Five generated elections at the IACR group (n = 1, 2, 3, 5, 7 candidates;
2 or 3 trustees; 4 or 6 ballots, half from the booth, half from the
certified prover; E4 has all-0 and all-1 ballots), plus IACR 2023 and 2024
as published. The trustees' keys, proofs of knowledge, decryption factors
and proofs are made by Helios's own code with its random source seeded.

| source | cases | what |
|---|---|---|
| honest | 7 | the 5 generated elections, IACR 2023, IACR 2024 |
| field | 509 | one random occurrence of every field, by type: group elements ×g, 1, inverse, random, swapped with a sibling; exponents +1, 0, negated, random; the tally +1, −1, swapped; metadata strings and the trustees' declared group changed |
| structural | 165 | lists one short or long (choices, proofs, branches, answers, factors, tally), extra/missing fields, key order, the overall proof, 8 encodings of one integer, values outside G_q or Z_q |
| tally | 53 | ballots dropped or duplicated (also all-0 ones), a wrong tally, a trustee's decryption replaced by another's, trustees reordered, removed or replaced by a fresh trustee with valid proofs, a wrong election key, a ballot under another key |

## Results (`results/summary.tsv`)

| source | cases | both accept | both reject | Helios accepts, certified rejects | Helios rejects, certified accepts |
|---|---|---|---|---|---|
| honest | 7 | 7 | 0 | 0 | 0 |
| field | 509 | 45 | 459 | 5 | 0 |
| structural | 165 | 5 | 95 | 65 | 0 |
| tally | 53 | 10 | 43 | 0 | 0 |
| total | 734 | 67 | 597 | 70 | 0 |

Every honest election is accepted by both, including the booth's ballots by
the certified verifier and the certified prover's ballots by Helios. The 70
disagreements are all inputs Helios accepts and the certified verifier
rejects:

- 15 where Helios is lenient (3 kinds × 5 elections): an extra individual
  proof (n choices, n + 1 proofs) is ignored by `EncryptedAnswer.verify`; an
  extra decryption factor is ignored by `Tally.verify_decryption_proofs` and
  `decrypt_from_factors`; a proof response r + q verifies as r (responses
  are not range-checked). Each leaves the votes and the tally unchanged:
  several byte strings for the same ballot or trustee record verify.
- 55 differences by design: the certified parser reads exactly the
  canonical JSON Helios writes and rejects the whole election otherwise
  (an extra or missing field, another key order, a non-null overall proof
  of an approval question, integers with whitespace, `+`, `_` or non-ASCII
  digits, which Python's `int()` accepts), and checks the trustees'
  declared generator, which Helios does not use.

Found in the certified side's trusted boundary and fixed (outside the
certified code): the parser discarded the recorded challenges of
decryption proofs and proofs of knowledge (a changed challenge was
accepted; it must now equal SHA-1 of the commitment, as Helios checks); the
certified verifier does not read a ballot's election hash and UUID, which
the diff driver now checks against the election (the IACR driver `main.ml`
has no election object and still does not); `big_int_of_string` accepted
`0x` and other prefixes (now decimal digits only); the first `diff.ml`
passed the number of trustees where `compute_final_count_ins` expects one
less (the talliers are a vector of length 1 + m).

## Versions

macOS 27.0.1 (arm64); Python 3.13.16 with pycryptodome 4.1.0 (created by
`run.sh` with uv 0.13.1); Node v26.12.0 (booth fixtures only); OCaml 5.4.1,
Rocq 9.2.0, dune 3.23.1, zarith 1.14, yojson 3.0.0, menhir 20260209,
cryptokit 1.21.1 (opam switch `default`). A run takes about 8.5 min (513 s,
3 Python workers and one certified process), of which the IACR elections
take most.
