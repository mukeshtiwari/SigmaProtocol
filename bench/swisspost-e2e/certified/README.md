# Certified checking of a Swiss Post election's tally

Checks every proof of the tally phase of a Swiss Post election event with
the certified verifiers of this repository, wired as the Swiss Post
specifications prescribe, and compares with Swiss Post's own Verifier
(`../verifier/`) on tampered copies of the election.

The election is the synthetic event `Post_E2E_DEV` of the Swiss Post
[testdata](https://gitlab.com/swisspost-evoting/e-voting/testdata)
repository (release 1.6.1.0): 4 ballot boxes, each mixed and partially
decrypted by the 4 online control components and then mixed and decrypted
by the tally control component (electoral board).

```sh
git clone --depth 1 https://gitlab.com/swisspost-evoting/e-voting/testdata.git
E=testdata/election-events/Post_E2E_DEV
python3 bench/swisspost-e2e/certified/mkins.py $(ls $E/D3/secure-data-manager-tally/tally/ballotBoxes/*/controlComponentShufflePayload_1.json | head -1)
dune build src/Executable/Swissposte2e/main.exe
python3 bench/swisspost-e2e/certified/e2e_extract.py $E statements.json
_build/default/src/Executable/Swissposte2e/main.exe statements.json      # exit 0 iff everything verifies
python3 bench/swisspost-e2e/certified/run_tampers.py $E TAMPER_ROOT     # against ../verifier's tampered copies
```

The pieces:

- `mkins.py` generates [BayerGrothE2EIns.v](/src/Examples/BayerGrothE2EIns.v)
  and [SwissPostZkpE2EIns.v](/src/Examples/SwissPostZkpE2EIns.v): the
  instances of `BayerGrothIns.v` and `SwissPostZkpIns.v` at the election's
  3072-bit group (p = 2q + 1, g = 2). **The primality of q is assumed** (the
  axiom `prime_q`); p is proved prime from it by Pocklington's criterion and
  the order of g is computed, as in `BayerGrothIns.v`. Both are extracted to
  `SwissPostE2Elib`.
- `e2e_extract.py` is the protocol wiring (trusted): for each ballot box it
  emits the 5 shuffle statements and the decryption statements with the
  inputs, keys and auxiliary information of Verifier Specification 1.7.1
  (Algorithms 4.1, 4.2) and System Specification 1.6.1 (6.1, 6.10):

  | step | shuffle | key | decryption key, i_aux |
  |---|---|---|---|
  | CC j = 1..4 | C_init (j = 1) or c_dec,j−1 → c_mix,j | CombinePublicKeys(EL_pk,j…4, EB_pk) (EL_pk for j = 1) | EL_pk,j, (ee, bb, "MixDecOnline", "j") |
  | tally | c_dec,4 → c_mix,5 | EB_pk cut to δ | EB_pk cut, (ee, bb, "MixDecOffline") |

  C_init is CC 1's confirmed votes ordered by verification card ID, padded
  with two trivial encryptions GetCiphertext(1, 1, EL_pk) below two votes;
  the shuffles use the computation-optimized dimensions (m = 1, n = N) and
  the commitment key GetVerifiableCommitmentKey(N) (Algorithm 9.6, with
  SHAKE-256, checked against the Swiss Post test vectors at start-up). It
  also records the checks that involve no proof: EL_pk = CombinePublicKeys
  of the control components' and electoral board's keys, the four control
  components' agreement on the confirmed votes, distinct verification card
  IDs, the payloads' election event, ballot box, node and group, γ′ = γ of
  every partial decryption (Algorithm 8.13), and that the decrypted
  plaintexts other than the trivial 1s are, as a multiset, the products of
  the listed decrypted votes. The payloads encode integers with
  IntegerToByteArray (unsigned), not with the two's complement of the
  crypto-primitives test vectors.
- [Swissposte2e/main.ml](/src/Executable/Swissposte2e/main.ml) checks the
  input boundary (subgroup membership, exponent range), computes the
  RecursiveHash challenges and runs the certified shuffle and decryption
  verifiers on every statement.

Not covered: the voting-client proofs of Algorithm 4.1
(VerifyVotingClientProofs: exponentiation and plaintext-equality proofs of
each confirmed vote), the setup-phase verifications, the decoding of the
plaintexts into voting options and write-ins (VerifyProcessPlaintexts beyond
the products) and the eCH-0222 result file; payload signatures are not
checked (Swiss Post's Verifier checks them).

## Results

On the untampered `Post_E2E_DEV` (4 ballot boxes of 0, 1, 3 and 4
confirmed votes; the first two are padded with two trivial encryptions):
20 shuffles, 60 decryption proofs and 57 protocol checks, all verified, in
12 s.

Against the 29 re-signed tampered copies of `../verifier/` (`run_tampers.py`,
30 s): the certified checker agrees with the Swiss Post Verifier on every
scenario within its scope (21 of 29), accepting the three controls and the
reordered confirmed votes (a no-op: Algorithm 6.1 orders them) and rejecting
every swapped, relabelled, missing, dropped, duplicated or foreign payload or
vote, every changed proof, the tally re-mixed and decrypted under a fresh
key, and the decrypted votes swapped, replaced, dropped or reordered. The
other 8 are accepted by the certified checker and rejected by the Verifier,
all outside its scope: a stale signature, the decoded votes and write-ins
(3), and the eCH-0222 result file (4).
