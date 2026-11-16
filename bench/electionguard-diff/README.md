# Differential testing: certified ElectionGuard verifier vs the reference

The certified ElectionGuard 2.0 verifier (`src/Executable/Egverifier`,
`Backend/ElectionGuardTally.v`) against the verifier of the ElectionGuard
reference implementation it was written for, on the same election records.

## Reproduce

```sh
bench/electionguard-diff/run.sh WORK_DIR [SEED]          # SEED defaults to 1
bench/electionguard-diff/run.sh WORK_DIR SEED --regen    # new fixture elections (see below)
```

`run.sh` needs git, a JDK 17 (`JAVA_HOME`, default Homebrew's `openjdk@17`;
egk sets `jvmToolchain(17)`), Python 3, and the opam switch `default` of this
repository (dune, zarith, cryptokit, yojson). It

1. clones the reference, **electionguard-kotlin-multiplatform** (egk),
   <https://github.com/JohnLCaron/electionguard-kotlin-multiplatform>, checks
   out commit `194b9c788ccaecda8719c227bd41ce57a3b857be` (v2.0.4-SNAPSHOT,
   2024-02-18, the final commit; the repository is archived) and checks the
   hash; its test records under `egklib/src/commonTest/data/workflow` are the
   records our verifier's `data/` was taken from (byte-identical);
2. builds `egkliball/build/libs/egklib-all.jar` with the Gradle wrapper (Gradle
   8.6, `distributionSha256Sum=9631d53c…f440f24c` added to the wrapper so the
   download is checked) in a Gradle home under `WORK_DIR`; Maven dependencies
   are fetched at the versions of egk's `gradle/libs.versions.toml` (not
   hash-locked). The jar is not bit-reproducible (its SHA-256 differs between
   builds); the source commit, Gradle checksum and JDK are what is pinned;
3. builds the certified verifier with dune;
4. checks the fixtures against `fixtures.sha256`;
5. runs `campaign.py` twice with the same seed and checks that the two verdict
   tables are identical (`results/run1/summary.tsv`, `results/run2/summary.tsv`,
   copied to `results/summary.tsv`); `results/run*/details.tsv` adds each
   verifier's failed checks and times, `results/run*/skipped.tsv` the cases
   whose construction failed in egk's tools, `results/versions.txt` the
   versions and hashes of the run.

Tested with: OpenJDK 17.0.21 (Homebrew), Python 3.15.0, OCaml 5.4.1, macOS
(Apple Silicon), 4 parallel jobs.

## Fixtures

`fixtures/` holds five elections made with egk's command-line programs by
`gen_elections.sh` (manifest, configuration, trusted key ceremony, input
ballots, batch encryption, chosen ballots challenged — state `SPOILED`, egk's
spelling —, tally, trusted tally and challenged-ballot decryption), with the
trustees' and voters' private data that the forgeries need:

| fixture | contests × options | guardians (quorum) | ballots (challenged) | notes |
|---|---|---|---|---|
| small | 2 × 3 | 3 (3) | 6 (1) | |
| quorum | 2 × 3 | 5 (3) | 6 (1) | guardians 2 and 4 missing at decryption |
| multi | 3 × 4 | 3 (3) | 6 (1) | contest 2 allows two votes |
| medium | 4 × 4 | 3 (3) | 15 (2) | |
| chained-batch | 2 × 3 | 3 (3) | 6 (1) | `--chainCodes`; egk's batch encryption does not chain (a protocol case) |

and the campaign also uses egk's three workflow records (`allAvailableJson`,
`someAvailableJson`, `chainedJson`, 20 × 5, 11 ballots). egk draws its
randomness from `SecureRandom`, so elections cannot be regenerated bit for
bit: the fixtures are saved, and every random choice of `campaign.py` comes
from the seed. The forgeries re-run egk's tools (decryption, encryption), whose
proofs differ between runs; the verdicts do not.

## The campaign (`campaign.py`)

Each case is a published record (without the private data) verified by egk's
`RunVerifier` and by the certified verifier. An egk exception (no `allOK`
line) and a parse failure of the certified driver count as rejections.

1. **honest**: the 4 fixtures and egk's 3 records.
2. **field**: on `small`, `quorum`, `multi`, one random occurrence of every
   field of every file, mutated by type (elements of Z_p^r: times g, 1,
   inverse, random, swapped with a sibling; elements of Z_q: +1, 0, negated,
   random; hashes and byte strings: last digit changed, zero; integers: +1, 0;
   strings; booleans). Fields that no verification step reads are expected
   "either".
3. **structure** (on `small`): encodings (lower case, leading zeros), values
   outside Z_p^r or Z_q, lists one element short or long, a missing, extra or
   mistyped field, ballot states (`SPOILED`, `UNKNOWN`, `CHALLENGED`, `cast`),
   a duplicated ballot, a ballot of another election.
4. **forgery / protocol**, each with a control built the same way:
   - ballots of our prover (`eglib.py`: the hash H, encryption, the range proof
     of egk's `makeChaumPedersenWithNonces`; checked at start-up against egk's
     own proofs, contest hashes and confirmation codes) with Fiat–Shamir-
     consistent cheating proofs (the honest algorithm run on a wrong witness):
     an option encrypting 2, a vote transfer (−1 and +1, only one range proof
     cheating), two votes in a one-vote contest (only the selection-limit proof
     cheating); each is cast, the encrypted tally recomputed and validly
     decrypted by the trustees with egk;
   - tallies validly decrypted by the trustees that are not the product of the
     cast ballots (times Enc(1), a challenged ballot counted, a cast ballot left
     out), a cast ballot deleted, a cast ballot's decryption published as a
     challenged one, a challenged ballot's decryption replaced by that of
     another ciphertext;
   - the base hashes H_E, H_B, H_M, H_P replaced by a random value that egk's
     own pipeline (encryption, tally, decryption) then uses consistently;
   - on egk's chained record: ballots removed from, swapped in or left out of
     the confirmation chain, the closing hash changed, the chain file removed;
     and the chained-batch fixture.

Our certified prover does not exist for ElectionGuard (the certified code is
the verifier); the ballots of source 4 come from `eglib.py`, which is checked
against egk's proofs, not certified.

## Results (seed 1; `run.sh` twice: identical verdict tables, 31 min for both on 4 jobs)

779 cases: 7 honest, 675 field, 42 structure, 48 forgery, 7 protocol; 2
constructions skipped (egk's ballot decryption fails on its own `chainedJson`
record: `NegativeArraySizeException` decoding the contest data).

| source | egk | certified | cases |
|---|---|---|---|
| honest | accept | accept | 7 |
| field | accept | accept | 116 |
| field | reject (or abort) | reject (or parse failure) | 538 |
| field | accept | reject (or parse failure) | 18 |
| field | abort | accept | 3 |
| structure | accept | accept | 8 |
| structure | reject (or abort) | reject (or parse failure) | 31 |
| structure | accept | reject (or parse failure) | 3 |
| forgery/protocol | accept | accept | 22 (the controls) |
| forgery/protocol | reject (or abort) | reject | 28 |
| forgery/protocol | accept | reject | 5 |

All 29 disagreements go one way: egk accepts, or aborts on a field no
verification reads, and the certified verifier rejects. Every control is
accepted by both; every ballot with cheating proofs, every tally that is not
the product of the cast ballots and every base-hash forgery is rejected by
both, each verifier naming the targeted check (egk: 5–6 or 8; certified: the
invalid ballot, the tally, 1.F–4.A). egk accepts:

- a challenged ballot whose published decryption is a valid decryption of
  another ciphertext with other choices (`VerifyDecryption.verify` checks the
  proofs against the ciphertexts written in the decryption file and never
  looks up the challenged ballot): a device that encrypts a wrong choice
  would pass the voter's challenge (cases *forgery small/quorum tally: a
  challenged ballot's published decryption is that of another ciphertext*);
- a cast ballot's decryption published as a challenged ballot (no check that
  a decrypted ballot is a challenged one);
- with chained codes, a published ballot left out of `ballot_chain.json` and
  the tally (egk reads the device's ballots through the chain's list only);
- a decrypted tally missing a contest, an encrypted tally missing an option
  or with a renamed one, an encrypted tally naming another election, ballots
  whose contest or option labels are not the manifest's, a challenged
  decryption whose id names no ballot;

and egk's `RunVerifier` aborts (uncaught exception, no verdict) on an
inconsistent manifest hash and on an unknown contest-data status.

Found on the certified side and fixed (`src/Executable/Egverifier/main.ml`):
the confirmation chain (verification 7: links, closing hash, and the chain
must list exactly the device's published ballots) was not checked; the
challenged ballots' contest-data decryptions (verification 14; egk hashes C1
as the text of its hex encoding, which the driver follows) and election id
were not checked; pre-encrypted ballots were not refused. Before the fixes,
egk rejected and the certified verifier accepted 5 chain cases and 69 field
mutants (23 per fixture: the challenged ballots' contest data and election id,
and the pre-encryption flag).
