# Swiss Post Verifier on the synthetic election Post_E2E_DEV

The Swiss Post Verifier is the software the cantonal auditors run on an
election. Here it runs headlessly on the synthetic election `Post_E2E_DEV` of
the testdata repository, and on re-signed, protocol-level tampered copies of
it.

## Versions

| repository | version |
|---|---|
| verifier (gitlab.com/swisspost-evoting/verifier/verifier) | 1.7.1.0 (master, 8474a916) |
| testdata (gitlab.com/swisspost-evoting/e-voting/testdata) | 1.6.1.0 (78d7772) |
| e-voting-libraries | 1.6.1.0 (e4f0dace) |
| crypto-primitives | 1.6.1.0 (94a8438, the submodule `bench/crypto-primitives`) |

Verifier 1.7.1.0 depends on crypto-primitives and e-voting-libraries 1.6.1.0,
the versions the testdata 1.6.1.0 was made with.

## Build

None of the Swiss Post artifacts is on Maven Central, so all of them are built
from source and installed in the local Maven repository, with a JDK 25 and
`-DskipHashGeneration` (the profile that needs the in-house
`hash-generator-maven-plugin`):

```sh
export JAVA_HOME=/opt/homebrew/opt/openjdk@25/libexec/openjdk.jdk/Contents/Home
F="-DskipTests -DskipHashGeneration -Denforcer.skip=true -Djacoco.skip=true -Dmaven.javadoc.skip=true"
(cd crypto-primitives && mvn -q install $F)                   # a copy of bench/crypto-primitives
(cd testdata && mvn -q install -DskipHashGeneration)          # the testdata zip, needed by e-voting-libraries
(cd e-voting-libraries && git checkout e-voting-libraries-1.6.1.0 && mvn -q install $F -pl '!e-voting-libraries-ui')
(cd verifier && mvn -q package $F -pl verifier-backend -am \
   && cd verifier-backend && mvn -q dependency:build-classpath -Dmdep.outputFile=cp.txt -DskipHashGeneration)
```

The Electron front end is not needed.

## Running the Verifier

```sh
bench/swisspost-e2e/verifier/run_verifier.sh VERIFIER TESTDATA DATASET [setup|tally|all]
```

[VerifierCli.java](VerifierCli.java) starts the Verifier's Spring context and
calls `verify(Path)` on every verification bean, in the order of their ids, as
`AbstractVerification.executeVerify` does; the encrypted-zip upload of the GUI
is bypassed. `DATASET` holds `D2/context` (setup) and `D3/{context,tally}`
(tally), as in the Verifier's own tests:

```sh
TD=testdata/election-events/Post_E2E_DEV
mkdir -p DATASET/D2 DATASET/D3
cp -r $TD/D2/secure-data-manager-setup/context DATASET/D2/
cp -r $TD/D2/secure-data-manager-setup/context DATASET/D3/
cp -r $TD/D3/secure-data-manager-tally/tally   DATASET/D3/
```

On the untampered election all 43 verifications (24 setup, 19 tally) are OK,
in 34 s.

## Re-signing

Every payload is signed by the component that produced it, so a tampered
payload with its old signature only tests the signature check. The dev keys
and passwords of all components are in `testdata/direct-trust/`.
[Tamper.java](Tamper.java) `resign` reads a payload with the e-voting-libraries
domain classes (`DomainJsonMapper`) and signs it as the component does:
`SignatureKeystore.generateSignature(payload, ChannelSecurityContextData.…)`
with the component's key (control component j for its ballot box and shuffle
payloads, `sdm_tally` for the tally component's payloads); the eCH-0222 file
gets a new enveloped XML signature (`XMLSignatureService.genXMLSignature`,
inside `eCH-0222:rawDataDelivery/eCH-0222:extension`, as
`TallyComponentEch0222FileRepository` places it). Validation: the ten payloads
of a ballot box and the eCH-0222 file re-signed unchanged are accepted, and a
changed payload left with its old signature is rejected by the signature check.

## Tampering

```sh
bench/swisspost-e2e/verifier/tamper.py TESTDATA VERIFIER DATASET OUT_DIR [SCENARIO ...]
```

[tamper.py](tamper.py) copies the dataset for each scenario, edits it,
re-signs what it changed, runs the tally verifications and writes
`OUT_DIR/manifest.json` (`name, description, changed_files, expected,
verifier_verdict, verifier_failed_steps`). Results: see below.

### Results (29 scenarios, every verdict as expected)

| scenario | Verifier | first failing verification |
|---|---|---|
| control: 10 payloads + eCH-0222 re-signed unchanged | accept | – |
| control: eCH-0222 re-signed unchanged | accept | – |
| control: decoded vote changed, old signature kept | reject | 07.04 signature |
| two ballot box directories exchanged | reject | 08.05 ballot box ids |
| two ballot boxes exchanged, ids rewritten, re-signed | reject | 08.07 verification card ids |
| shuffle payloads of CC 2 and CC 3 exchanged, re-signed with swapped keys | reject | 10.01 online control components |
| CC 2's shuffle payload taken from another ballot box | reject | 08.11 number of confirmed votes |
| CC 1's shuffle payload relabelled to another election | reject | 08.04 election event ids |
| a confirmed vote dropped from all four CC ballot box payloads | reject | 08.11 number of confirmed votes |
| a confirmed vote dropped from CC 2's ballot box payload only | reject | 08.08 confirmed votes consistency |
| a confirmed vote duplicated in all four | reject | the domain classes refuse the payload (duplicate verification card id); the Verifier fails reading it |
| a confirmed vote of another ballot box added to all four | reject | the same (mixed verification card sets) |
| confirmed votes reordered in all four | **accept, correct**: Algorithm 6.1 orders them by verification card id | – |
| votes payload: a decoded vote replaced | reject | 10.02 tally control component |
| votes payload: a whole vote replaced consistently (primes, options, write-ins) | reject | 10.02 |
| votes payload: a vote dropped | reject | 08.11 |
| votes payload: votes reordered | reject | 10.02 |
| votes payload: a write-in changed / added | reject | 10.02 |
| tally shuffle payload: two decrypted votes exchanged (alone / with the votes payload) | reject | 10.02 |
| CC 2's shuffle argument: response r + 1 | reject | 10.01 |
| CC 3's decryption proof: z₀ + 1 | reject | 10.01 |
| tally mix-decryption redone: valid shuffle, decryption under a fresh key with valid proofs for it | reject | 10.02 (an exception, see below) |
| CC 3's shuffle payload deleted | reject | 06.01 completeness |
| eCH-0222: an answer changed / a ballot dropped / a ballot duplicated / the invalid voting cards count changed (re-signed) | reject | 10.02 |

Observations, none of them an acceptance of a tampered election:

- When the tally component's proofs fail, `VerifyTallyControlComponentBallotBoxAlgorithm` still runs `VerifyProcessPlaintexts` on the unverified plaintexts; plaintexts that are not products of the encoding primes make it throw ("The actual number of prime factors does not match …"), so the step reports UNEXPECTED_ERROR instead of the failed decryption proofs. The verdict is still a failure; the auditor's message hides the cause.
- Payloads that the domain classes refuse (duplicated or foreign confirmed votes) make every verification that reads them report UNEXPECTED_ERROR instead of a NOK of the relevant consistency check.
- The dataset's `tally/manifest.json` names election `A7837373830511AA2DB9C7D27B9BE278`, the payloads `E1AD18B1386A1508DEDE13345468ED56`; the Verifier does not read the manifest.

Not done: attacks that need a valid proof for a tampered statement (a control component shuffling or decrypting something other than its predecessor's output, a wrong key share with a valid proof for the setup key) need the control components' secret key shares, which are not in the dataset, or the electoral board's passwords, which the dataset does not publish: the key derived from `Password_EB1_Password_EB1` / `Password_EB2_Password_EB2` (Run_Election_Event.md) and from the passwords of the SDM tests does not match the setup's electoral board key (`Tamper.java ebkey`, which hashes as `MixDecOfflineAlgorithm` does). With the passwords, `Tamper.java remix` forges the tally component's mix-decryption with valid proofs (variants honest, stale-votes, wrong-input, wrong-key, drop-one).
