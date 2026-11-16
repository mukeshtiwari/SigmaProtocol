# IVXV (Estonia) — feasibility of certified differential testing

Time-boxed check (about one hour), 2026-10-21. Verdict: **go**, with a scope
limited to IVXV's own verifiers (shuffle, decryption) and the Go core proofs,
on executions we generate ourselves.

## Licence

`LICENSE`: © Estonian State Electoral Office (Vabariigi Valimisteenistus),
created by Cybernetica AS; **Creative Commons BY-NC-ND 3.0 Unported**.
Reading: building, running and testing for non-commercial academic research
is permitted; redistributing the code, modified or not, requires attribution
and must be non-commercial, and **no derivative works may be distributed**.
Consequences for the harness:

- never vendor or copy IVXV sources into this repository, and never patch
  them; fetch a pinned commit at run time;
- our drivers are separate source files compiled *alongside* the unmodified
  build (the probe below sits in IVXV's package name because the
  components' constructors are package-private, as for the Swiss Post
  harness, but no IVXV file is changed or copied);
- publishing verdicts, findings and our own harness is not distribution of
  IVXV. Confirm this reading with the institution (or with the Electoral
  Office at disclosure time).

## Version

`https://github.com/valimised/ivxv`, branch `published`, commit
`2785872f84dffb56bbecc41b096a7ee0f2876e64` ("KOV2025"); 20 MB (8.7 MB of
history). Java apps version 1.10.3.

## Build

```sh
git clone --branch published https://github.com/valimised/ivxv.git   # then checkout 2785872f
brew install openjdk@21                                              # sourceCompatibility = 21; Gradle 8.11 cannot run on JDK 25/27
curl -LO https://services.gradle.org/distributions/gradle-8.11-bin.zip   # sha256 checked against gradle-8.11-bin.zip.sha256
JAVA_HOME=$(brew --prefix openjdk@21)/libexec/openjdk.jdk/Contents/Home \
  gradle-8.11/bin/gradle -g CACHE --max-workers=4 installDist -x test   # in auditor/ and key/
```

- `make external` is now only `git submodule update --init` for a public
  documentation submodule (`e-gov/VIS3-EHS`); there is no Git LFS bundle any
  more. The Java dependencies resolve from Maven Central (online Gradle run,
  i.e. without the Makefile's `--offline`).
- `auditor` and `key` build with no change (warnings only). `processor` and
  `common/java` build as dependencies of these. Tests not run.
- Go core (`core/`, module `tivi.io/core`, Go ≥ 1.23): not built (Go not
  installed; not attempted within the time box).

## Crypto surface

(a) **Shuffle verifier** — `auditor/src/main/java/ee/ivxv/audit/shuffle/`
(`Verifier`, `ThreadedVerifier`, `RO`, `PRNG`, `ByteTree`, `DataParser`,
`ProtocolInformation`, `ShuffleProof`): an independent Java re-implementation
of the Verificatum Terelius–Wikström proof-of-shuffle verifier (references to
verificatum-vmn commit `9d9c45e` / vcr `97974cf`). It checks the five
equations A, B, C, D, F of the PoS for **one mix server only**
(`PermutationCommitment01`, `PoSCommitment01`, `PoSReply01`), not the
decryption; it reads `Ciphertexts.bt`, `ShuffledCiphertexts.bt`,
`FullPublicKey.bt`. Groups: `ModPGroup` (**safe primes only**: the order is
taken as (p−1)/2, the q of Verificatum's group description is ignored) and
`ECqPGroup` (P-384 in `common/java/.../math/ECGroup.java`). The XML reader
requires `keywidth = 5` and `corr = noninteractive`; the ciphertext group is
(G^keywidth)². Keywidth is not part of the Fiat–Shamir prefix ρ.

(b) **Decryption proofs** — `common/java/.../crypto/elgamal/ElGamalDecryptionProof.java`,
checked in the auditor (`audit/util/InvalidDecProofs`) and produced by the key
application: Chaum–Pedersen in announcement form (a, b, s):
c₁^s = a·(c₂/d)^k and g^s = b·y^k; challenge k = rejection-sampled from a
deterministic PRNG (`DPRNG`) seeded with the ASN.1 sequence
("DECRYPTION", public key with parameters and election identifier,
ciphertext, plaintext, a, b), into [0, order). Groups: safe-prime mod-p and
P-384.

(c) **Go core NIZK** — `core/crypto/elgamal/nizkp/{nizkp.go, key/, ciphertext/}`,
`core/crypto/elgamal/elgamal.go`, `core/crypto/elgamal/distributed/distributed.go`.
Two challenge derivations:
- `ProofChallenge` (used by the distributed decryption-share proofs,
  `distributed.go:1148`): SHA-3/SHAKE over ("DECRYPTION", public key,
  ciphertext, decryption, message commitment, key commitment, salt) — each
  value separately; Chaum–Pedersen in compact form (e, s).
- the generic `ProofProve`/`ProofVerify` with `nizkp.Challenge`: SHAKE-256
  over ("NIZKP", the **group product** of all reconstructed commitments and
  statement elements, salt). In this tree it has no production caller
  outside its own package and interface (`core/crypto/crypto.go`).
Groups: `ModPElement`, `NistElement`, `Edwards25519Element` (the ASN.1
`GROUP ELEMENT` choice in `proof.go`).

(d) **Mapping to certified verifiers**:
- (a) → `Vmnverifier` (Terelius–Wikström, `VerificatumVerifier.v`), which is
  instantiated at a fixed group: a new instance is needed at a safe-prime
  group IVXV accepts (primality assumed, as `BayerGrothE2EIns.v`) and with
  keywidth 5 (our verifier must support product-group keys of width 5).
  P-384 would need a new curve instance (only P-256 exists in `src/Curve`).
- (b), (c) → the certified Chaum–Pedersen verifier (announcement form) and
  the Maurer `verify_rows` verifier (compact form), with the challenge
  closures in the trusted driver (ASN.1 + DPRNG for (b), SHAKE for (c)).

## Data

No published election data: `Documentation/common/examples/` holds only RPC
JSON samples; `testdata/` directories hold certificates, OCSP/TSP responses
and ZIP/BDOC containers. Executions must be generated. Done within the time
box: a single-mix-server, keywidth-5 Verificatum 3.1.0 execution, generated
deterministically with vmn's demo scripts (seeded PRGHeuristic, as
`../verificatum-diff/gen_session.sh`), 5 ciphertexts:

| Group | vmnv `-mix -e -v` | IVXV verifier (own reader / probe) | IVXV, two outputs swapped |
|---|---|---|---|
| Helios mod-p (2048-bit p, 256-bit q, not safe prime) | accept | reject ("A failed") | reject |
| `vog -gen ModPGroup -fixed 2048` (safe prime) | accept | **accept / accept** | **reject** ("A failed") |

The first row is a configuration mismatch, not an IVXV defect: IVXV supports
safe-prime groups only and computes the order as (p−1)/2. The probe is
`probe/ee/ivxv/audit/shuffle/ProbeShuffle.java` (our code; `--official` runs
IVXV's own `ShuffleProof(protInfo, dir)` reader on a copy of the execution
laid out as IVXV expects, with `ShuffledCiphertexts.bt` =
`proofs/Ciphertexts01.bt`).

Not tried within the time box: generating an election with IVXV's own `key`
(key generation, decryption with proofs) and `processor` applications, which
need election configuration files and signed inputs (test certificates exist
under `common/collector/*/testdata`).

## Observations (to triage in the campaign, not findings yet)

1. `Verifier.verify_all(boolean throwexception)` returns **true** when a
   `ShuffleException` or `MathException` is thrown and `throwexception` is
   true (the exception is caught and not rethrown). It has no caller in this
   tree (`MixerTool` uses `verify_all()`, which throws), so it is dead code;
   a latent hazard if it is ever used.
2. Go `ProofProve`/`ProofVerify` (`elgamal.go`): the challenge hashes only
   the group product of the commitments; for several relations sharing one
   response this binds only the product relation. Also the commitment array
   index advances by one per relation (`added++`) instead of by the number of
   commitments of that relation, so with several relations commitments
   overwrite each other. No production caller in this tree; the deployed
   decryption-share proofs use `ProofChallenge`, which hashes each value.
   Needs careful triage (and, if relevant to a deployed path, responsible
   disclosure via the Electoral Office); no attack was constructed.
3. `nizkp.Verify` checks base^s = element^c · (base^s · element^{-c}), an
   identity; soundness rests entirely on the recomputed challenge (correct
   for compact proofs, but the equality check is redundant).
4. IVXV's `ModPGroup` ignores the subgroup order in Verificatum's group
   description and assumes a safe prime; on a non-safe-prime group it
   rejects honest proofs (no false accept observed).

## Recommended campaign and effort

- S1 honest: Verificatum executions (safe-prime mod-p and P-384, keywidth 5,
  one mix server, several N) — three-way: vmnv, IVXV verifier, certified.
- S3/S4 field and structural mutants of the byte trees (reuse
  `../verificatum-diff`), compared across the three.
- S5/S6 certified-prover proofs of false shuffles and single-check
  forgeries for the TW checks (with `../verificatum-diff` once it has them),
  verdicts only.
- Decryption proofs: honest proofs from IVXV's `key` app (if an election can
  be set up offline) or from IVXV's `ElGamalDecryptionProof` API directly,
  mutants, certified Chaum–Pedersen verifier.
- Go core: build, honest proofs from its API, mutants, certified verifier.
- Not realistic: S7 (no published election, signed inputs with ID-card
  infrastructure), S8 optional.

Effort: about 2–3 days of agent time — a certified instance at a safe-prime
group with keywidth 5 (and, optionally, P-384), the three-way shuffle
harness, the decryption-proof harness, the Go harness. Blockers: none hard;
P-384 needs a new curve instance; an IVXV-generated election (key and
processor apps) is uncertain.
