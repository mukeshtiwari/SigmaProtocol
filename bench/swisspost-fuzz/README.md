# Fuzzing the Swiss Post crypto-primitives library

Coverage-guided fuzzing ([Jazzer](https://github.com/CodeIntelligenceTesting/jazzer) 0.30.0, libFuzzer for the JVM) of the Swiss Post crypto-primitives library, the submodule [../crypto-primitives](../crypto-primitives) at commit 94a8438. The targets run the Java library alone (no certified verifier in the loop); where they compare outputs, it is against independent implementations of the specification's pseudocode in [Spec.java](src/ch/post/it/evoting/cryptoprimitives/fuzz/Spec.java), written from Crypto-Primitives Specification 1.6.0 and sharing only SHA3-256 (JDK) and SHAKE-256 (BouncyCastle) with the library.

```sh
git submodule update --init bench/crypto-primitives
# JDK 25 (brew install openjdk@25): Jazzer 0.30's ASM cannot read the class files of JDK 26+
export JAVA_HOME=/opt/homebrew/opt/openjdk@25/libexec/openjdk.jdk/Contents/Home
# Jazzer release: jazzer-macos.tar.gz (or -linux-*) from GitHub, unpacked in JAZZER_DIR
bench/swisspost-fuzz/build.sh bench/crypto-primitives JAZZER_DIR BUILD_DIR
bench/swisspost-fuzz/run.sh TARGET SECONDS BUILD_DIR JAZZER_DIR WORK_DIR          # fuzz
bench/swisspost-fuzz/run.sh TARGET 0 BUILD_DIR JAZZER_DIR WORK_DIR CRASH_FILE     # replay one input
```

`build.sh` compiles the library's main sources with the targets on the class path. There a sealed type may only permit subclasses of its own package, so the build strips `sealed … permits …` from a copy of the six sealed declarations (VerificationResult, Base16/32/64, Alphabet, GqElement); nothing else is changed. The targets sit in the library's packages to reach its package-private services. `run.sh` keeps the corpus, crashing inputs and Jazzer's Java reproducers in `WORK_DIR/TARGET/` and continues past findings with distinct stack traces (`--keep_going`).

## Targets

| target | what it checks |
|---|---|
| `ShuffleFuzz` | The Bayer–Groth verifiers on mutated honest arguments: the shuffle argument through the production entry point `MixnetService.verifyShuffle` (both optimization modes, so with and without the Hadamard argument; N ∈ {2, 3, 4, 6, 9}, l ∈ {1, 2}), and the product and multi-exponentiation arguments directly. Honest arguments come from the library's own provers once, at a 1024-bit safe-prime group (`SECURITY_LEVEL=TESTING_ONLY`, for speed). Each input applies 1–4 mutations: a value made random, multiplied by g / +1, set to 1 / 0, set to an out-of-range raw value (0, p, q, p ± 1, −1, 2^\|p\|, …), inverted / negated, or copied from another field; a vector entry removed, duplicated or swapped; a ciphertext given one component more or fewer. A finding is an accepted argument that differs from the honest one, or any exception other than the `IllegalArgumentException`/`NullPointerException` of the library's precondition checks. |
| `RecursiveHashFuzz` | RecursiveHash (5.5), RecursiveHashOfLength (5.7) and RecursiveHashToZq (5.6) against `Spec` on random values of the domain 𝒱 (nested lists of byte arrays, integers, strings), plus inputs outside it (negative integers, unpaired surrogates) that both must reject; and injectivity (no two different values with the same digest). |
| `EncodingFuzz` | IntegerToByteArray, ByteArrayToInteger, IntegerToFixedLengthByteArray, StringToByteArray, ByteArrayToString, CutToBitLength, StringToInteger / IntegerToString, and the Base16/32/64 encoders against `Spec` (an RFC 4648 encoder); decode ∘ encode = id; and that the decoders accept only canonical encodings. |
| `CommitmentKeyFuzz` | GetVerifiableCommitmentKey (9.6) at the 3072-bit standard group against the pseudocode over `Spec.recursiveHashToZq`, for ν ≤ 80; ν + 1 distinct members of G_q \ {1, g}; determinism; rejection of ν ≤ 0. The key is a deterministic function of ν, so this is a conformance sweep that saturates quickly. |

## Results

Apple M-series laptop, the four targets run concurrently, Jazzer 0.30.0 on JDK 25.0.4:

| target | time | executions | exec/s | findings |
|---|---|---|---|---|
| `ShuffleFuzz` | 30 + 20 min | 219,317 + 156,005 | 121–129 | no mutated argument accepted; finding 2 |
| `RecursiveHashFuzz` | 15 min | 4,528,934 | 5,026 | none: equal to the specification, no collision |
| `EncodingFuzz` | 10 min | 269,479,587 | 448,385 | finding 1 |
| `CommitmentKeyFuzz` | 5 min | 374,809,944 (ν ≤ 80, each computed once) | — | none: equal to algorithm 9.6 |

`Findings.java` reproduces both findings deterministically (`java -cp BUILD_DIR/classes:BUILD_DIR/lib/* ch.post.it.evoting.cryptoprimitives.fuzz.Findings`). Neither affects soundness.

1. **Base64Decode and Base32Decode accept non-canonical encodings** (low). `Base64Decode` accepts non-zero pad bits and missing padding (`"QR=="`, `"QQ"` and `"QQ=="` all decode to `<0x41>`; `"Af"` to `<0x01>`); `Base32Decode` likewise (`"IF======"`, `"IE"` → `<0x41>`, `"AQ"` → `<0x04>`) and decodes strings of only `=` (`"="`, `"========"`) to the empty array. The services delegate to `java.util.Base64` and Guava's `BaseEncoding`, which are lenient. RFC 4648 §3.5 permits this, but the specification calls the encodings injective and requires valid input for decoding, so one byte array has several accepted string forms. In the library the only decoding of untrusted input is `SymmetricAuthenticatedEncryptionService.getSymmetricCiphertextParts`, whose bytes are then authenticated by AES-GCM, so the malleability is of the string only; it matters to a caller that compares or deduplicates encoded strings. Base16 is strict.
2. **An empty vector makes constructors throw `IllegalStateException`** (low, robustness). `GroupVector.getGroup()` throws `IllegalStateException` on an empty vector (as documented), and six constructors call it before checking sizes: `ShuffleArgument` (line 59, empty c_A), `ProductStatement` (52), `SingleValueProductArgument` (70, inside a parallel stream, so wrapped in a second `IllegalStateException`), `ZeroArgument` (72), `MultiExponentiationArgument` (73, 75). Every other malformed argument is refused with the `IllegalArgumentException` of the precondition checks, so a caller that handles that exception for untrusted arguments sees a different, unchecked exception here. The input is still refused; nothing is accepted.

Observations that are not findings: the pseudocode of RecursiveHashToZq (5.6) hashes (q, "RecursiveHash", **v**), and 9.6 passes ("commitmentKey", i, count) in parentheses; with the bold **v** read as one vector, as in 5.5, the results would differ. The library splices the values in flat, and the Swiss Post test vectors (`recursive-hash-to-zq.json`, `get-verifiable-commitment-key.json`) agree with the library, so this is at most a notational ambiguity; `Spec` follows the vectors. The production default `COMPUTATION_OPTIMIZED` always uses m = 1 (no Hadamard or zero argument); `ShuffleFuzz` also covers `MEMORY_OPTIMIZED`.

Limits: random and coverage-guided mutations cannot be expected to find a soundness flaw that needs an algebraically crafted argument (consistent Fiat–Shamir challenges); `ShuffleFuzz` tests that every field is checked, and that malformed arguments are refused cleanly. The honest cases are regenerated at random on each start, so a crashing input replays the same mutations on fresh values.
