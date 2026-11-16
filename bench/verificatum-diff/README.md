# Differential testing: Verificatum `vmnv` vs. our certified verifier

Runs Verificatum's own verifier `vmnv` (VMN 3.1.0) and our certified verifier
(`src/Executable/Vmnverifier`) on the same `vmn`-produced mixing sessions and
compares their verdicts, modelled on `bench/swisspost-diff`.

## Reproduce

```sh
dune build src/Executable/Vmnverifier/main.exe       # default opam switch
export JAVA_HOME=/opt/homebrew/opt/openjdk@25/libexec/openjdk.jdk/Contents/Home   # any JDK >= 21
bench/verificatum-diff/run.sh WORKDIR
```

`run.sh` downloads `verificatum-vmn-3.1.0-full.tar.gz` (sha256
`e848b870...e473aad`, pinned and checked), builds `vcr-3.1.0` and `vmn-3.1.0`
pure-Java into `WORKDIR/install`, generates three sessions with a fixed seed
(`gen_session.sh`: `shared` and `distinct` per-server seeds, and one with a
prime number of ciphertexts), runs `campaign.py` on each, and re-runs the
shared-seed campaign to confirm the verdict table is identical. The group is
the certified 2048-bit Helios group (`group.txt`), the one our verifier
targets.

- `gen_session.sh` drives VMN's demo scripts deterministically: every random
  source is VCR's `PRGHeuristic` seeded from a fixed string. `shared` gives
  all mix-servers one seed file (what VMN's demo does); `distinct` gives each
  its own.
- `campaign.py` makes one tampered copy of a proof directory per case and runs
  both verifiers on it: `honest`; `field` (one leaf per proof file changed, by
  type: group element x g / to 1 / random, scalar +1 / 0 / random, opaque
  byte flip); `structural` (short/long arrays, malformed byte tree, non-member
  element, out-of-range scalar); `protocol` (swapped outputs, replaced output
  list, shared permutation commitment, flipped `CorrectIndices`); and
  `forge-pos` (a crafted `A'` collision). `--ours-before BIN` adds a column
  for a second (e.g. pre-fix) build of our verifier.
- `vmnlib.py` reads and writes VMN byte trees and the group of a protocol info
  file.

## Results (fixed certified verifier)

`results/distinct-seed.tsv`, `results/shared-seed.tsv`: 79 cases each. Both
verifiers agree on 75; the 4 differences are all `vmnv`-accepts /
certified-rejects, each sound (no wrong plaintext). See `FINDINGS.md`:
a completeness bug we found and fixed in our own driver (colliding `A'` when
servers share a seed), a stricter decryption-quorum check, and a stricter
proof-array parser. The two seeded shared-session runs produce identical
verdict tables.

## Versions

verificatum-vmn 3.1.0, verificatum-vcr 3.1.0 (from the full 3.1.0 bundle,
sha256 `e848b870...`), built with OpenJDK 25 (any JDK >= 21). Verifier spec:
"How to Implement a Stand-alone Verifier for the Verificatum Mix-Net" 3.1.0.
