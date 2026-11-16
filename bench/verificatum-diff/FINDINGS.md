# Findings: certified verifier vs. Verificatum `vmnv` (VMN 3.1.0)

Differential testing of `vmnv` against our certified Verificatum verifier
(`src/Executable/Vmnverifier`) on mixing sessions produced by `vmn`, over the
certified 2048-bit Helios group, three mix-servers, threshold two. No forged
proof is accepted by either verifier, and no run produces a wrong plaintext.
The items below are a completeness bug we found and fixed in our own driver,
and robustness/strictness differences where `vmnv` is more lenient than the
certified verifier. None is a soundness break in `vmnv`.

## 1. Completeness bug in our driver (fixed): colliding `A'` across servers

**Severity: completeness, in our trusted driver — not the certified core, not `vmnv`.**

VMN's own demo scripts give every mix-server the *same* seed file, so the
servers run the Fiat-Shamir prover with the same randomness and their
proof-of-shuffle first announcements `A'` are identical. Our driver computed
each shuffle proof's challenge `v` by looking its commitment `tau` up in a
hash table keyed by `A'`. With equal `A'`, the table collided and the second
server's `tau` was used for the first server, so the certified verifier
received the wrong challenge and rejected an honest session that `vmnv`
accepts. Fixed by re-encoding each proof's `tau = (B, A', B', C', D', F')`
from the proof itself (and requiring it to equal the proof file's bytes).
After the fix both verifiers accept the honest session, with distinct or
shared seeds. The `--ours-before` column of the campaign records the pre-fix
driver rejecting the honest shared-seed session.

## 2. Decryption quorum: a corrupted reply from a listed-but-unneeded party

**Severity: low; strictness difference; no wrong plaintext accepted.**

`CorrectIndices.bt` lists all three servers while the threshold is two.
Changing server 3's decryption reply scalar: `vmnv` accepts (it combines only
a threshold-sized subset; the plaintexts are unchanged and equal the published
ones), the certified verifier rejects (per Algorithm 27 it combines every
listed party). Both sound; the certified verifier is the stricter and the
closer to the spec's written Delta handling.

## 3. Parser leniency: trailing array element in a proof reply

**Severity: low; parser robustness; no soundness impact.**

An extra trailing child on `PoSReply01.bt` is accepted by `vmnv` (surplus
ignored) and rejected by our parser (exact byte-tree shape). Same family as
the Swiss Post Base64/Base32 canonicity leniency.

## Agreement elsewhere

Both verifiers reject every field mutation of every proof file, every
structural/encoding mutation, every protocol tampering (two outputs swapped, a
server's output replaced by another's, a shared permutation commitment), and
the targeted `A'`-collision forgery. A flipped `CorrectIndices` that still
meets the threshold is accepted by both.
