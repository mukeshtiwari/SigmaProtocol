/*
 * GetVerifiableCommitmentKey (algorithm 9.6) of the library against an
 * implementation of the pseudocode over Spec.recursiveHashToZq, at the
 * 3072-bit group of the standard level (FUZZ_FIXTURE: a Swiss Post fixture
 * file to take p, q, g from), for ν chosen by the fuzzer; and the properties
 * the Bayer–Groth argument relies on: ν + 1 distinct members of G_q, none 1 or
 * g, the same key on every call. The key is deterministic in ν, so this is a
 * conformance sweep rather than a search; results are cached per ν.
 */
package ch.post.it.evoting.cryptoprimitives.internal.mixnet;

import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import com.code_intelligence.jazzer.api.FuzzedDataProvider;
import com.code_intelligence.jazzer.api.FuzzerSecurityIssueHigh;

import ch.post.it.evoting.cryptoprimitives.fuzz.Spec;
import ch.post.it.evoting.cryptoprimitives.internal.hashing.HashService;
import ch.post.it.evoting.cryptoprimitives.internal.securitylevel.SecurityLevelConfig;
import ch.post.it.evoting.cryptoprimitives.math.GqElement;
import ch.post.it.evoting.cryptoprimitives.math.GqGroup;

public final class CommitmentKeyFuzz {

	private static GqGroup group;
	private static final CommitmentKeyService service = new CommitmentKeyService(HashService.getInstance());
	private static final int lambda = SecurityLevelConfig.getSystemSecurityLevel().getSecurityStrength();
	private static final java.util.Set<Integer> done = new HashSet<>();

	public static void fuzzerInitialize() throws IOException {
		final BigInteger[] pqg = Spec.groupOfFixture(Path.of(System.getenv("FUZZ_FIXTURE")));
		group = new GqGroup(pqg[0], pqg[1], pqg[2]);
	}

	/** algorithm 9.6; ("commitmentKey", i, count) are three values of RecursiveHashToZq, not one vector (as the
	 * library and get-verifiable-commitment-key.json read the pseudocode) */
	static List<BigInteger> spec(final int nu, final BigInteger p, final BigInteger q, final BigInteger g) {
		int count = 0;
		int i = 0;
		final List<BigInteger> v = new ArrayList<>();
		while (count <= nu) {
			final BigInteger u = Spec.recursiveHashToZq(q, lambda,
					new Spec.Str("commitmentKey"), new Spec.Int(BigInteger.valueOf(i)), new Spec.Int(BigInteger.valueOf(count)))
					.add(BigInteger.ONE);
			final BigInteger w = u.modPow(BigInteger.TWO, p);
			if (!w.equals(BigInteger.ONE) && !w.equals(g) && !v.contains(w)) {
				v.add(w);
				count++;
			}
			i++;
		}
		return v;
	}

	public static void fuzzerTestOneInput(final FuzzedDataProvider d) {
		final int nu = d.consumeInt(-3, 80);
		if (nu <= 0) {
			try {
				service.getVerifiableCommitmentKey(nu, group);
			} catch (final IllegalArgumentException _) {
				return;
			}
			throw new FuzzerSecurityIssueHigh("GetVerifiableCommitmentKey accepts ν = " + nu);
		}
		if (!done.add(nu)) {
			return;
		}
		final CommitmentKey ck = service.getVerifiableCommitmentKey(nu, group);
		final List<BigInteger> lib = new ArrayList<>();
		lib.add(ck.getH().getValue());
		ck.getG().stream().map(GqElement::getValue).forEach(lib::add);
		if (!lib.equals(spec(nu, group.getP(), group.getQ(), group.getGenerator().getValue()))) {
			throw new FuzzerSecurityIssueHigh("GetVerifiableCommitmentKey(" + nu + ") differs from algorithm 9.6");
		}
		if (lib.size() != nu + 1 || new HashSet<>(lib).size() != nu + 1 || ck.size() != nu) {
			throw new FuzzerSecurityIssueHigh("GetVerifiableCommitmentKey(" + nu + ") has not ν + 1 distinct elements");
		}
		for (final BigInteger w : lib) {
			if (!group.isGroupMember(w) || w.equals(BigInteger.ONE) || w.equals(group.getGenerator().getValue())) {
				throw new FuzzerSecurityIssueHigh("GetVerifiableCommitmentKey(" + nu + ") has an element outside G_q \\ {1, g}");
			}
		}
		if (!service.getVerifiableCommitmentKey(nu, group).equals(ck)) {
			throw new FuzzerSecurityIssueHigh("GetVerifiableCommitmentKey(" + nu + ") is not deterministic");
		}
	}
}
