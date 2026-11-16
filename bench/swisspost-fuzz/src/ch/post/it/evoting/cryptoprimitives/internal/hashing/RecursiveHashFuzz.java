/*
 * RecursiveHash (5.5), RecursiveHashOfLength (5.7) and RecursiveHashToZq (5.6)
 * of the library against Spec, on random values of the domain 𝒱 (and a few
 * outside it: negative integers, unpaired surrogates, which both must
 * reject); and injectivity: two different values never get the same digest.
 * In the package of HashService for the package-private
 * recursiveHashOfLength.
 */
package ch.post.it.evoting.cryptoprimitives.internal.hashing;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HexFormat;
import java.util.Map;
import java.util.function.Supplier;

import com.code_intelligence.jazzer.api.FuzzedDataProvider;
import com.code_intelligence.jazzer.api.FuzzerSecurityIssueCritical;
import com.code_intelligence.jazzer.api.FuzzerSecurityIssueHigh;

import ch.post.it.evoting.cryptoprimitives.fuzz.Spec;
import ch.post.it.evoting.cryptoprimitives.hashing.Hashable;
import ch.post.it.evoting.cryptoprimitives.internal.securitylevel.SecurityLevelConfig;

public final class RecursiveHashFuzz {

	private static final HashService hashService = HashService.getInstance();
	private static final int lambda = SecurityLevelConfig.getSystemSecurityLevel().getSecurityStrength();
	private static final Map<String, String> seen = new HashMap<>();

	private static <T> T lib(final Supplier<T> f) {
		try {
			return f.get();
		} catch (final IllegalArgumentException _) {
			return null;
		}
	}

	private static <T> T spec(final Supplier<T> f) {
		try {
			return f.get();
		} catch (final Spec.Bottom _) {
			return null;
		}
	}

	private static void same(final String what, final Object lib, final Object spec, final Spec.Node[] v) {
		final boolean eq = lib instanceof byte[] a && spec instanceof byte[] b ? Arrays.equals(a, b) : java.util.Objects.equals(lib, spec);
		if (!eq) {
			throw new FuzzerSecurityIssueHigh(what + ": library " + (lib instanceof byte[] a ? HexFormat.of().formatHex(a) : lib)
					+ ", specification " + (spec instanceof byte[] b ? HexFormat.of().formatHex(b) : spec)
					+ ", input " + String.join(", ", Arrays.stream(v).map(Spec::canon).toList()));
		}
	}

	private static Hashable[] toLib(final Spec.Node[] v) {
		return Arrays.stream(v).map(Spec::toLib).toArray(Hashable[]::new);
	}

	public static void fuzzerTestOneInput(final FuzzedDataProvider d) {
		final int mode = d.consumeInt(0, 3);
		final Spec.Node[] v = new Spec.Node[mode == 1 ? d.consumeInt(2, 4) : d.consumeInt(1, 3)];
		for (int i = 0; i < v.length; i++) {
			v[i] = Spec.node(d, 0);
		}
		switch (mode) {
		case 0, 1 -> {   // RecursiveHash; mode 1 always with k > 1 values
			final byte[] l = lib(() -> hashService.recursiveHash(toLib(v)).elements());
			same("RecursiveHash", l, spec(() -> Spec.recursiveHash(v)), v);
			if (l != null && v.length == 1) {
				final String key = HexFormat.of().formatHex(l);
				final String c = Spec.canon(v[0]);
				final String prev = seen.putIfAbsent(key, c);
				if (prev != null && !prev.equals(c)) {
					throw new FuzzerSecurityIssueCritical("RecursiveHash collision: " + prev + " and " + c);
				}
				if (seen.size() > 200_000) {
					seen.clear();
				}
			}
		}
		case 2 -> {   // RecursiveHashOfLength
			final int ell = d.consumeInt(0, 4200);
			same("RecursiveHashOfLength(ℓ = " + ell + ")", lib(() -> hashService.recursiveHashOfLength(ell, toLib(v)).elements()),
					spec(() -> Spec.recursiveHashOfLength(ell, v)), v);
		}
		default -> {   // RecursiveHashToZq
			final BigInteger q = new BigInteger(1, d.consumeBytes(d.consumeInt(0, 400)));
			same("RecursiveHashToZq(|q| = " + q.bitLength() + ")", lib(() -> hashService.recursiveHashToZq(q, toLib(v)).getValue()),
					spec(() -> Spec.recursiveHashToZq(q, lambda, v)), v);
		}
		}
	}
}
