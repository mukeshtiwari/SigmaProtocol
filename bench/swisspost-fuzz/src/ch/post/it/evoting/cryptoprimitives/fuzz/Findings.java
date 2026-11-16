/*
 * Deterministic reproducers of the findings of README.md:
 *   java -cp BUILD_DIR/classes:BUILD_DIR/lib/* ch.post.it.evoting.cryptoprimitives.fuzz.Findings
 */
package ch.post.it.evoting.cryptoprimitives.fuzz;

import java.math.BigInteger;
import java.util.HexFormat;

import ch.post.it.evoting.cryptoprimitives.math.BaseEncodingFactory;
import ch.post.it.evoting.cryptoprimitives.math.GroupVector;
import ch.post.it.evoting.cryptoprimitives.math.ZqElement;
import ch.post.it.evoting.cryptoprimitives.math.ZqGroup;
import ch.post.it.evoting.cryptoprimitives.mixnet.ProductStatement;

public final class Findings {

	private Findings() {
	}

	private static void decode(final String name, final java.util.function.Function<String, byte[]> dec, final String... inputs) {
		for (final String s : inputs) {
			try {
				System.out.printf("  %s(\"%s\") = <%s>%n", name, s, HexFormat.of().formatHex(dec.apply(s)));
			} catch (final IllegalArgumentException e) {
				System.out.printf("  %s(\"%s\") rejected%n", name, s);
			}
		}
	}

	public static void main(final String[] args) {
		System.out.println("1. Base64Decode and Base32Decode accept non-canonical encodings (non-zero pad bits, missing padding, only padding):");
		final var b64 = BaseEncodingFactory.createBase64();
		final var b32 = BaseEncodingFactory.createBase32();
		decode("Base64Decode", s -> b64.base64Decode(s).elements(), "QQ==", "QR==", "QQ", "Af");
		decode("Base32Decode", s -> b32.base32Decode(s).elements(), "IE======", "IF======", "IE", "AQ", "=", "========");

		System.out.println("2. an empty vector makes constructors throw IllegalStateException, not the IllegalArgumentException of their checks:");
		try {
			new ProductStatement(GroupVector.of(), ZqElement.create(BigInteger.ONE, new ZqGroup(BigInteger.valueOf(11))));
			System.out.println("  new ProductStatement((), b) accepted");
		} catch (final RuntimeException e) {
			System.out.println("  new ProductStatement((), b) throws " + e);
		}
	}
}
