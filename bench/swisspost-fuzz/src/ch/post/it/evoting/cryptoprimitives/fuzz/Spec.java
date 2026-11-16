/*
 * Independent implementations of algorithms of the Crypto-Primitives
 * Specification 1.6.0, written from the pseudocode and not from the library,
 * against which the fuzz targets compare the library: conversions (3.1, 3.8 to
 * 3.13), RFC 4648 encodings (3.2 to 3.7), RecursiveHash (5.5),
 * RecursiveHashToZq (5.6) and RecursiveHashOfLength (5.7). The only primitives
 * taken from elsewhere are SHA3-256 (the JDK) and SHAKE-256 (BouncyCastle).
 */
package ch.post.it.evoting.cryptoprimitives.fuzz;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.bouncycastle.crypto.digests.SHAKEDigest;

import com.code_intelligence.jazzer.api.FuzzedDataProvider;

import ch.post.it.evoting.cryptoprimitives.collection.ImmutableByteArray;
import ch.post.it.evoting.cryptoprimitives.collection.ImmutableList;
import ch.post.it.evoting.cryptoprimitives.hashing.Hashable;
import ch.post.it.evoting.cryptoprimitives.hashing.HashableBigInteger;
import ch.post.it.evoting.cryptoprimitives.hashing.HashableList;
import ch.post.it.evoting.cryptoprimitives.hashing.HashableString;

public final class Spec {

	private Spec() {
	}

	/** Thrown where the specification returns ⊥ or a Require clause fails. */
	public static final class Bottom extends RuntimeException {
		public Bottom(final String msg) {
			super(msg, null, false, false);
		}
	}

	// ---- groups ----

	/** A 1024-bit safe prime p = 2q + 1 with p ≡ 23 (mod 24) (openssl dhparam -2 1024): 2 generates G_q (testing-only level). */
	public static final BigInteger P1024 = new BigInteger(
			"967140554E7C8C2A7324B86F5A1A8985EA991B035674C9C65089E538DF031191"
					+ "FD48D562D38F627041FB826E7F7BC332A87FC752B0F2F265E84062924058FC55"
					+ "B658E9DFE2F86E138F08028A498FC7581726AA4C40459649A431CEFE88444200"
					+ "D02C6B6F98521BF82DD9D6A38F5BBD238569F330848DC4CB633F86AE90C2C037", 16);

	/** p, q, g of the first case of a Swiss Post fixture file (the 3072-bit group of the standard level). */
	public static BigInteger[] groupOfFixture(final Path fixture) throws IOException {
		final String s = Files.readString(fixture);
		final BigInteger[] r = new BigInteger[3];
		final String[] names = { "p", "q", "g" };
		for (int i = 0; i < 3; i++) {
			final Matcher m = Pattern.compile("\"" + names[i] + "\"\\s*:\\s*\"([A-Za-z0-9+/=]+)\"").matcher(s);
			if (!m.find()) {
				throw new IOException("no " + names[i] + " in " + fixture);
			}
			r[i] = new BigInteger(java.util.Base64.getDecoder().decode(m.group(1)));
		}
		return r;
	}

	// ---- conversions (Section 3) ----

	/** Algorithm 3.11 */
	public static int byteLength(final BigInteger x) {
		return (x.bitLength() + 7) / 8;
	}

	/** Algorithm 3.8 */
	public static BigInteger byteArrayToInteger(final byte[] b) {
		BigInteger x = BigInteger.ZERO;
		for (final byte bi : b) {
			x = x.shiftLeft(8).add(BigInteger.valueOf(bi & 0xff));
		}
		return x;
	}

	/** Algorithm 3.10 */
	public static byte[] integerToFixedLengthByteArray(final BigInteger x0, final int m) {
		if (x0.signum() < 0 || m < 0) {
			throw new Bottom("x or m not in N");
		}
		if (byteLength(x0) > m) {
			throw new Bottom("ByteLength(x) > m");
		}
		BigInteger x = x0;
		final byte[] b = new byte[m];
		final BigInteger b256 = BigInteger.valueOf(256);
		for (int i = 0; i < m; i++) {
			b[m - i - 1] = (byte) x.mod(b256).intValue();
			x = x.divide(b256);
		}
		return b;
	}

	/** Algorithm 3.9 */
	public static byte[] integerToByteArray(final BigInteger x) {
		if (x.signum() < 0) {
			throw new Bottom("x not in N");
		}
		return integerToFixedLengthByteArray(x, byteLength(x));
	}

	/** Algorithm 3.1 */
	public static byte[] cutToBitLength(final byte[] B, final int n) {
		final int N = B.length;
		if (n < 0 || n > N * 8) {
			throw new Bottom("n > 8N");
		}
		final int length = (n + 7) / 8;
		final int offset = N - length;
		final byte[] r = new byte[length];
		for (int i = 0; i < length; i++) {
			r[i] = B[offset + i];
		}
		if (n % 8 != 0) {
			r[0] = (byte) (B[offset] & ((1 << (n % 8)) - 1));
		}
		return r;
	}

	/** Algorithm 3.12: UTF-8 of a string of UCS code points (RFC 3629); an unpaired surrogate is not a UCS string */
	public static byte[] stringToByteArray(final String s) {
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		for (int i = 0; i < s.length(); i++) {
			final char c = s.charAt(i);
			int cp;
			if (Character.isHighSurrogate(c)) {
				if (i + 1 < s.length() && Character.isLowSurrogate(s.charAt(i + 1))) {
					cp = 0x10000 + ((c - 0xD800) << 10) + (s.charAt(i + 1) - 0xDC00);
					i++;
				} else {
					throw new Bottom("unpaired high surrogate");
				}
			} else if (Character.isLowSurrogate(c)) {
				throw new Bottom("unpaired low surrogate");
			} else {
				cp = c;
			}
			if (cp < 0x80) {
				out.write(cp);
			} else if (cp < 0x800) {
				out.write(0xC0 | cp >> 6);
				out.write(0x80 | cp & 0x3F);
			} else if (cp < 0x10000) {
				out.write(0xE0 | cp >> 12);
				out.write(0x80 | cp >> 6 & 0x3F);
				out.write(0x80 | cp & 0x3F);
			} else {
				out.write(0xF0 | cp >> 18);
				out.write(0x80 | cp >> 12 & 0x3F);
				out.write(0x80 | cp >> 6 & 0x3F);
				out.write(0x80 | cp & 0x3F);
			}
		}
		return out.toByteArray();
	}

	/** Algorithm 3.13: strict UTF-8 decoding (RFC 3629: no overlong forms, no surrogates, at most U+10FFFF) */
	public static String byteArrayToString(final byte[] b) {
		final StringBuilder sb = new StringBuilder();
		int i = 0;
		while (i < b.length) {
			final int b0 = b[i] & 0xff;
			final int len;
			int cp;
			final int min;
			if (b0 < 0x80) {
				len = 1;
				cp = b0;
				min = 0;
			} else if (b0 >= 0xC2 && b0 <= 0xDF) {
				len = 2;
				cp = b0 & 0x1F;
				min = 0x80;
			} else if (b0 >= 0xE0 && b0 <= 0xEF) {
				len = 3;
				cp = b0 & 0x0F;
				min = 0x800;
			} else if (b0 >= 0xF0 && b0 <= 0xF4) {
				len = 4;
				cp = b0 & 0x07;
				min = 0x10000;
			} else {
				throw new Bottom("invalid UTF-8 lead byte");
			}
			if (i + len > b.length) {
				throw new Bottom("truncated UTF-8");
			}
			for (int j = 1; j < len; j++) {
				final int bj = b[i + j] & 0xff;
				if ((bj & 0xC0) != 0x80) {
					throw new Bottom("invalid UTF-8 continuation");
				}
				cp = cp << 6 | bj & 0x3F;
			}
			if (cp < min || cp > 0x10FFFF || cp >= 0xD800 && cp <= 0xDFFF) {
				throw new Bottom("overlong, surrogate or out of range");
			}
			sb.appendCodePoint(cp);
			i += len;
		}
		return sb.toString();
	}

	/** Algorithm 3.14: a non-empty string of the decimal alphabet 𝔸10 */
	public static BigInteger stringToInteger(final String s) {
		if (s.isEmpty()) {
			throw new Bottom("empty");
		}
		BigInteger x = BigInteger.ZERO;
		for (int i = 0; i < s.length(); i++) {
			final char c = s.charAt(i);
			if (c < '0' || c > '9') {
				throw new Bottom("not a decimal digit");
			}
			x = x.multiply(BigInteger.TEN).add(BigInteger.valueOf(c - '0'));
		}
		return x;
	}

	// ---- RFC 4648 encodings (algorithms 3.2, 3.4, 3.6) ----

	private static String encodeBits(final byte[] b, final String alphabet, final int bits, final int block) {
		final StringBuilder sb = new StringBuilder();
		int buffer = 0;
		int n = 0;
		for (final byte x : b) {
			buffer = buffer << 8 | x & 0xff;
			n += 8;
			while (n >= bits) {
				sb.append(alphabet.charAt(buffer >> n - bits & (1 << bits) - 1));
				n -= bits;
			}
		}
		if (n > 0) {
			sb.append(alphabet.charAt(buffer << bits - n & (1 << bits) - 1));
		}
		while (sb.length() % block != 0) {
			sb.append('=');
		}
		return sb.toString();
	}

	public static String base16(final byte[] b) {
		return encodeBits(b, "0123456789ABCDEF", 4, 1);
	}

	public static String base32(final byte[] b) {
		return encodeBits(b, "ABCDEFGHIJKLMNOPQRSTUVWXYZ234567", 5, 8);
	}

	public static String base64(final byte[] b) {
		return encodeBits(b, "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/", 6, 4);
	}

	// ---- the recursive-hash domain 𝒱 ----

	public interface Node {
	}

	public record Bytes(byte[] b) implements Node {
	}

	public record Int(BigInteger x) implements Node {
	}

	public record Str(String s) implements Node {
	}

	public record Lst(List<Node> xs) implements Node {
	}

	/** a random value of 𝒱 (and, rarely, outside it: negative integers, unpaired surrogates) */
	public static Node node(final FuzzedDataProvider d, final int depth) {
		switch (d.consumeInt(0, depth >= 3 ? 2 : 3)) {
		case 0:
			return new Bytes(d.consumeBytes(d.consumeInt(0, 48)));
		case 1: {
			final BigInteger x = new BigInteger(1, d.consumeBytes(d.consumeInt(0, 48)));
			return new Int(d.consumeInt(0, 63) == 0 ? x.negate().subtract(BigInteger.ONE) : x);
		}
		case 2: {
			String s = d.consumeString(d.consumeInt(0, 24));
			if (d.consumeInt(0, 63) == 0) {
				s = s + (d.consumeBoolean() ? '\uD800' : '\uDC00');
			}
			return new Str(s);
		}
		default: {
			final int k = d.consumeInt(0, 4);
			final List<Node> xs = new ArrayList<>();
			for (int i = 0; i < k; i++) {
				xs.add(node(d, depth + 1));
			}
			return new Lst(xs);
		}
		}
	}

	public static Hashable toLib(final Node n) {
		return switch (n) {
			case Bytes(final byte[] b) -> ImmutableByteArray.of(b);
			case Int(final BigInteger x) -> HashableBigInteger.from(x);
			case Str(final String s) -> HashableString.from(s);
			case Lst(final List<Node> xs) -> HashableList.from(ImmutableList.from(xs.stream().map(Spec::toLib).toList()));
			default -> throw new IllegalStateException();
		};
	}

	/** an unambiguous rendering of a value of 𝒱, for the injectivity check */
	public static String canon(final Node n) {
		return switch (n) {
			case Bytes(final byte[] b) -> "B" + java.util.HexFormat.of().formatHex(b);
			case Int(final BigInteger x) -> "I" + x;
			case Str(final String s) -> "S" + java.util.HexFormat.of().formatHex(s.getBytes(java.nio.charset.StandardCharsets.UTF_16BE));
			case Lst(final List<Node> xs) -> "L" + xs.size() + "(" + String.join(",", xs.stream().map(Spec::canon).toList()) + ")";
			default -> throw new IllegalStateException();
		};
	}

	private static byte[] concat(final byte prefix, final byte[] b) {
		final byte[] r = new byte[b.length + 1];
		r[0] = prefix;
		System.arraycopy(b, 0, r, 1, b.length);
		return r;
	}

	private static byte[] sha3(final byte[] m) {
		try {
			return MessageDigest.getInstance("SHA3-256").digest(m);
		} catch (final NoSuchAlgorithmException e) {
			throw new IllegalStateException(e);
		}
	}

	private static byte[] shake256(final int L, final byte[] m) {
		final SHAKEDigest d = new SHAKEDigest(256);
		d.update(m, 0, m.length);
		final byte[] r = new byte[L];
		d.doFinal(r, 0, L);
		return r;
	}

	/** Algorithm 5.5 */
	public static byte[] recursiveHash(final Node... v) {
		if (v.length == 0) {
			throw new Bottom("k = 0");
		}
		if (v.length > 1) {
			return recursiveHash(new Lst(List.of(v)));
		}
		return switch (v[0]) {
			case Bytes(final byte[] b) -> sha3(concat((byte) 0, b));
			case Int(final BigInteger x) -> sha3(concat((byte) 1, integerToByteArray(x)));
			case Str(final String s) -> sha3(concat((byte) 2, stringToByteArray(s)));
			case Lst(final List<Node> xs) -> {
				final ByteArrayOutputStream out = new ByteArrayOutputStream();
				out.write(3);
				for (final Node x : xs) {
					out.writeBytes(recursiveHash(x));
				}
				yield sha3(out.toByteArray());
			}
			default -> throw new IllegalStateException();
		};
	}

	/** Algorithm 5.7, with ℓ* = 512 (table 3) */
	public static byte[] recursiveHashOfLength(final int l, final Node... v) {
		if (v.length == 0) {
			throw new Bottom("k = 0");
		}
		if (l < 512) {
			throw new Bottom("ℓ < ℓ*");
		}
		final int L = (l + 7) / 8;
		if (v.length > 1) {
			return recursiveHashOfLength(l, new Lst(List.of(v)));
		}
		final byte[] m = switch (v[0]) {
			case Bytes(final byte[] b) -> concat((byte) 0, b);
			case Int(final BigInteger x) -> concat((byte) 1, integerToByteArray(x));
			case Str(final String s) -> concat((byte) 2, stringToByteArray(s));
			case Lst(final List<Node> xs) -> {
				final ByteArrayOutputStream out = new ByteArrayOutputStream();
				out.write(3);
				for (final Node x : xs) {
					out.writeBytes(recursiveHashOfLength(l, x));
				}
				yield out.toByteArray();
			}
			default -> throw new IllegalStateException();
		};
		return cutToBitLength(shake256(L, m), l);
	}

	/** Algorithm 5.6 */
	public static BigInteger recursiveHashToZq(final BigInteger q, final int lambda, final Node... v) {
		if (v.length == 0) {
			throw new Bottom("k = 0");
		}
		if (q.signum() <= 0 || q.bitLength() < 512) {
			throw new Bottom("q not in N+ or |q| < 512");
		}
		final Node[] w = new Node[v.length + 2];
		w[0] = new Int(q);
		w[1] = new Str("RecursiveHash");
		System.arraycopy(v, 0, w, 2, v.length);
		return byteArrayToInteger(recursiveHashOfLength(q.bitLength() + 2 * lambda, w)).mod(q);
	}
}
