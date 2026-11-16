/*
 * Conversions and encodings of the library (ConversionsInternal, ByteArrays,
 * Base16/32/64) against Spec: equal outputs, or both rejecting (the library by
 * IllegalArgumentException, Spec by Bottom). Decoders must also be canonical:
 * a string that decodes must be the encoding of what it decodes to (RFC 4648
 * Section 3.5 lets a decoder accept non-canonical encodings; the specification
 * calls the encodings injective and requires valid input to decode).
 */
package ch.post.it.evoting.cryptoprimitives.fuzz;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.function.Supplier;

import com.code_intelligence.jazzer.api.FuzzedDataProvider;
import com.code_intelligence.jazzer.api.FuzzerSecurityIssueHigh;
import com.code_intelligence.jazzer.api.FuzzerSecurityIssueLow;

import ch.post.it.evoting.cryptoprimitives.collection.ImmutableByteArray;
import ch.post.it.evoting.cryptoprimitives.internal.utils.ByteArrays;
import ch.post.it.evoting.cryptoprimitives.internal.utils.ConversionsInternal;
import ch.post.it.evoting.cryptoprimitives.math.Base16;
import ch.post.it.evoting.cryptoprimitives.math.Base32;
import ch.post.it.evoting.cryptoprimitives.math.Base64;
import ch.post.it.evoting.cryptoprimitives.math.BaseEncodingFactory;

public final class EncodingFuzz {

	private static final Base16 base16 = BaseEncodingFactory.createBase16();
	private static final Base32 base32 = BaseEncodingFactory.createBase32();
	private static final Base64 base64 = BaseEncodingFactory.createBase64();

	/** the library's result, or null when it rejects with IllegalArgumentException */
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

	private static void same(final String what, final Object lib, final Object spec, final Object input) {
		final boolean eq = lib instanceof byte[] a && spec instanceof byte[] b ? Arrays.equals(a, b) : java.util.Objects.equals(lib, spec);
		if (!eq) {
			throw new FuzzerSecurityIssueHigh(what + ": library " + show(lib) + ", specification " + show(spec) + ", input " + show(input));
		}
	}

	private static String show(final Object o) {
		return o instanceof byte[] b ? java.util.HexFormat.of().formatHex(b) : o instanceof String s ? '"' + s.codePoints()
				.mapToObj(c -> c < 0x20 || c > 0x7e ? String.format("\\u{%x}", c) : Character.toString(c)).reduce("", String::concat) + '"'
				: String.valueOf(o);
	}

	private static byte[] bytes(final ImmutableByteArray b) {
		return b == null ? null : b.elements();
	}

	public static void fuzzerTestOneInput(final FuzzedDataProvider d) {
		switch (d.consumeInt(0, 8)) {
		case 0 -> {   // IntegerToByteArray (3.9), and back (3.8)
			final BigInteger x0 = new BigInteger(1, d.consumeBytes(d.consumeInt(0, 64)));
			final BigInteger x = d.consumeInt(0, 15) == 0 ? x0.negate() : x0;
			final byte[] l = bytes(lib(() -> ConversionsInternal.integerToByteArray(x)));
			same("IntegerToByteArray", l, spec(() -> Spec.integerToByteArray(x)), x);
			if (l != null) {
				same("ByteArrayToInteger(IntegerToByteArray(x))", ConversionsInternal.byteArrayToInteger(ImmutableByteArray.of(l)), x, x);
			}
		}
		case 1 -> {   // ByteArrayToInteger (3.8)
			final byte[] b = d.consumeBytes(d.consumeInt(0, 64));
			same("ByteArrayToInteger", lib(() -> ConversionsInternal.byteArrayToInteger(ImmutableByteArray.of(b))), Spec.byteArrayToInteger(b), b);
		}
		case 2 -> {   // IntegerToFixedLengthByteArray (3.10)
			final BigInteger x0 = new BigInteger(1, d.consumeBytes(d.consumeInt(0, 40)));
			final BigInteger x = d.consumeInt(0, 15) == 0 ? x0.negate() : x0;
			final int m = d.consumeInt(-2, 48);
			same("IntegerToFixedLengthByteArray(m = " + m + ")", bytes(lib(() -> ConversionsInternal.integerToFixedLengthByteArray(x, m))),
					spec(() -> Spec.integerToFixedLengthByteArray(x, m)), x);
		}
		case 3 -> {   // StringToByteArray (3.12)
			final String s = d.consumeString(d.consumeInt(0, 40));
			same("StringToByteArray", bytes(lib(() -> ConversionsInternal.stringToByteArray(s))), spec(() -> Spec.stringToByteArray(s)), s);
		}
		case 4 -> {   // ByteArrayToString (3.13)
			final byte[] b = d.consumeBytes(d.consumeInt(0, 40));
			same("ByteArrayToString", lib(() -> ConversionsInternal.byteArrayToString(ImmutableByteArray.of(b))), spec(() -> Spec.byteArrayToString(b)), b);
		}
		case 5 -> {   // CutToBitLength (3.1)
			final byte[] b = d.consumeBytes(d.consumeInt(0, 40));
			final int n = d.consumeInt(-1, b.length * 8 + 9);
			same("CutToBitLength(n = " + n + ")", bytes(lib(() -> ByteArrays.cutToBitLength(ImmutableByteArray.of(b), n))),
					spec(() -> Spec.cutToBitLength(b, n)), b);
		}
		case 6 -> {   // the encoders (3.2, 3.4, 3.6) and decode ∘ encode = id
			final byte[] b = d.consumeBytes(d.consumeInt(0, 40));
			final ImmutableByteArray ib = ImmutableByteArray.of(b);
			same("Base16Encode", base16.base16Encode(ib), Spec.base16(b), b);
			same("Base32Encode", base32.base32Encode(ib), Spec.base32(b), b);
			same("Base64Encode", base64.base64Encode(ib), Spec.base64(b), b);
			same("Base16Decode(Base16Encode(B))", base16.base16Decode(Spec.base16(b)).elements(), b, b);
			same("Base32Decode(Base32Encode(B))", base32.base32Decode(Spec.base32(b)).elements(), b, b);
			same("Base64Decode(Base64Encode(B))", base64.base64Decode(Spec.base64(b)).elements(), b, b);
		}
		case 7 -> {   // the decoders (3.3, 3.5, 3.7) accept only canonical encodings
			final String s = d.consumeAsciiString(d.consumeInt(0, 24));
			final byte[] b16 = bytes(lib(() -> base16.base16Decode(s)));
			if (b16 != null && !Spec.base16(b16).equals(s)) {
				throw new FuzzerSecurityIssueLow("Base16Decode accepts the non-canonical " + show(s) + " for " + show(b16));
			}
			final byte[] b32 = bytes(lib(() -> base32.base32Decode(s)));
			if (b32 != null && !Spec.base32(b32).equals(s)) {
				throw new FuzzerSecurityIssueLow("Base32Decode accepts the non-canonical " + show(s) + " for " + show(b32));
			}
			final byte[] b64 = bytes(lib(() -> base64.base64Decode(s)));
			if (b64 != null && !Spec.base64(b64).equals(s)) {
				throw new FuzzerSecurityIssueLow("Base64Decode accepts the non-canonical " + show(s) + " for " + show(b64));
			}
		}
		default -> {   // StringToInteger (3.14), IntegerToString (3.15)
			final String s = d.consumeString(d.consumeInt(0, 24));
			final BigInteger l = lib(() -> ConversionsInternal.stringToInteger(s));
			same("StringToInteger", l, spec(() -> Spec.stringToInteger(s)), s);
			if (l != null) {
				same("StringToInteger(IntegerToString(x))", ConversionsInternal.stringToInteger(ConversionsInternal.integerToString(l)), l, s);
			}
		}
		}
	}
}
