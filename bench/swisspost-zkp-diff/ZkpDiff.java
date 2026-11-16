/*
 * Differential-testing driver for the zero-knowledge proofs of the Swiss Post
 * crypto-primitives library (specification Section 10), compiled into the
 * crypto-primitives module (package internal.zeroknowledgeproofs) by build.sh.
 * Files are in the format of the library's test vectors
 * (src/test/resources/zeroknowledgeproofs/verify-KIND.json).
 *
 *   gen KIND FIXTURE OUT COUNT   COUNT honest proofs at the group of FIXTURE,
 *                                random sizes and auxiliary information;
 *                                the output field records the verdict of the
 *                                Swiss Post verifier
 *   verify KIND FILE             one line per case: true, false, or error: msg
 *
 * KIND is schnorr, exponentiation, plaintext-equality or decryption.
 */
package ch.post.it.evoting.cryptoprimitives.internal.zeroknowledgeproofs;

import java.io.File;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Base64;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import ch.post.it.evoting.cryptoprimitives.collection.AuxiliaryInformation;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientCiphertext;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientKeyPair;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientMessage;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientPublicKey;
import ch.post.it.evoting.cryptoprimitives.internal.hashing.HashService;
import ch.post.it.evoting.cryptoprimitives.internal.math.RandomService;
import ch.post.it.evoting.cryptoprimitives.math.GqElement;
import ch.post.it.evoting.cryptoprimitives.math.GqGroup;
import ch.post.it.evoting.cryptoprimitives.math.GroupVector;
import ch.post.it.evoting.cryptoprimitives.math.ZqElement;
import ch.post.it.evoting.cryptoprimitives.math.ZqGroup;
import ch.post.it.evoting.cryptoprimitives.zeroknowledgeproofs.DecryptionProof;
import ch.post.it.evoting.cryptoprimitives.zeroknowledgeproofs.ExponentiationProof;
import ch.post.it.evoting.cryptoprimitives.zeroknowledgeproofs.PlaintextEqualityProof;
import ch.post.it.evoting.cryptoprimitives.zeroknowledgeproofs.SchnorrProof;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

public final class ZkpDiff {

	private static final RandomService random = new RandomService();
	private static final ZeroKnowledgeProofService zkp = new ZeroKnowledgeProofService(random, HashService.getInstance());
	private static final DecryptionProofService decryption = new DecryptionProofService(random, HashService.getInstance());
	private static final java.util.Random rng = new java.util.Random();

	// ---- values: Base64 of BigInteger.toByteArray(), as in the test vectors ----

	private static String b64(final BigInteger v) {
		return "\"" + Base64.getEncoder().encodeToString(v.toByteArray()) + "\"";
	}

	private static String e(final GqElement x) {
		return b64(x.getValue());
	}

	private static String f(final ZqElement x) {
		return b64(x.getValue());
	}

	private static String arr(final Stream<String> xs) {
		return "[" + xs.collect(Collectors.joining(",")) + "]";
	}

	private static String jstr(final String s) {
		final StringBuilder sb = new StringBuilder("\"");
		for (final char c : s.toCharArray()) {
			if (c == '"' || c == '\\') {
				sb.append('\\').append(c);
			} else if (c < 0x20 || c > 0x7e) {
				sb.append(String.format("\\u%04x", (int) c));
			} else {
				sb.append(c);
			}
		}
		return sb.append('"').toString();
	}

	private static BigInteger dec(final JsonNode n) {
		return new BigInteger(Base64.getDecoder().decode(n.asString()));
	}

	private static GqElement el(final JsonNode n, final GqGroup g) {
		return GqElement.GqElementFactory.fromValue(dec(n), g);
	}

	private static ZqElement sc(final JsonNode n, final GqGroup g) {
		return ZqElement.create(dec(n), ZqGroup.sameOrderAs(g));
	}

	private static GroupVector<GqElement, GqGroup> els(final JsonNode n, final GqGroup g) {
		final List<GqElement> xs = new ArrayList<>();
		n.forEach(x -> xs.add(el(x, g)));
		return GroupVector.from(xs);
	}

	private static GroupVector<ZqElement, ZqGroup> scs(final JsonNode n, final GqGroup g) {
		final List<ZqElement> xs = new ArrayList<>();
		n.forEach(x -> xs.add(sc(x, g)));
		return GroupVector.from(xs);
	}

	private static AuxiliaryInformation aux(final JsonNode n) {
		final List<String> xs = new ArrayList<>();
		n.forEach(x -> xs.add(x.asString()));
		return AuxiliaryInformation.of(xs.toArray(String[]::new));
	}

	private static ElGamalMultiRecipientCiphertext ct(final JsonNode n, final GqGroup g) {
		return ElGamalMultiRecipientCiphertext.create(el(n.get("gamma"), g), els(n.get("phis"), g));
	}

	private static String ct(final ElGamalMultiRecipientCiphertext c) {
		return "{\"gamma\":" + e(c.getGamma()) + ",\"phis\":" + arr(c.getPhis().stream().map(ZkpDiff::e)) + "}";
	}

	// ---- random honest inputs ----

	private static final String[] AUX_POOL = { "", "test-0", "Test string 1", "ä", "日本語", "🗳", "é", "a\u0000b", "\\\"",
			"x".repeat(1000) };

	private static List<String> randomAux() {
		final int s = rng.nextInt(4) == 0 ? 0 : rng.nextInt(4);
		return IntStream.range(0, s).mapToObj(i -> AUX_POOL[rng.nextInt(AUX_POOL.length)]).toList();
	}

	private static ZqElement rz(final GqGroup g) {
		return ZqElement.create(random.genRandomInteger(g.getQ()), ZqGroup.sameOrderAs(g));
	}

	private static GqElement rg(final GqGroup g) {
		return g.getGenerator().exponentiate(rz(g));
	}

	private static String context(final GqGroup g) {
		return "\"context\":{\"p\":" + b64(g.getP()) + ",\"q\":" + b64(g.getQ()) + ",\"g\":" + e(g.getGenerator()) + "}";
	}

	private static String genCase(final String kind, final GqGroup g, final int i) {
		final List<String> a = randomAux();
		final AuxiliaryInformation ia = AuxiliaryInformation.of(a.toArray(String[]::new));
		final String auxJson = arr(a.stream().map(ZkpDiff::jstr));
		switch (kind) {
		case "schnorr" -> {
			final ZqElement x = rz(g);
			final GqElement y = g.getGenerator().exponentiate(x);
			final SchnorrProof pr = zkp.genSchnorrProof(x, y, ia);
			final boolean ok = zkp.verifySchnorrProof(pr, y, ia);
			return "{\"description\":\"java schnorr " + i + "\"," + context(g) + ",\"input\":{\"proof\":{\"e\":" + f(pr.get_e()) + ",\"z\":"
					+ f(pr.get_z()) + "},\"statement\":" + e(y) + ",\"additional_information\":" + auxJson + "},\"output\":{\"result\":\"" + ok + "\"}}";
		}
		case "exponentiation" -> {
			final int n = 1 + rng.nextInt(6);
			final ZqElement x = rz(g);
			final GroupVector<GqElement, GqGroup> bases = Stream.generate(() -> rg(g)).limit(n).collect(GroupVector.toGroupVector());
			final GroupVector<GqElement, GqGroup> ys = bases.stream().map(b -> b.exponentiate(x)).collect(GroupVector.toGroupVector());
			final ExponentiationProof pr = zkp.genExponentiationProof(bases, x, ys, ia);
			final boolean ok = zkp.verifyExponentiation(bases, ys, pr, ia);
			return "{\"description\":\"java exponentiation " + i + ", n=" + n + "\"," + context(g) + ",\"input\":{\"bases\":"
					+ arr(bases.stream().map(ZkpDiff::e)) + ",\"statement\":" + arr(ys.stream().map(ZkpDiff::e)) + ",\"proof\":{\"e\":"
					+ f(pr.get_e()) + ",\"z\":" + f(pr.get_z()) + "},\"additional_information\":" + auxJson + "},\"output\":{\"verif_result\":\""
					+ ok + "\"}}";
		}
		case "plaintext-equality" -> {
			final GqElement h = rg(g), h2 = rg(g), msg = rg(g);
			final ZqElement r = rz(g), r2 = rz(g);
			final ElGamalMultiRecipientCiphertext c = ElGamalMultiRecipientCiphertext.create(g.getGenerator().exponentiate(r),
					GroupVector.of(h.exponentiate(r).multiply(msg)));
			final ElGamalMultiRecipientCiphertext c2 = ElGamalMultiRecipientCiphertext.create(g.getGenerator().exponentiate(r2),
					GroupVector.of(h2.exponentiate(r2).multiply(msg)));
			final PlaintextEqualityProof pr = zkp.genPlaintextEqualityProof(c, c2, h, h2, GroupVector.of(r, r2), ia);
			final boolean ok = zkp.verifyPlaintextEquality(c, c2, h, h2, pr, ia);
			return "{\"description\":\"java plaintext-equality " + i + "\"," + context(g) + ",\"input\":{\"upper_c\":" + ct(c)
					+ ",\"upper_c_prime\":" + ct(c2) + ",\"h\":" + e(h) + ",\"h_prime\":" + e(h2) + ",\"proof\":{\"e\":" + f(pr.get_e())
					+ ",\"z\":" + arr(pr.get_z().stream().map(ZkpDiff::f)) + "},\"i_aux\":" + auxJson + "},\"output\":{\"output\":\"" + ok
					+ "\"}}";
		}
		case "decryption" -> {
			final int l = 1 + rng.nextInt(5);
			final int k = l + rng.nextInt(3);
			final ElGamalMultiRecipientKeyPair kp = ElGamalMultiRecipientKeyPair.genKeyPair(g, k, random);
			final ElGamalMultiRecipientPublicKey pk = kp.getPublicKey();
			final GroupVector<GqElement, GqGroup> ms = Stream.generate(() -> rg(g)).limit(l).collect(GroupVector.toGroupVector());
			final ZqElement r = rz(g);
			final ElGamalMultiRecipientCiphertext c = ElGamalMultiRecipientCiphertext.create(g.getGenerator().exponentiate(r),
					IntStream.range(0, l).mapToObj(j -> pk.get(j).exponentiate(r).multiply(ms.get(j))).collect(GroupVector.toGroupVector()));
			final ElGamalMultiRecipientMessage m = new ElGamalMultiRecipientMessage(ms);
			final DecryptionProof pr = decryption.genDecryptionProof(c, kp, m, ia);
			final boolean ok = zkp.verifyDecryption(c, pk, m, pr, ia);
			return "{\"description\":\"java decryption " + i + ", l=" + l + ", k=" + k + "\"," + context(g) + ",\"input\":{\"ciphertext\":"
					+ ct(c) + ",\"public_key\":" + arr(pk.stream().map(ZkpDiff::e)) + ",\"message\":" + arr(ms.stream().map(ZkpDiff::e))
					+ ",\"proof\":{\"e\":" + f(pr.e()) + ",\"z\":" + arr(pr.z().stream().map(ZkpDiff::f)) + "},\"additional_information\":"
					+ auxJson + "},\"output\":{\"verif_result\":\"" + ok + "\"}}";
		}
		default -> throw new IllegalArgumentException("unknown kind " + kind);
		}
	}

	// ---- verify, through the production entry points of ZeroKnowledgeProofService ----

	private static String verify(final String kind, final JsonNode t) {
		try {
			final JsonNode c = t.get("context");
			final GqGroup g = new GqGroup(dec(c.get("p")), dec(c.get("q")), dec(c.get("g")));
			final JsonNode in = t.get("input");
			final JsonNode pr = in.get("proof");
			final boolean ok = switch (kind) {
				case "schnorr" -> zkp.verifySchnorrProof(new SchnorrProof(sc(pr.get("e"), g), sc(pr.get("z"), g)), el(in.get("statement"), g),
						aux(in.get("additional_information")));
				case "exponentiation" -> zkp.verifyExponentiation(els(in.get("bases"), g), els(in.get("statement"), g),
						new ExponentiationProof(sc(pr.get("e"), g), sc(pr.get("z"), g)), aux(in.get("additional_information")));
				case "plaintext-equality" -> zkp.verifyPlaintextEquality(ct(in.get("upper_c"), g), ct(in.get("upper_c_prime"), g),
						el(in.get("h"), g), el(in.get("h_prime"), g), new PlaintextEqualityProof(sc(pr.get("e"), g), scs(pr.get("z"), g)),
						aux(in.get("i_aux")));
				case "decryption" -> zkp.verifyDecryption(ct(in.get("ciphertext"), g), new ElGamalMultiRecipientPublicKey(els(in.get("public_key"), g)),
						new ElGamalMultiRecipientMessage(els(in.get("message"), g)), new DecryptionProof(sc(pr.get("e"), g), scs(pr.get("z"), g)),
						aux(in.get("additional_information")));
				default -> throw new IllegalArgumentException("unknown kind " + kind);
			};
			return Boolean.toString(ok);
		} catch (final RuntimeException ex) {
			return "error: " + ex.getClass().getSimpleName() + ": " + String.valueOf(ex.getMessage()).replace('\n', ' ');
		}
	}

	public static void main(final String[] args) throws IOException {
		final JsonMapper mapper = JsonMapper.builder().build();
		switch (args[0]) {
		case "gen" -> {
			final JsonNode c = mapper.readTree(new File(args[2])).get(0).get("context");
			final GqGroup g = new GqGroup(dec(c.get("p")), dec(c.get("q")), dec(c.get("g")));
			final int count = Integer.parseInt(args[4]);
			final List<String> cases = IntStream.range(0, count).parallel().mapToObj(i -> genCase(args[1], g, i)).toList();
			Files.writeString(new File(args[3]).toPath(), "[\n" + String.join(",\n", cases) + "\n]\n");
		}
		case "verify" -> {
			final List<JsonNode> cases = new ArrayList<>();
			mapper.readTree(new File(args[2])).forEach(cases::add);
			cases.parallelStream().map(t -> verify(args[1], t)).toList().forEach(System.out::println);
		}
		default -> throw new IllegalArgumentException("usage: gen KIND FIXTURE OUT COUNT | verify KIND FILE");
		}
	}
}
