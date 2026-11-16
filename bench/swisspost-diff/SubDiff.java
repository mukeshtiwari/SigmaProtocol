/*
 * The Swiss Post verifiers of the sub-arguments of the shuffle argument
 * (Algorithms 9.16, 9.19, 9.21, 9.23, 9.26), on files in the format of the
 * library's verify-*-argument.json test vectors; parsed as in its own tests.
 *
 *   SubDiff KIND FILE    KIND = zero | svp | hadamard | product | multiexp;
 *                        one line per case: true, false<TAB>messages, or error: msg
 */
package ch.post.it.evoting.cryptoprimitives.internal.mixnet;

import java.io.File;
import java.math.BigInteger;
import java.util.List;

import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientPublicKey;
import ch.post.it.evoting.cryptoprimitives.internal.hashing.HashService;
import ch.post.it.evoting.cryptoprimitives.internal.math.RandomService;
import ch.post.it.evoting.cryptoprimitives.internal.utils.Verifiable;
import ch.post.it.evoting.cryptoprimitives.math.GqElement;
import ch.post.it.evoting.cryptoprimitives.math.GqGroup;
import ch.post.it.evoting.cryptoprimitives.math.ZqElement;
import ch.post.it.evoting.cryptoprimitives.math.ZqGroup;
import ch.post.it.evoting.cryptoprimitives.mixnet.HadamardStatement;
import ch.post.it.evoting.cryptoprimitives.mixnet.MultiExponentiationStatement;
import ch.post.it.evoting.cryptoprimitives.mixnet.ProductStatement;
import ch.post.it.evoting.cryptoprimitives.mixnet.SingleValueProductStatement;
import ch.post.it.evoting.cryptoprimitives.mixnet.ZeroStatement;
import ch.post.it.evoting.cryptoprimitives.test.tools.serialization.JsonData;
import ch.post.it.evoting.cryptoprimitives.test.tools.serialization.TestParameters;
import ch.post.it.evoting.cryptoprimitives.utils.VerificationResult;

import tools.jackson.databind.DeserializationFeature;
import tools.jackson.databind.json.JsonMapper;

public final class SubDiff {

	private static final HashService hashService = HashService.getInstance();
	private static final RandomService randomService = new RandomService();

	private static String verify(final String kind, final TestParameters t) {
		try {
			final TestContextParser context = new TestContextParser(t.getContext());
			final GqGroup group = context.getGqGroup();
			final ZqGroup zq = ZqGroup.sameOrderAs(group);
			final ElGamalMultiRecipientPublicKey pk = context.parsePublicKey();
			final CommitmentKey ck = context.parseCommitmentKey();
			final TestArgumentParser parser = new TestArgumentParser(group);
			final JsonData st = t.getInput().getJsonData("statement");
			final JsonData arg = t.getInput().getJsonData("argument");
			final Verifiable v = switch (kind) {
				case "zero" -> new ZeroArgumentService(pk, ck, randomService, hashService).verifyZeroArgument(
						new ZeroStatement(TestParser.parseCommitment(st, "c_a", group), TestParser.parseCommitment(st, "c_b", group),
								ZqElement.create(st.get("y", BigInteger.class), zq)),
						parser.parseZeroArgument(arg));
				case "svp" -> new SingleValueProductArgumentService(randomService, hashService, pk, ck).verifySingleValueProductArgument(
						new SingleValueProductStatement(GqElement.GqElementFactory.fromValue(st.get("c_a", BigInteger.class), group),
								ZqElement.create(st.get("b", BigInteger.class), zq)),
						parser.parseSingleValueProductArgument(arg));
				case "hadamard" -> new HadamardArgumentService(randomService, hashService, pk, ck).verifyHadamardArgument(
						new HadamardStatement(TestParser.parseCommitment(st, "c_a", group),
								GqElement.GqElementFactory.fromValue(st.get("c_b", BigInteger.class), group)),
						parser.parseHadamardArgument(arg));
				case "product" -> new ProductArgumentService(randomService, hashService, pk, ck).verifyProductArgument(
						new ProductStatement(TestParser.parseCommitment(st, "c_a", group), ZqElement.create(st.get("b", BigInteger.class), zq)),
						parser.parseProductArgument(arg));
				case "multiexp" -> new MultiExponentiationArgumentService(pk, ck, randomService, hashService).verifyMultiExponentiationArgument(
						new MultiExponentiationStatement(parser.parseCiphertextMatrix(st.getJsonData("ciphertexts")),
								parser.parseCiphertext(st.getJsonData("ciphertext_product")), TestParser.parseCommitment(st, "c_a", group)),
						parser.parseMultiExponentiationArgument(arg));
				default -> throw new IllegalArgumentException("unknown kind " + kind);
			};
			final VerificationResult r = v.verify();
			return r.isVerified() ? "true" : "false\t" + String.join(" | ", r.getErrorMessages());
		} catch (final RuntimeException ex) {
			return "error: " + ex.getClass().getSimpleName() + ": " + String.valueOf(ex.getMessage()).replace('\n', ' ');
		}
	}

	public static void main(final String[] args) {
		final List<TestParameters> cases = List.of(JsonMapper.builder().disable(DeserializationFeature.FAIL_ON_TRAILING_TOKENS).build()
				.readValue(new File(args[1]), TestParameters[].class));
		cases.stream().parallel().map(t -> verify(args[0], t)).toList().forEach(System.out::println);
	}
}
