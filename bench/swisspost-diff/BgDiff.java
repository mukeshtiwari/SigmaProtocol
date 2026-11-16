/*
 * Differential-testing driver for the Swiss Post Bayer–Groth shuffle argument
 * (crypto-primitives, Section 9 of the specification), compiled into the
 * crypto-primitives module (package internal.mixnet, whose prover and
 * verifier are package-private) by build.sh.
 *
 *   gen FIXTURE OUT M,N,L[,K] ...   honest shuffles (K >= L: size of the key) and arguments at the group of
 *                               the first case of FIXTURE, in the format of
 *                               verify-shuffle-argument.json; output.result is
 *                               the Swiss Post verdict, x, y, z its challenges
 *   genprod FIXTURE OUT MODE N,L[,K] ...   the same through the production MixnetService, under the
 *                               optimization mode MODE (COMPUTATION_OPTIMIZED: m = 1; MEMORY_OPTIMIZED:
 *                               m the largest divisor of N up to sqrt(N)), with the verifiable commitment key
 *   verify FILE                 one line per case: true, false, or error: msg
 *   verifyprod FILE             the same through MixnetService.verifyShuffle, which derives the commitment key
 *   dims MODE N ...             the dimensions m,n that MODE chooses for each N
 */
package ch.post.it.evoting.cryptoprimitives.internal.mixnet;

import java.io.File;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Base64;
import java.util.List;
import java.util.stream.Stream;

import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientCiphertext;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientKeyPair;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientPublicKey;
import ch.post.it.evoting.cryptoprimitives.hashing.HashableBigInteger;
import ch.post.it.evoting.cryptoprimitives.hashing.HashableString;
import ch.post.it.evoting.cryptoprimitives.internal.hashing.HashService;
import ch.post.it.evoting.cryptoprimitives.internal.math.RandomService;
import ch.post.it.evoting.cryptoprimitives.internal.utils.ConversionsInternal;
import ch.post.it.evoting.cryptoprimitives.math.GqElement;
import ch.post.it.evoting.cryptoprimitives.math.GqGroup;
import ch.post.it.evoting.cryptoprimitives.math.GroupVector;
import ch.post.it.evoting.cryptoprimitives.math.ZqElement;
import ch.post.it.evoting.cryptoprimitives.math.ZqGroup;
import ch.post.it.evoting.cryptoprimitives.mixnet.HadamardArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.MultiExponentiationArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.ProductArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.Shuffle;
import ch.post.it.evoting.cryptoprimitives.mixnet.ShuffleArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.ShuffleStatement;
import ch.post.it.evoting.cryptoprimitives.mixnet.ShuffleWitness;
import ch.post.it.evoting.cryptoprimitives.mixnet.SingleValueProductArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.VerifiableShuffle;
import ch.post.it.evoting.cryptoprimitives.mixnet.ZeroArgument;
import ch.post.it.evoting.cryptoprimitives.test.tools.serialization.JsonData;
import ch.post.it.evoting.cryptoprimitives.test.tools.serialization.TestParameters;

import tools.jackson.databind.DeserializationFeature;
import tools.jackson.databind.json.JsonMapper;

public final class BgDiff {

	private static final HashService hashService = HashService.getInstance();
	private static final RandomService randomService = new RandomService();

	private static List<TestParameters> load(final String file) {
		return List.of(JsonMapper.builder().disable(DeserializationFeature.FAIL_ON_TRAILING_TOKENS).build()
				.readValue(new File(file), TestParameters[].class));
	}

	// ---- JSON output: values are Base64 of BigInteger.toByteArray(), as in the fixtures ----

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
		return "[" + String.join(",", xs.toList()) + "]";
	}

	private static String ev(final GroupVector<GqElement, GqGroup> xs) {
		return arr(xs.stream().map(BgDiff::e));
	}

	private static String fv(final GroupVector<ZqElement, ZqGroup> xs) {
		return arr(xs.stream().map(BgDiff::f));
	}

	private static String ct(final ElGamalMultiRecipientCiphertext c) {
		return "{\"gamma\":" + e(c.getGamma()) + ",\"phis\":" + ev(c.getPhis()) + "}";
	}

	private static String cts(final GroupVector<ElGamalMultiRecipientCiphertext, GqGroup> cs) {
		return arr(cs.stream().map(BgDiff::ct));
	}

	private static String zero(final ZeroArgument z) {
		return "{\"c_a0\":" + e(z.get_c_A_0()) + ",\"c_bm\":" + e(z.get_c_B_m()) + ",\"c_d\":" + ev(z.get_c_d())
				+ ",\"a\":" + fv(z.get_a_prime()) + ",\"b\":" + fv(z.get_b_prime())
				+ ",\"r\":" + f(z.get_r_prime()) + ",\"s\":" + f(z.get_s_prime()) + ",\"t\":" + f(z.get_t_prime()) + "}";
	}

	private static String svpa(final SingleValueProductArgument s) {
		return "{\"c_d\":" + e(s.get_c_d()) + ",\"c_lower_delta\":" + e(s.get_c_delta()) + ",\"c_upper_delta\":" + e(s.get_c_Delta())
				+ ",\"a_tilde\":" + fv(s.get_a_tilde()) + ",\"b_tilde\":" + fv(s.get_b_tilde())
				+ ",\"r_tilde\":" + f(s.get_r_tilde()) + ",\"s_tilde\":" + f(s.get_s_tilde()) + "}";
	}

	private static String product(final ProductArgument p) {
		final StringBuilder sb = new StringBuilder("{");
		if (p.get_c_b().isPresent()) {
			final HadamardArgument h = p.getHadamardArgument().orElseThrow();
			sb.append("\"c_b\":").append(e(p.get_c_b().get()))
					.append(",\"hadamard_argument\":{\"cUpperB\":").append(ev(h.get_c_B()))
					.append(",\"zero_argument\":").append(zero(h.get_zeroArgument())).append("},");
		}
		return sb.append("\"single_vpa\":").append(svpa(p.getSingleValueProductArgument())).append("}").toString();
	}

	private static String mexp(final MultiExponentiationArgument a) {
		return "{\"c_a_0\":" + e(a.getc_A_0()) + ",\"c_b\":" + ev(a.get_c_B()) + ",\"a\":" + fv(a.get_a())
				+ ",\"e\":" + cts(a.get_E()) + ",\"r\":" + f(a.get_r()) + ",\"b\":" + f(a.get_b())
				+ ",\"s\":" + f(a.get_s()) + ",\"tau\":" + f(a.get_tau()) + "}";
	}

	// ---- gen ----

	private static ZqElement challenge(final GqGroup g, final ZqGroup zq, final Object... values) {
		final var hs = Stream.of(values).map(v -> (ch.post.it.evoting.cryptoprimitives.hashing.Hashable) v)
				.toArray(ch.post.it.evoting.cryptoprimitives.hashing.Hashable[]::new);
		return ZqElement.create(ConversionsInternal.byteArrayToInteger(hashService.recursiveHash(hs)), zq);
	}

	private static String genCase(final GqGroup group, final int m, final int n, final int l, final int k) {
		final ZqGroup zq = ZqGroup.sameOrderAs(group);
		final ElGamalMultiRecipientPublicKey pk = ElGamalMultiRecipientKeyPair.genKeyPair(group, k, randomService).getPublicKey();
		final CommitmentKey ck = new CommitmentKeyService(hashService).getVerifiableCommitmentKey(n, group);
		final GqElement gen = group.getGenerator();
		final GroupVector<ElGamalMultiRecipientCiphertext, GqGroup> C = Stream.generate(() -> ElGamalMultiRecipientCiphertext.create(
						gen.exponentiate(randomService.genRandomVector(group.getQ(), 1).get(0)),
						randomService.genRandomVector(group.getQ(), l).stream().map(gen::exponentiate).collect(GroupVector.toGroupVector())))
				.limit((long) m * n).collect(GroupVector.toGroupVector());
		final Shuffle shuffle = new ShuffleService(randomService, new PermutationService(randomService)).genShuffle(C, pk);
		final ShuffleStatement st = new ShuffleStatement(C, shuffle.getCiphertexts());
		final ShuffleWitness w = new ShuffleWitness(shuffle.getPermutation(), shuffle.getReEncryptionExponents());
		final ShuffleArgumentService service = new ShuffleArgumentService(pk, ck, randomService, hashService);
		final ShuffleArgument arg = service.getShuffleArgument(st, w, m, n);
		final boolean ok = service.verifyShuffleArgument(st, arg, m, n).isVerified();
		return caseJson("3072-bits, m=" + m + ", n=" + n + ", l=" + l + (k == l ? "" : ", k=" + k) + ", honest", group, pk, ck, st, arg, ok);
	}

	private static String caseJson(final String desc, final GqGroup group, final ElGamalMultiRecipientPublicKey pk, final CommitmentKey ck,
			final ShuffleStatement st, final ShuffleArgument arg, final boolean ok) {
		final ZqGroup zq = ZqGroup.sameOrderAs(group);
		final GqElement gen = group.getGenerator();
		final var C = st.get_C();
		final var P = HashableBigInteger.from(group.getP());
		final var Q = HashableBigInteger.from(group.getQ());
		final ZqElement x = challenge(group, zq, P, Q, pk, ck, C, st.get_C_prime(), arg.get_c_A());
		final ZqElement y = challenge(group, zq, arg.get_c_B(), P, Q, pk, ck, C, st.get_C_prime(), arg.get_c_A());
		final ZqElement z = challenge(group, zq, HashableString.from("1"), arg.get_c_B(), P, Q, pk, ck, C, st.get_C_prime(), arg.get_c_A());

		return "{\"description\":\"" + desc + "\""
				+ ",\"context\":{\"p\":" + b64(group.getP()) + ",\"q\":" + b64(group.getQ()) + ",\"g\":" + e(gen)
				+ ",\"pk\":" + ev(pk.stream().collect(GroupVector.toGroupVector()))
				+ ",\"ck\":{\"h\":" + e(ck.getH()) + ",\"g\":" + ev(ck.getG()) + "}}"
				+ ",\"input\":{\"statement\":{\"ciphertexts\":" + cts(C) + ",\"shuffled_ciphertexts\":" + cts(st.get_C_prime()) + "}"
				+ ",\"argument\":{\"ca\":" + ev(arg.get_c_A()) + ",\"cb\":" + ev(arg.get_c_B())
				+ ",\"product_argument\":" + product(arg.getProductArgument())
				+ ",\"multi_exp_argument\":" + mexp(arg.getMultiExponentiationArgument()) + "}}"
				+ ",\"output\":{\"result\":" + ok + ",\"x\":" + f(x) + ",\"y\":" + f(y) + ",\"z\":" + f(z) + "}}";
	}

	// ---- the production path: MixnetService, whose dimensions m, n depend on the optimization mode ----

	private static GroupVector<ElGamalMultiRecipientCiphertext, GqGroup> randomCiphertexts(final GqGroup group, final int N, final int l) {
		final GqElement gen = group.getGenerator();
		return Stream.generate(() -> ElGamalMultiRecipientCiphertext.create(
						gen.exponentiate(randomService.genRandomVector(group.getQ(), 1).get(0)),
						randomService.genRandomVector(group.getQ(), l).stream().map(gen::exponentiate).collect(GroupVector.toGroupVector())))
				.limit(N).collect(GroupVector.toGroupVector());
	}

	/**
	 * A shuffle by MixnetService.genVerifiableShuffle under the given optimization mode, with the verifiable commitment key of the
	 * production verifier in the context; output.result is the verdict of MixnetService.verifyShuffle, which must agree with
	 * ShuffleArgumentService.verifyShuffleArgument on the same key (else the run stops).
	 */
	private static String genProd(final GqGroup group, final String mode, final int N, final int l, final int k) {
		System.setProperty("MIXNET_OPTIMIZATION_MODE", mode);
		final int[] dims = MatrixUtils.getMatrixDimensions(N);
		final int m = dims[0], n = dims[1];
		final ElGamalMultiRecipientPublicKey pk = ElGamalMultiRecipientKeyPair.genKeyPair(group, k, randomService).getPublicKey();
		final var C = randomCiphertexts(group, N, l);
		final MixnetService mixnet = new MixnetService();
		final VerifiableShuffle vs = mixnet.genVerifiableShuffle(C, pk);
		final boolean prod = mixnet.verifyShuffle(C, vs.shuffledCiphertexts(), vs.shuffleArgument(), pk).isVerified();
		final CommitmentKey ck = new CommitmentKeyService(hashService).getVerifiableCommitmentKey(n, group);
		final ShuffleStatement st = new ShuffleStatement(C, vs.shuffledCiphertexts());
		final boolean internal = new ShuffleArgumentService(pk, ck, randomService, hashService)
				.verifyShuffleArgument(st, vs.shuffleArgument(), m, n).isVerified();
		if (prod != internal || vs.shuffleArgument().get_m() != m)
			throw new IllegalStateException("production and ShuffleArgumentService verdicts differ: " + prod + " " + internal);
		return caseJson("3072-bits, m=" + m + ", n=" + n + ", l=" + l + (k == l ? "" : ", k=" + k) + ", production " + mode + ", honest",
				group, pk, ck, st, vs.shuffleArgument(), prod);
	}

	/** MixnetService.verifyShuffle, which derives m, n (m = 1: COMPUTATION_OPTIMIZED) and the commitment key itself */
	private static String verifyProd(final TestParameters t) {
		try {
			final TestContextParser context = new TestContextParser(t.getContext());
			final GqGroup group = context.getGqGroup();
			final JsonData stData = t.getInput().getJsonData("statement");
			final var C = TestParser.parseCiphertexts(stData.getJsonData("ciphertexts"), group);
			final var C_prime = TestParser.parseCiphertexts(stData.getJsonData("shuffled_ciphertexts"), group);
			final ShuffleArgument arg = parseArgument(t.getInput().getJsonData("argument"), group);
			System.setProperty("MIXNET_OPTIMIZATION_MODE", arg.get_m() == 1 ? "COMPUTATION_OPTIMIZED" : "MEMORY_OPTIMIZED");
			return Boolean.toString(new MixnetService().verifyShuffle(C, C_prime, arg, context.parsePublicKey()).isVerified());
		} catch (final RuntimeException ex) {
			return "error: " + ex.getClass().getSimpleName() + ": " + String.valueOf(ex.getMessage()).replace('\n', ' ');
		}
	}

	private static ShuffleArgument parseArgument(final JsonData a, final GqGroup group) {
		final TestArgumentParser parser = new TestArgumentParser(group);
		return new ShuffleArgument.Builder()
				.with_c_A(TestParser.parseCommitment(a, "ca", group))
				.with_c_B(TestParser.parseCommitment(a, "cb", group))
				.with_productArgument(parser.parseProductArgument(a.getJsonData("product_argument")))
				.with_multiExponentiationArgument(parser.parseMultiExponentiationArgument(a.getJsonData("multi_exp_argument")))
				.build();
	}

	// ---- verify (as ShuffleArgumentServiceTest.jsonData) ----

	private static String verify(final TestParameters t) {
		try {
			final TestContextParser context = new TestContextParser(t.getContext());
			final GqGroup group = context.getGqGroup();
			final JsonData stData = t.getInput().getJsonData("statement");
			final ShuffleStatement st = new ShuffleStatement(TestParser.parseCiphertexts(stData.getJsonData("ciphertexts"), group),
					TestParser.parseCiphertexts(stData.getJsonData("shuffled_ciphertexts"), group));
			final JsonData a = t.getInput().getJsonData("argument");
			final TestArgumentParser parser = new TestArgumentParser(group);
			final ShuffleArgument arg = new ShuffleArgument.Builder()
					.with_c_A(TestParser.parseCommitment(a, "ca", group))
					.with_c_B(TestParser.parseCommitment(a, "cb", group))
					.with_productArgument(parser.parseProductArgument(a.getJsonData("product_argument")))
					.with_multiExponentiationArgument(parser.parseMultiExponentiationArgument(a.getJsonData("multi_exp_argument")))
					.build();
			final int m = arg.get_m();
			final int n = st.get_N() / m;
			return Boolean.toString(new ShuffleArgumentService(context.parsePublicKey(), context.parseCommitmentKey(), randomService, hashService)
					.verifyShuffleArgument(st, arg, m, n).isVerified());
		} catch (final RuntimeException ex) {
			return "error: " + ex.getClass().getSimpleName() + ": " + String.valueOf(ex.getMessage()).replace('\n', ' ');
		}
	}

	public static void main(final String[] args) throws IOException {
		switch (args[0]) {
		case "gen" -> {
			final GqGroup group = new TestContextParser(load(args[1]).getFirst().getContext()).getGqGroup();
			final List<String> cases = new ArrayList<>();
			for (int i = 3; i < args.length; i++) {
				final String[] d = args[i].split(",");
				final int l = Integer.parseInt(d[2]);
				cases.add(genCase(group, Integer.parseInt(d[0]), Integer.parseInt(d[1]), l, d.length > 3 ? Integer.parseInt(d[3]) : l));
				System.err.println("generated " + args[i]);
			}
			Files.writeString(new File(args[2]).toPath(), "[\n" + String.join(",\n", cases) + "\n]\n");
		}
		case "genprod" -> {
			final GqGroup group = new TestContextParser(load(args[1]).getFirst().getContext()).getGqGroup();
			final List<String> cases = new ArrayList<>();
			for (int i = 4; i < args.length; i++) {
				final String[] d = args[i].split(",");
				final int l = Integer.parseInt(d[1]);
				cases.add(genProd(group, args[3], Integer.parseInt(d[0]), l, d.length > 2 ? Integer.parseInt(d[2]) : l));
				System.err.println("generated " + args[3] + " " + args[i]);
			}
			Files.writeString(new File(args[2]).toPath(), "[\n" + String.join(",\n", cases) + "\n]\n");
		}
		case "verify" -> load(args[1]).stream().parallel().map(BgDiff::verify).toList().forEach(System.out::println);
		// sequential: the optimization mode is a system property
		case "verifyprod" -> load(args[1]).stream().map(BgDiff::verifyProd).forEach(System.out::println);
		case "dims" -> {   // m,n of each N under the given mode
			System.setProperty("MIXNET_OPTIMIZATION_MODE", args[1]);
			for (int i = 2; i < args.length; i++) {
				final int[] d = MatrixUtils.getMatrixDimensions(Integer.parseInt(args[i]));
				System.out.println(d[0] + "," + d[1]);
			}
		}
		default -> throw new IllegalArgumentException(
				"usage: gen FIXTURE OUT M,N,L[,K] ... | genprod FIXTURE OUT MODE N,L[,K] ... | verify FILE | verifyprod FILE | dims MODE N ...");
		}
	}
}
