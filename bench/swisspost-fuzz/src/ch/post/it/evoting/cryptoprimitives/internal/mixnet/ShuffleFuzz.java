/*
 * The Bayer–Groth verifiers of the library on mutated honest arguments: the
 * shuffle argument through the production entry point
 * MixnetService.verifyShuffle (in both optimization modes, so with and without
 * the Hadamard argument), and the product and multi-exponentiation arguments
 * directly. Honest statements and arguments are generated once by the
 * library's provers at a 1024-bit group (SECURITY_LEVEL=TESTING_ONLY, for
 * speed; nothing in the verifiers depends on the size of p). Each input picks
 * a case and applies one to four mutations to its fields (values: random,
 * times g / +1, identity / 0, out-of-range raw values, inverse / negation,
 * copied from elsewhere; vectors: removed, duplicated or swapped entries;
 * ciphertexts: one more or one fewer component).
 *
 * Expected: the verifier rejects, or a constructor or the verifier refuses
 * with IllegalArgumentException / NullPointerException (Preconditions).
 * Findings: an accepted argument that differs from the honest one, and every
 * other exception.
 */
package ch.post.it.evoting.cryptoprimitives.internal.mixnet;

import static ch.post.it.evoting.cryptoprimitives.math.GroupVector.toGroupVector;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import com.code_intelligence.jazzer.api.FuzzedDataProvider;
import com.code_intelligence.jazzer.api.FuzzerSecurityIssueCritical;

import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientCiphertext;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientKeyPair;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientPublicKey;
import ch.post.it.evoting.cryptoprimitives.fuzz.Spec;
import ch.post.it.evoting.cryptoprimitives.internal.hashing.HashService;
import ch.post.it.evoting.cryptoprimitives.internal.math.RandomService;
import ch.post.it.evoting.cryptoprimitives.internal.securitylevel.SecurityLevelConfig;
import ch.post.it.evoting.cryptoprimitives.internal.securitylevel.SecurityLevelInternal;
import ch.post.it.evoting.cryptoprimitives.math.GqElement;
import ch.post.it.evoting.cryptoprimitives.math.GqElement.GqElementFactory;
import ch.post.it.evoting.cryptoprimitives.math.GqGroup;
import ch.post.it.evoting.cryptoprimitives.math.GroupMatrix;
import ch.post.it.evoting.cryptoprimitives.math.GroupVector;
import ch.post.it.evoting.cryptoprimitives.math.ZqElement;
import ch.post.it.evoting.cryptoprimitives.math.ZqGroup;
import ch.post.it.evoting.cryptoprimitives.mixnet.HadamardArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.MultiExponentiationArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.MultiExponentiationStatement;
import ch.post.it.evoting.cryptoprimitives.mixnet.MultiExponentiationWitness;
import ch.post.it.evoting.cryptoprimitives.mixnet.ProductArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.ProductStatement;
import ch.post.it.evoting.cryptoprimitives.mixnet.ProductWitness;
import ch.post.it.evoting.cryptoprimitives.mixnet.ShuffleArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.SingleValueProductArgument;
import ch.post.it.evoting.cryptoprimitives.mixnet.VerifiableShuffle;
import ch.post.it.evoting.cryptoprimitives.mixnet.ZeroArgument;

public final class ShuffleFuzz {

	// ---- a case: named fields, each a list of items (an item: one value, or the components of a ciphertext) ----

	private enum Kind {G, Z, CT}

	private record Field(Kind kind, boolean list, List<BigInteger[]> items) {
		Field copy() {
			return new Field(kind, list, new ArrayList<>(items.stream().map(BigInteger[]::clone).toList()));
		}

		boolean same(final Field o) {
			if (items.size() != o.items.size()) {
				return false;
			}
			for (int i = 0; i < items.size(); i++) {
				if (!Arrays.equals(items.get(i), o.items.get(i))) {
					return false;
				}
			}
			return true;
		}
	}

	private record Case(String type, String mode, int m, int n, Map<String, Field> fields) {
		String describe() {
			return type + " m=" + m + " n=" + n + (mode == null ? "" : " " + mode);
		}
	}

	private static GqGroup group;
	private static ZqGroup zq;
	private static BigInteger p;
	private static BigInteger q;
	private static final RandomService random = new RandomService();
	private static final HashService hash = HashService.getInstance();
	private static final MixnetService mixnet = new MixnetService();
	private static final Map<Integer, CommitmentKey> keys = new HashMap<>();
	private static final List<Case> cases = new ArrayList<>();
	private static final java.util.Set<String> emptyVectorSites = new java.util.HashSet<>();

	private static CommitmentKey ck(final int n) {
		return keys.computeIfAbsent(n, k -> new CommitmentKeyService(hash).getVerifiableCommitmentKey(k, group));
	}

	// ---- fields from objects ----

	private static BigInteger[] one(final BigInteger x) {
		return new BigInteger[] { x };
	}

	private static Field g1(final GqElement x) {
		return new Field(Kind.G, false, new ArrayList<>(List.<BigInteger[]>of(one(x.getValue()))));
	}

	private static Field z1(final ZqElement x) {
		return new Field(Kind.Z, false, new ArrayList<>(List.<BigInteger[]>of(one(x.getValue()))));
	}

	private static Field gs(final GroupVector<GqElement, GqGroup> xs) {
		return new Field(Kind.G, true, new ArrayList<>(xs.stream().map(x -> one(x.getValue())).toList()));
	}

	private static Field zs(final GroupVector<ZqElement, ZqGroup> xs) {
		return new Field(Kind.Z, true, new ArrayList<>(xs.stream().map(x -> one(x.getValue())).toList()));
	}

	private static BigInteger[] ct(final ElGamalMultiRecipientCiphertext c) {
		return Stream.concat(Stream.of(c.getGamma()), c.getPhis().stream()).map(GqElement::getValue).toArray(BigInteger[]::new);
	}

	private static Field cts(final Stream<ElGamalMultiRecipientCiphertext> cs, final boolean list) {
		return new Field(Kind.CT, list, new ArrayList<>(cs.map(ShuffleFuzz::ct).toList()));
	}

	private static void zero(final Map<String, Field> f, final String pre, final ZeroArgument z) {
		f.put(pre + "c_A_0", g1(z.get_c_A_0()));
		f.put(pre + "c_B_m", g1(z.get_c_B_m()));
		f.put(pre + "c_d", gs(z.get_c_d()));
		f.put(pre + "a'", zs(z.get_a_prime()));
		f.put(pre + "b'", zs(z.get_b_prime()));
		f.put(pre + "r'", z1(z.get_r_prime()));
		f.put(pre + "s'", z1(z.get_s_prime()));
		f.put(pre + "t'", z1(z.get_t_prime()));
	}

	private static void svp(final Map<String, Field> f, final String pre, final SingleValueProductArgument s) {
		f.put(pre + "c_d", g1(s.get_c_d()));
		f.put(pre + "c_delta", g1(s.get_c_delta()));
		f.put(pre + "c_Delta", g1(s.get_c_Delta()));
		f.put(pre + "a~", zs(s.get_a_tilde()));
		f.put(pre + "b~", zs(s.get_b_tilde()));
		f.put(pre + "r~", z1(s.get_r_tilde()));
		f.put(pre + "s~", z1(s.get_s_tilde()));
	}

	private static void product(final Map<String, Field> f, final ProductArgument a) {
		if (a.get_c_b().isPresent()) {
			f.put("prod.c_b", g1(a.get_c_b().get()));
			final HadamardArgument h = a.getHadamardArgument().orElseThrow();
			f.put("prod.had.c_B", gs(h.get_c_B()));
			zero(f, "prod.had.zero.", h.get_zeroArgument());
		}
		svp(f, "prod.svp.", a.getSingleValueProductArgument());
	}

	private static void mexp(final Map<String, Field> f, final MultiExponentiationArgument a) {
		f.put("mexp.c_A_0", g1(a.getc_A_0()));
		f.put("mexp.c_B", gs(a.get_c_B()));
		f.put("mexp.E", cts(a.get_E().stream(), true));
		f.put("mexp.a", zs(a.get_a()));
		f.put("mexp.r", z1(a.get_r()));
		f.put("mexp.b", z1(a.get_b()));
		f.put("mexp.s", z1(a.get_s()));
		f.put("mexp.tau", z1(a.get_tau()));
	}

	// ---- objects from fields (constructors check membership, ranges and dimensions) ----

	private static GqElement ge(final BigInteger x) {
		return GqElementFactory.fromValue(x, group);
	}

	private static ZqElement ze(final BigInteger x) {
		return ZqElement.create(x, zq);
	}

	private static GqElement G1(final Map<String, Field> f, final String k) {
		return ge(f.get(k).items().getFirst()[0]);
	}

	private static ZqElement Z1(final Map<String, Field> f, final String k) {
		return ze(f.get(k).items().getFirst()[0]);
	}

	private static GroupVector<GqElement, GqGroup> Gs(final Map<String, Field> f, final String k) {
		return f.get(k).items().stream().map(x -> ge(x[0])).collect(toGroupVector());
	}

	private static GroupVector<ZqElement, ZqGroup> Zs(final Map<String, Field> f, final String k) {
		return f.get(k).items().stream().map(x -> ze(x[0])).collect(toGroupVector());
	}

	private static ElGamalMultiRecipientCiphertext CT(final BigInteger[] c) {
		return ElGamalMultiRecipientCiphertext.create(ge(c[0]), Arrays.stream(c).skip(1).map(ShuffleFuzz::ge).collect(toGroupVector()));
	}

	private static GroupVector<ElGamalMultiRecipientCiphertext, GqGroup> CTs(final Map<String, Field> f, final String k) {
		return f.get(k).items().stream().map(ShuffleFuzz::CT).collect(toGroupVector());
	}

	private static ElGamalMultiRecipientPublicKey PK(final Map<String, Field> f) {
		return new ElGamalMultiRecipientPublicKey(Gs(f, "pk"));
	}

	private static ZeroArgument Zero(final Map<String, Field> f, final String pre) {
		return new ZeroArgument.Builder().with_c_A_0(G1(f, pre + "c_A_0")).with_c_B_m(G1(f, pre + "c_B_m")).with_c_d(Gs(f, pre + "c_d"))
				.with_a_prime(Zs(f, pre + "a'")).with_b_prime(Zs(f, pre + "b'"))
				.with_r_prime(Z1(f, pre + "r'")).with_s_prime(Z1(f, pre + "s'")).with_t_prime(Z1(f, pre + "t'")).build();
	}

	private static SingleValueProductArgument Svp(final Map<String, Field> f, final String pre) {
		return new SingleValueProductArgument.Builder().with_c_d(G1(f, pre + "c_d")).with_c_delta(G1(f, pre + "c_delta"))
				.with_c_Delta(G1(f, pre + "c_Delta")).with_a_tilde(Zs(f, pre + "a~")).with_b_tilde(Zs(f, pre + "b~"))
				.with_r_tilde(Z1(f, pre + "r~")).with_s_tilde(Z1(f, pre + "s~")).build();
	}

	private static ProductArgument Product(final Map<String, Field> f) {
		if (f.containsKey("prod.c_b")) {
			return new ProductArgument(G1(f, "prod.c_b"), new HadamardArgument(Gs(f, "prod.had.c_B"), Zero(f, "prod.had.zero.")),
					Svp(f, "prod.svp."));
		}
		return new ProductArgument(Svp(f, "prod.svp."));
	}

	private static MultiExponentiationArgument Mexp(final Map<String, Field> f) {
		return new MultiExponentiationArgument.Builder().with_c_A_0(G1(f, "mexp.c_A_0")).with_c_B(Gs(f, "mexp.c_B"))
				.with_E(CTs(f, "mexp.E")).with_a(Zs(f, "mexp.a"))
				.with_r(Z1(f, "mexp.r")).with_b(Z1(f, "mexp.b")).with_s(Z1(f, "mexp.s")).with_tau(Z1(f, "mexp.tau")).build();
	}

	/** the m × n matrix of a list of ciphertexts, by rows of n (a shorter last row when the list was resized) */
	private static GroupMatrix<ElGamalMultiRecipientCiphertext, GqGroup> matrix(final GroupVector<ElGamalMultiRecipientCiphertext, GqGroup> cs,
			final int n) {
		final List<GroupVector<ElGamalMultiRecipientCiphertext, GqGroup>> rows = new ArrayList<>();
		for (int i = 0; i < cs.size(); i += n) {
			rows.add(cs.subVector(i, Math.min(i + n, cs.size())));
		}
		return GroupMatrix.fromRows(GroupVector.from(rows));
	}

	private static boolean verify(final Case c, final Map<String, Field> f) {
		switch (c.type()) {
		case "shuffle" -> {
			System.setProperty("MIXNET_OPTIMIZATION_MODE", c.mode());
			final ShuffleArgument arg = new ShuffleArgument.Builder().with_c_A(Gs(f, "c_A")).with_c_B(Gs(f, "c_B"))
					.with_productArgument(Product(f)).with_multiExponentiationArgument(Mexp(f)).build();
			return mixnet.verifyShuffle(CTs(f, "C"), CTs(f, "C'"), arg, PK(f)).isVerified();
		}
		case "product" -> {
			return new ProductArgumentService(random, hash, PK(f), ck(c.n()))
					.verifyProductArgument(new ProductStatement(Gs(f, "st.c_A"), Z1(f, "st.b")), Product(f)).verify().isVerified();
		}
		default -> {
			final GroupVector<ElGamalMultiRecipientCiphertext, GqGroup> cc = CTs(f, "st.C");
			if (cc.size() != 1) {
				throw new IllegalArgumentException("C is one ciphertext");   // the harness' own shape check
			}
			return new MultiExponentiationArgumentService(PK(f), ck(c.n()), random, hash)
					.verifyMultiExponentiationArgument(new MultiExponentiationStatement(matrix(CTs(f, "st.Cs"), c.n()), cc.getFirst(), Gs(f, "st.c_A")),
							Mexp(f)).verify().isVerified();
		}
		}
	}

	// ---- honest cases ----

	private static ElGamalMultiRecipientCiphertext randomCiphertext(final int l) {
		final GqElement g = group.getGenerator();
		return ElGamalMultiRecipientCiphertext.create(g.exponentiate(random.genRandomVector(q, 1).getFirst()),
				random.genRandomVector(q, l).stream().map(g::exponentiate).collect(toGroupVector()));
	}

	private static GroupMatrix<ZqElement, ZqGroup> randomMatrix(final int rows, final int columns) {
		return GroupMatrix.fromRows(Stream.generate(() -> random.genRandomVector(q, columns)).limit(rows).collect(toGroupVector()));
	}

	private static void addShuffle(final ElGamalMultiRecipientPublicKey pk, final int N, final int l, final String mode) {
		System.setProperty("MIXNET_OPTIMIZATION_MODE", mode);
		final GroupVector<ElGamalMultiRecipientCiphertext, GqGroup> C = Stream.generate(() -> randomCiphertext(l)).limit(N).collect(toGroupVector());
		final VerifiableShuffle vs = mixnet.genVerifiableShuffle(C, pk);
		final ShuffleArgument a = vs.shuffleArgument();
		final Map<String, Field> f = new LinkedHashMap<>();
		f.put("pk", gs(pk.stream().collect(toGroupVector())));
		f.put("C", cts(C.stream(), true));
		f.put("C'", cts(vs.shuffledCiphertexts().stream(), true));
		f.put("c_A", gs(a.get_c_A()));
		f.put("c_B", gs(a.get_c_B()));
		product(f, a.getProductArgument());
		mexp(f, a.getMultiExponentiationArgument());
		cases.add(new Case("shuffle", mode, a.get_m(), a.get_n(), f));
	}

	private static void addProduct(final ElGamalMultiRecipientPublicKey pk, final int n, final int m) {
		final GroupMatrix<ZqElement, ZqGroup> A = randomMatrix(n, m);
		final GroupVector<ZqElement, ZqGroup> r = random.genRandomVector(q, m);
		final GroupVector<GqElement, GqGroup> cA = CommitmentService.getCommitmentMatrix(A, r, ck(n));
		final ZqElement b = A.flatStream().reduce(ZqElement.create(1, zq), ZqElement::multiply);
		final ProductArgument a = new ProductArgumentService(random, hash, pk, ck(n)).getProductArgument(new ProductStatement(cA, b),
				new ProductWitness(A, r));
		final Map<String, Field> f = new LinkedHashMap<>();
		f.put("pk", gs(pk.stream().collect(toGroupVector())));
		f.put("st.c_A", gs(cA));
		f.put("st.b", z1(b));
		product(f, a);
		cases.add(new Case("product", null, m, n, f));
	}

	private static void addMexp(final ElGamalMultiRecipientPublicKey pk, final int m, final int n, final int l) {
		final GroupMatrix<ElGamalMultiRecipientCiphertext, GqGroup> Cs = GroupMatrix.fromRows(
				Stream.generate(() -> Stream.generate(() -> randomCiphertext(l)).limit(n).collect(toGroupVector())).limit(m).collect(toGroupVector()));
		final GroupMatrix<ZqElement, ZqGroup> A = randomMatrix(n, m);
		final GroupVector<ZqElement, ZqGroup> r = random.genRandomVector(q, m);
		final ZqElement rho = random.genRandomVector(q, 1).getFirst();
		final GroupVector<GqElement, GqGroup> cA = CommitmentService.getCommitmentMatrix(A, r, ck(n));
		final MultiExponentiationArgumentService service = new MultiExponentiationArgumentService(pk, ck(n), random, hash);
		final ElGamalMultiRecipientCiphertext C = service.multiExponentiation(Cs, A, rho, l);
		final MultiExponentiationArgument a = service.getMultiExponentiationArgument(new MultiExponentiationStatement(Cs, C, cA),
				new MultiExponentiationWitness(A, r, rho));
		final Map<String, Field> f = new LinkedHashMap<>();
		f.put("pk", gs(pk.stream().collect(toGroupVector())));
		f.put("st.Cs", cts(Cs.flatStream(), true));
		f.put("st.C", cts(Stream.of(C), false));
		f.put("st.c_A", gs(cA));
		mexp(f, a);
		cases.add(new Case("mexp", null, m, n, f));
	}

	public static void fuzzerInitialize() {
		if (SecurityLevelConfig.getSystemSecurityLevel() != SecurityLevelInternal.TESTING_ONLY) {
			throw new IllegalStateException("run with SECURITY_LEVEL=TESTING_ONLY (the 1024-bit group)");
		}
		p = Spec.P1024;
		q = p.subtract(BigInteger.ONE).shiftRight(1);
		group = new GqGroup(p, q, BigInteger.TWO);
		zq = ZqGroup.sameOrderAs(group);
		final ElGamalMultiRecipientPublicKey pk = ElGamalMultiRecipientKeyPair.genKeyPair(group, 2, random).getPublicKey();
		addShuffle(pk, 2, 1, "COMPUTATION_OPTIMIZED");
		addShuffle(pk, 3, 2, "COMPUTATION_OPTIMIZED");
		addShuffle(pk, 4, 2, "MEMORY_OPTIMIZED");
		addShuffle(pk, 6, 1, "MEMORY_OPTIMIZED");
		addShuffle(pk, 9, 2, "MEMORY_OPTIMIZED");
		addProduct(pk, 2, 1);
		addProduct(pk, 3, 1);
		addProduct(pk, 2, 2);
		addProduct(pk, 3, 2);
		addProduct(pk, 2, 3);
		addMexp(pk, 1, 2, 1);
		addMexp(pk, 2, 2, 2);
		addMexp(pk, 3, 2, 1);
		addMexp(pk, 2, 3, 2);
		for (final Case c : cases) {
			if (!verify(c, c.fields())) {
				throw new IllegalStateException("honest case rejected: " + c.describe());
			}
			System.err.println("honest case accepted: " + c.describe() + ", " + c.fields().size() + " fields");
		}
	}

	// ---- mutations ----

	private static BigInteger special(final FuzzedDataProvider d) {
		return switch (d.consumeInt(0, 9)) {
			case 0 -> BigInteger.ZERO;
			case 1 -> BigInteger.ONE;
			case 2 -> p.subtract(BigInteger.ONE);
			case 3 -> p;
			case 4 -> q;
			case 5 -> q.subtract(BigInteger.ONE);
			case 6 -> q.add(BigInteger.ONE);
			case 7 -> p.add(BigInteger.ONE);
			case 8 -> BigInteger.ONE.negate();
			default -> BigInteger.ONE.shiftLeft(p.bitLength());
		};
	}

	public static void fuzzerTestOneInput(final FuzzedDataProvider d) {
		final Case c = cases.get(d.consumeInt(0, cases.size() - 1));
		final Map<String, Field> f = new LinkedHashMap<>();
		c.fields().forEach((k, v) -> f.put(k, v.copy()));
		final List<String> names = List.copyOf(f.keySet());
		final StringBuilder log = new StringBuilder();
		final int ops = d.consumeInt(1, 4);
		for (int o = 0; o < ops; o++) {
			final String name = names.get(d.consumeInt(0, names.size() - 1));
			final Field F = f.get(name);
			final int op = d.consumeInt(0, 9);
			if (F.items().isEmpty()) {
				if (op == 7) {
					F.items().add(one(BigInteger.ONE));
				}
				continue;
			}
			final int i = d.consumeInt(0, F.items().size() - 1);
			final BigInteger[] item = F.items().get(i);
			final int j = d.consumeInt(0, item.length - 1);
			final BigInteger x = item[j];
			final boolean grp = F.kind() != Kind.Z;
			log.append(String.format("%s[%d][%d] op %d; ", name, i, j, op));
			switch (op) {
			case 0 -> {
				final BigInteger k = BigInteger.valueOf(d.consumeLong()).mod(q);
				item[j] = grp ? BigInteger.TWO.modPow(k, p) : k;
			}
			case 1 -> item[j] = grp ? x.shiftLeft(1).mod(p) : x.add(BigInteger.ONE).mod(q);
			case 2 -> item[j] = grp ? BigInteger.ONE : BigInteger.ZERO;
			case 3 -> item[j] = special(d);
			case 4 -> item[j] = grp ? (x.mod(p).signum() == 0 ? BigInteger.ONE : x.modInverse(p)) : x.negate().mod(q);
			case 5 -> {
				final Field S = f.get(names.get(d.consumeInt(0, names.size() - 1)));
				if (!S.items().isEmpty() && (S.kind() != Kind.Z) == grp) {
					final BigInteger[] si = S.items().get(d.consumeInt(0, S.items().size() - 1));
					item[j] = si[d.consumeInt(0, si.length - 1)];
				}
			}
			case 6 -> {
				if (F.list()) {
					F.items().remove(i);
				}
			}
			case 7 -> {
				if (F.list()) {
					F.items().add(i, item.clone());
				}
			}
			case 8 -> {
				final int i2 = d.consumeInt(0, F.items().size() - 1);
				F.items().set(i, F.items().get(i2));
				F.items().set(i2, item);
			}
			default -> {
				if (F.kind() == Kind.CT) {
					if (d.consumeBoolean()) {
						if (item.length > 1) {
							F.items().set(i, Arrays.copyOf(item, item.length - 1));
						}
					} else {
						final BigInteger[] longer = Arrays.copyOf(item, item.length + 1);
						longer[item.length] = BigInteger.TWO;
						F.items().set(i, longer);
					}
				}
			}
			}
		}
		if (f.entrySet().stream().allMatch(e -> e.getValue().same(c.fields().get(e.getKey())))) {
			return;   // a mutation that changed nothing
		}
		final boolean accepted;
		try {
			accepted = verify(c, f);
		} catch (final IllegalArgumentException | NullPointerException _) {
			return;
		} catch (final IllegalStateException e) {
			// finding 1 (README): constructors call GroupVector.getGroup() on a vector that may be empty, which throws
			// IllegalStateException (wrapped in another one when it happens in a parallel stream) instead of the
			// IllegalArgumentException of their checks; logged once per call site
			boolean emptyVector = false;
			for (Throwable t = e; t != null; t = t.getCause()) {
				emptyVector |= t instanceof IllegalStateException && "An empty GroupVector does not have a group.".equals(t.getMessage());
			}
			if (!emptyVector) {
				throw e;
			}
			final StackTraceElement site = Arrays.stream(e.getStackTrace())
					.filter(s -> s.getClassName().startsWith("ch.post.") && !s.getClassName().endsWith(".GroupVector")
							&& !s.getClassName().endsWith(".Validations") && !s.getClassName().endsWith(".ShuffleFuzz"))
					.findFirst().orElse(e.getStackTrace()[0]);
			if (emptyVectorSites.add(site.toString())) {
				System.err.println("EMPTY-GROUPVECTOR " + site + " (" + c.describe() + ": " + log + ")");
			}
			return;
		}
		if (accepted) {
			throw new FuzzerSecurityIssueCritical("mutated " + c.describe() + " accepted: " + log);
		}
	}
}
