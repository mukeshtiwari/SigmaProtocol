/*
 * Re-signing and forging tool for tampered copies of a Swiss Post e-voting
 * dataset (testdata layout: DATASET/D2/context, DATASET/D3/{context,tally}),
 * built on the e-voting-libraries domain classes and crypto-primitives, so
 * that signatures and proofs are computed exactly as the components do.
 *
 *   resign TESTDATA DATASET FILE...
 *       re-signs each tally payload (paths relative to DATASET) with the dev
 *       key of its component (testdata/direct-trust) and its channel-security
 *       context: controlComponentShufflePayload_j / controlComponentBallotBoxPayload_j
 *       (control component j), tallyComponentShufflePayload / tallyComponentVotesPayload
 *       (sdm_tally), eCH-0222*.xml (sdm_tally, enveloped XML signature)
 *   ebkey DATASET PW...
 *       derives EB_sk,i = RecursiveHashToZq(q, ("ElectoralBoardSecretKey", ee, i, PW...)), the tuple hashed as one list
 *       (System Specification, Algorithm 4.14) and compares g^EB_sk,i with the
 *       electoral board public key of the setup
 *   remix TESTDATA DATASET BB VARIANT PW...
 *       redoes MixDecOffline (Algorithm 6.11) for ballot box BB with the
 *       electoral board key: new tallyComponentShufflePayload (valid proofs) and
 *       a tallyComponentVotesPayload reordered to match, both re-signed.
 *       VARIANT: honest | stale-votes (keep the old votes payload) |
 *       wrong-input (shuffle a list where vote 1 is replaced by a re-encryption
 *       of vote 0) | wrong-key (vote 0 decrypted under a fresh key, valid
 *       proof for that key) | drop-one (shuffle all but the last vote) |
 *       wrong-key-all (valid shuffle under the setup's EB_pk, every vote
 *       decrypted under a fresh key with valid proofs for that key; no passwords)
 */
package ch.post.it.evoting.verifier.backend.tamper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.KeyStore;
import java.security.PrivateKey;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.IntStream;

import ch.post.it.evoting.cryptoprimitives.collection.AuxiliaryInformation;
import ch.post.it.evoting.cryptoprimitives.collection.ImmutableList;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientCiphertext;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientKeyPair;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientMessage;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientPrivateKey;
import ch.post.it.evoting.cryptoprimitives.elgamal.ElGamalMultiRecipientPublicKey;
import ch.post.it.evoting.cryptoprimitives.hashing.Hashable;
import ch.post.it.evoting.cryptoprimitives.hashing.HashableBigInteger;
import ch.post.it.evoting.cryptoprimitives.hashing.HashableString;
import ch.post.it.evoting.cryptoprimitives.internal.hashing.HashService;
import ch.post.it.evoting.cryptoprimitives.internal.math.RandomService;
import ch.post.it.evoting.cryptoprimitives.internal.mixnet.MixnetService;
import ch.post.it.evoting.cryptoprimitives.internal.zeroknowledgeproofs.ZeroKnowledgeProofService;
import ch.post.it.evoting.cryptoprimitives.math.GqElement;
import ch.post.it.evoting.cryptoprimitives.math.GqGroup;
import ch.post.it.evoting.cryptoprimitives.math.GroupVector;
import ch.post.it.evoting.cryptoprimitives.math.PrimeGqElement;
import ch.post.it.evoting.cryptoprimitives.math.ZqElement;
import ch.post.it.evoting.cryptoprimitives.math.ZqGroup;
import ch.post.it.evoting.cryptoprimitives.mixnet.VerifiableShuffle;
import ch.post.it.evoting.cryptoprimitives.signing.SignatureKeystore;
import ch.post.it.evoting.cryptoprimitives.signing.SignatureKeystoreFactory;
import ch.post.it.evoting.cryptoprimitives.zeroknowledgeproofs.VerifiableDecryptions;
import ch.post.it.evoting.evotinglibraries.domain.common.ChannelSecurityContextData;
import ch.post.it.evoting.evotinglibraries.domain.mapper.DomainJsonMapper;
import ch.post.it.evoting.evotinglibraries.domain.mixnet.ControlComponentShufflePayload;
import ch.post.it.evoting.evotinglibraries.domain.mixnet.ElectionEventContextPayload;
import ch.post.it.evoting.evotinglibraries.domain.mixnet.SetupComponentPublicKeysPayload;
import ch.post.it.evoting.evotinglibraries.domain.mixnet.TallyComponentShufflePayload;
import ch.post.it.evoting.evotinglibraries.domain.mixnet.VerifiablePlaintextDecryption;
import ch.post.it.evoting.evotinglibraries.domain.signature.Alias;
import ch.post.it.evoting.evotinglibraries.domain.signature.CryptoPrimitivesSignature;
import ch.post.it.evoting.evotinglibraries.domain.signature.SignedPayload;
import ch.post.it.evoting.evotinglibraries.domain.tally.ControlComponentBallotBoxPayload;
import ch.post.it.evoting.evotinglibraries.domain.tally.TallyComponentVotesPayload;
import ch.post.it.evoting.evotinglibraries.protocol.algorithms.channelsecurity.XMLSignatureService;

import tools.jackson.databind.json.JsonMapper;

public final class Tamper {

	private static final JsonMapper mapper = DomainJsonMapper.getNewInstance();
	private static final HashService hash = HashService.getInstance();
	private static final RandomService random = new RandomService();

	// ---- keys of testdata/direct-trust ----

	private static Path keystoreDir(final Path testdata, final Alias alias) {
		final String c = alias.get();
		return c.startsWith("control_component_")
				? testdata.resolve("direct-trust/control-component/" + c)
				: testdata.resolve("direct-trust/" + (c.equals("sdm_tally") ? "secure-data-manager-tally" : c));
	}

	private static char[] password(final Path dir, final Alias alias) throws Exception {
		return Files.readString(dir.resolve("local_direct_trust_pw_" + alias.get() + ".txt")).trim().toCharArray();
	}

	private static SignatureKeystore<Alias> signer(final Path testdata, final Alias alias) throws Exception {
		final Path dir = keystoreDir(testdata, alias);
		try (InputStream in = Files.newInputStream(dir.resolve("local_direct_trust_keystore_" + alias.get() + ".p12"))) {
			return SignatureKeystoreFactory.createSignatureKeystore(in, "PKCS12", password(dir, alias), ks -> true, alias);
		}
	}

	private static PrivateKey privateKey(final Path testdata, final Alias alias) throws Exception {
		final Path dir = keystoreDir(testdata, alias);
		final KeyStore ks = KeyStore.getInstance("PKCS12");
		try (InputStream in = Files.newInputStream(dir.resolve("local_direct_trust_keystore_" + alias.get() + ".p12"))) {
			ks.load(in, password(dir, alias));
		}
		return (PrivateKey) ks.getKey(alias.get(), password(dir, alias));
	}

	private static <T extends SignedPayload> void sign(final Path testdata, final Path file, final T payload, final Alias alias, final Hashable context)
			throws Exception {
		// the hashable form of a payload leaves out its signature
		final SignatureKeystore<Alias> s = signer(testdata, alias);
		payload.setSignature(new CryptoPrimitivesSignature(s.generateSignature(payload, context)));
		Files.writeString(file, mapper.writerWithDefaultPrettyPrinter().writeValueAsString(payload));
	}

	static void resign(final Path testdata, final Path file) throws Exception {
		final String name = file.getFileName().toString();
		if (name.startsWith("controlComponentShufflePayload")) {
			final ControlComponentShufflePayload p = mapper.readValue(file.toFile(), ControlComponentShufflePayload.class);
			sign(testdata, file, p, Alias.getControlComponentByNodeId(p.getNodeId()),
					ChannelSecurityContextData.controlComponentShuffle(p.getNodeId(), p.getElectionEventId(), p.getBallotBoxId()));
		} else if (name.startsWith("controlComponentBallotBoxPayload")) {
			final ControlComponentBallotBoxPayload p = mapper.readValue(file.toFile(), ControlComponentBallotBoxPayload.class);
			sign(testdata, file, p, Alias.getControlComponentByNodeId(p.getNodeId()),
					ChannelSecurityContextData.controlComponentBallotBox(p.getNodeId(), p.getElectionEventId(), p.getBallotBoxId()));
		} else if (name.startsWith("tallyComponentShufflePayload")) {
			final TallyComponentShufflePayload p = mapper.readValue(file.toFile(), TallyComponentShufflePayload.class);
			sign(testdata, file, p, Alias.SDM_TALLY, ChannelSecurityContextData.tallyComponentShuffle(p.getElectionEventId(), p.getBallotBoxId()));
		} else if (name.startsWith("tallyComponentVotesPayload")) {
			final TallyComponentVotesPayload p = mapper.readValue(file.toFile(), TallyComponentVotesPayload.class);
			sign(testdata, file, p, Alias.SDM_TALLY, ChannelSecurityContextData.tallyComponentVotes(p.getElectionEventId(), p.getBallotBoxId()));
		} else if (name.endsWith(".xml")) {
			// drop the extension that holds the enveloped signature, then sign again
			// where the tally component does (TallyComponentEch0222FileRepository)
			final String xml = Files.readString(file, StandardCharsets.UTF_8);
			final Matcher m = Pattern.compile("<eCH-0222:extension>.*</eCH-0222:extension>", Pattern.DOTALL).matcher(xml);
			final String unsigned = m.find() ? xml.substring(0, m.start()) + xml.substring(m.end()) : xml;
			final ByteArrayOutputStream out = new ByteArrayOutputStream();
			new XMLSignatureService().genXMLSignature(new ByteArrayInputStream(unsigned.getBytes(StandardCharsets.UTF_8)), out,
					privateKey(testdata, Alias.SDM_TALLY), "eCH-0222:rawDataDelivery", "eCH-0222:extension");
			Files.write(file, out.toByteArray());
		} else {
			throw new IllegalArgumentException("unknown payload " + file);
		}
	}

	// ---- the electoral board key ----

	private static ElectionEventContextPayload context(final Path dataset) throws Exception {
		return mapper.readValue(dataset.resolve("D3/context/electionEventContextPayload.json").toFile(), ElectionEventContextPayload.class);
	}

	private static ElGamalMultiRecipientKeyPair ebKey(final Path dataset, final GqGroup group, final int delta, final String[] pws) throws Exception {
		final String ee = context(dataset).getElectionEventContext().electionEventId();
		final List<ZqElement> sk = new ArrayList<>();
		for (int i = 0; i < delta; i++) {
			final List<Hashable> vs = new ArrayList<>(List.of(HashableString.from("ElectoralBoardSecretKey"), HashableString.from(ee),
					HashableBigInteger.from(BigInteger.valueOf(i))));
			// the passwords as byte arrays, exactly as the secure data manager makes them
			// (UTF_8.encode(CharBuffer).array(): the encoder's whole backing array)
			for (final String pw : pws) {
				vs.add(new ch.post.it.evoting.cryptoprimitives.collection.ImmutableByteArray(
						StandardCharsets.UTF_8.encode(java.nio.CharBuffer.wrap(pw.toCharArray())).array()));
			}
			// one nested list, as MixDecOfflineAlgorithm and SetupTallyEBAlgorithm of the e-voting system hash it
			sk.add(hash.recursiveHashToZq(group.getQ(), ch.post.it.evoting.cryptoprimitives.hashing.HashableList.from(ImmutableList.from(vs))));
		}
		return ElGamalMultiRecipientKeyPair.from(new ElGamalMultiRecipientPrivateKey(GroupVector.from(ImmutableList.from(sk))), group.getGenerator());
	}

	private static GroupVector<GqElement, GqGroup> ebPublicKey(final Path dataset) throws Exception {
		final SetupComponentPublicKeysPayload p = mapper.readValue(dataset.resolve("D3/context/setupComponentPublicKeysPayload.json").toFile(),
				SetupComponentPublicKeysPayload.class);
		return GroupVector.from(p.getSetupComponentPublicKeys().electoralBoardPublicKey().getKeyElements());
	}

	// ---- MixDecOffline again ----

	static void remix(final Path testdata, final Path dataset, final String bb, final String variant, final String[] pws) throws Exception {
		final Path dir = dataset.resolve("D3/tally/ballotBoxes/" + bb);
		final ControlComponentShufflePayload cc4 = mapper.readValue(dir.resolve("controlComponentShufflePayload_4.json").toFile(),
				ControlComponentShufflePayload.class);
		final TallyComponentShufflePayload old = mapper.readValue(dir.resolve("tallyComponentShufflePayload.json").toFile(),
				TallyComponentShufflePayload.class);
		final TallyComponentVotesPayload oldVotes = mapper.readValue(dir.resolve("tallyComponentVotesPayload.json").toFile(),
				TallyComponentVotesPayload.class);
		final GqGroup group = cc4.getEncryptionGroup();
		final String ee = cc4.getElectionEventId();
		GroupVector<ElGamalMultiRecipientCiphertext, GqGroup> cdec4 = cc4.getVerifiableDecryptions().getCiphertexts();
		final int delta = cdec4.getElementSize();
		// wrong-key-all: the shuffle under the electoral board public key of the setup, the
		// decryptions under a fresh key (the passwords of the dataset are not published)
		final ElGamalMultiRecipientKeyPair eb = variant.equals("wrong-key-all")
				? ElGamalMultiRecipientKeyPair.genKeyPair(group, delta, random)
				: ebKey(dataset, group, delta, pws);
		final ElGamalMultiRecipientPublicKey ebpk = variant.equals("wrong-key-all")
				? new ElGamalMultiRecipientPublicKey(GroupVector.from(ImmutableList.from(ebPublicKey(dataset).stream().limit(delta).toList())))
				: eb.getPublicKey();
		switch (variant) {
		case "wrong-input" -> {
			final List<ElGamalMultiRecipientCiphertext> cs = new ArrayList<>(cdec4.stream().toList());
			final ZqElement r = ZqElement.create(random.genRandomInteger(group.getQ()), ZqGroup.sameOrderAs(group));
			final ElGamalMultiRecipientCiphertext one = ch.post.it.evoting.cryptoprimitives.internal.elgamal.ElGamalMultiRecipientCiphertexts.getCiphertext(
					new ElGamalMultiRecipientMessage(GroupVector.from(ImmutableList.from(
							IntStream.range(0, delta).mapToObj(i -> group.getIdentity()).toList()))), r, ebpk);
			cs.set(1, cs.get(0).getCiphertextProduct(one));
			cdec4 = GroupVector.from(ImmutableList.from(cs));
		}
		case "drop-one" -> cdec4 = GroupVector.from(ImmutableList.from(cdec4.stream().limit(cdec4.size() - 1).toList()));
		default -> {
		}
		}
		final AuxiliaryInformation aux = AuxiliaryInformation.of(ee, bb, "MixDecOffline");
		VerifiableShuffle shuffle;
		VerifiableDecryptions dec;
		ImmutableList<Integer> order;
		do {
			shuffle = new MixnetService().genVerifiableShuffle(cdec4, ebpk);
			dec = new ZeroKnowledgeProofService().genVerifiableDecryptions(shuffle.shuffledCiphertexts(), eb, aux);
			order = matchVotes(group, dec, oldVotes);
		} while (variant.equals("stale-votes") && isIdentity(order));
		if (variant.equals("wrong-key")) {
			// vote 0 decrypted under a fresh key: a valid proof, for the wrong key
			final ElGamalMultiRecipientKeyPair other = ElGamalMultiRecipientKeyPair.genKeyPair(group, delta, random);
			final VerifiableDecryptions d0 = new ZeroKnowledgeProofService().genVerifiableDecryptions(
					GroupVector.of(shuffle.shuffledCiphertexts().get(0)), other, aux);
			final List<ElGamalMultiRecipientCiphertext> cs = new ArrayList<>(dec.getCiphertexts().stream().toList());
			final List<ch.post.it.evoting.cryptoprimitives.zeroknowledgeproofs.DecryptionProof> ps = new ArrayList<>(
					dec.getDecryptionProofs().stream().toList());
			cs.set(0, d0.getCiphertexts().get(0));
			ps.set(0, d0.getDecryptionProofs().get(0));
			dec = new VerifiableDecryptions(GroupVector.from(ImmutableList.from(cs)), GroupVector.from(ImmutableList.from(ps)));
		}
		final GroupVector<ElGamalMultiRecipientMessage, GqGroup> messages = GroupVector.from(ImmutableList.from(dec.getCiphertexts().stream()
				.map(c -> new ElGamalMultiRecipientMessage(c.getPhis())).toList()));
		final TallyComponentShufflePayload p = new TallyComponentShufflePayload(group, ee, bb, shuffle,
				new VerifiablePlaintextDecryption(messages, dec.getDecryptionProofs()));
		sign(testdata, dir.resolve("tallyComponentShufflePayload.json"), p, Alias.SDM_TALLY, ChannelSecurityContextData.tallyComponentShuffle(ee, bb));
		System.out.println("old proof replaced: " + !old.equals(p) + "; vote order " + order);
		if (!variant.equals("stale-votes") && !variant.equals("wrong-key") && order != null) {
			final TallyComponentVotesPayload v = new TallyComponentVotesPayload(group, ee, bb,
					GroupVector.from(ImmutableList.from(order.stream().map(i -> oldVotes.getDecryptedVotes().get(i)).toList())),
					ImmutableList.from(order.stream().map(i -> oldVotes.getDecodedVotes().get(i)).toList()),
					ImmutableList.from(order.stream().map(i -> oldVotes.getDecodedWriteIns().get(i)).toList()));
			sign(testdata, dir.resolve("tallyComponentVotesPayload.json"), v, Alias.SDM_TALLY, ChannelSecurityContextData.tallyComponentVotes(ee, bb));
		}
	}

	// the entry of the votes payload whose primes multiply to each decrypted message (null if one has none)
	private static ImmutableList<Integer> matchVotes(final GqGroup g, final VerifiableDecryptions dec, final TallyComponentVotesPayload votes) {
		final List<BigInteger> products = votes.getDecryptedVotes().stream()
				.map(v -> v.stream().map(PrimeGqElement::getValue).reduce(BigInteger.ONE, (a, b) -> a.multiply(b).mod(g.getP()))).toList();
		final List<Integer> order = new ArrayList<>();
		for (final ElGamalMultiRecipientCiphertext c : dec.getCiphertexts()) {
			final int i = products.indexOf(c.getPhis().get(0).getValue());
			if (i < 0) {
				return null;
			}
			order.add(i);
		}
		return ImmutableList.from(order);
	}

	private static boolean isIdentity(final ImmutableList<Integer> order) {
		return order != null && IntStream.range(0, order.size()).allMatch(i -> order.get(i) == i);
	}

	public static void main(final String[] args) throws Exception {
		switch (args[0]) {
		case "resign" -> {
			for (int i = 3; i < args.length; i++) {
				resign(Path.of(args[1]), Path.of(args[2]).resolve(args[i]));
			}
		}
		case "ebkey" -> {
			final Path dataset = Path.of(args[1]);
			final GroupVector<GqElement, GqGroup> pk = ebPublicKey(dataset);
			final ElGamalMultiRecipientKeyPair eb = ebKey(dataset, pk.getGroup(), pk.size(),
					java.util.Arrays.copyOfRange(args, 2, args.length));
			System.out.println("electoral board key derived from the passwords matches the setup: "
					+ eb.getPublicKey().getKeyElements().equals(pk) + " (" + pk.size() + " elements)");
		}
		case "remix" -> remix(Path.of(args[1]), Path.of(args[2]), args[3], args[4], java.util.Arrays.copyOfRange(args, 5, args.length));
		default -> throw new IllegalArgumentException(args[0]);
		}
	}
}
