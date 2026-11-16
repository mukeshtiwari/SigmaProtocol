/*
 * Feasibility probe (our code, compiled alongside an unmodified IVXV build):
 * runs IVXV's own Verificatum shuffle-proof verifier (ee.ivxv.audit.shuffle.Verifier)
 * on mix server 01 of a Verificatum (vmn 3.1.0) execution. IVXV's XML reader
 * insists on keywidth 5, which is not part of the Fiat-Shamir prefix rho and only
 * fixes the ciphertext group; this probe reads the protocol information itself and
 * supplies the execution's keywidth.
 *
 * usage: ProbeShuffle PROTINFO.xml EXECUTION_DIR(default/) [tamper]
 */
package ee.ivxv.audit.shuffle;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ee.ivxv.common.math.Group;
import ee.ivxv.common.math.GroupElement;

public final class ProbeShuffle {

    static String tag(String xml, String t) {
        Matcher m = Pattern.compile("<" + t + ">([^<]*)</" + t + ">").matcher(xml);
        if (!m.find()) throw new IllegalArgumentException("no <" + t + ">");
        return m.group(1).trim();
    }

    static final class Prot extends ProtocolInformation {
        private final Group g; private final GroupElement gen; private final int kw;
        Prot(String xml) throws ShuffleException {
            super(tag(xml, "version"), tag(xml, "sid"), tag(xml, "name"), tag(xml, "pgroup"),
                  Integer.parseInt(tag(xml, "keywidth")), Integer.parseInt(tag(xml, "vbitlenro")),
                  Integer.parseInt(tag(xml, "ebitlenro")), tag(xml, "prg"), tag(xml, "rohash"),
                  Integer.parseInt(tag(xml, "width")), Integer.parseInt(tag(xml, "statdist")));
            this.gen = DataParser.parseGroupGenerator(tag(xml, "pgroup"));
            this.g = gen.getGroup();
            this.kw = Integer.parseInt(tag(xml, "keywidth"));
        }
        @Override public Group get_parsed_pgroup() { return g; }
        @Override public GroupElement get_parsed_generator() { return gen; }
        @Override public int get_keywidth() { return kw; }
    }

    // the verifier reports progress to a console; a silent one
    static final class Quiet extends ShuffleConsole {
        Quiet() { super(null); }
        @Override public void enter(ShuffleStep step) {}
        @Override public ee.ivxv.common.service.console.Progress enter(ShuffleStep step, long length) {
            return new ee.ivxv.common.service.console.Progress() {
                public void increase(int amount) {}
                public void finish() {}
            };
        }
    }

    public static void main(String[] a) throws Exception {
        if (a[0].equals("--official")) {   // IVXV's own reader: ShuffleProof(protInfo, dir), dir laid out as IVXV expects
            ShuffleProof proof = new ShuffleProof(Path.of(a[1]), Path.of(a[2]), new Quiet());
            boolean ok;
            try { ok = new Verifier(new Quiet(), proof).verify_all(); }
            catch (ShuffleException e) { System.out.println("rejected: " + e.getMessage()); ok = false; }
            System.out.println(ok ? "true" : "false");
            return;
        }
        Prot prot = new Prot(Files.readString(Path.of(a[0])));
        Path d = Path.of(a[1]), pr = d.resolve("proofs");
        ShuffleProof.PermutationCommitment pc = new ShuffleProof.PermutationCommitment(prot, pr.resolve("PermutationCommitment01.bt"));
        ShuffleProof.PoSCommitment posc = new ShuffleProof.PoSCommitment(prot, pr.resolve("PoSCommitment01.bt"));
        ShuffleProof.PoSReply posr = new ShuffleProof.PoSReply(prot, pr.resolve("PoSReply01.bt"));
        // Verificatum encodes a width-1 product as a bare element; IVXV's layout is (G^keywidth)^2
        Group cg = prot.get_keywidth() == 1
            ? new ee.ivxv.common.math.ProductGroup(prot.get_parsed_pgroup(), 2)
            : new ee.ivxv.common.math.ProductGroup(new ee.ivxv.common.math.ProductGroup(prot.get_parsed_pgroup(), prot.get_keywidth()), 2);
        GroupElement pk = DataParser.getAsElement(cg, ByteTree.parse(d.resolve("FullPublicKey.bt")));
        GroupElement[] in = DataParser.getAsElementArray(cg, ByteTree.parse(d.resolve("Ciphertexts.bt")));
        GroupElement[] out = DataParser.getAsElementArray(cg, ByteTree.parse(pr.resolve("Ciphertexts01.bt")));
        if (a.length > 2) { GroupElement t = out[0]; out[0] = out[1]; out[1] = t; }   // two outputs swapped
        ShuffleProof proof = new ShuffleProof(prot, pc, posc, posr, in, out, pk);
        boolean ok;
        try { ok = new Verifier(new Quiet(), proof).verify_all(); }
        catch (ShuffleException e) { System.out.println("rejected: " + e.getMessage()); ok = false; }
        System.out.println(ok ? "true" : "false");
    }
}
