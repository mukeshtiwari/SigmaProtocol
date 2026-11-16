/*
 * Our code, compiled alongside an unmodified IVXV build (CC BY-NC-ND 3.0; no
 * IVXV file is copied or changed): runs IVXV's auditor proof-of-shuffle
 * verifier exactly as its MixerTool does -- new ShuffleProof(protInfo, dir)
 * read by IVXV's own reader, then Verifier.verify_all() (non-threaded) -- on
 * each case of a list. Any exception (reader or verifier) is a rejection,
 * as in MixerTool, where it aborts the tool. Each case is verified in both of
 * MixerTool's modes: Verifier (the default) and ThreadedVerifier (--threaded).
 *
 * usage: IvxvShuffleDiff CASES.tsv     (lines: protInfo.xml <TAB> proof directory)
 * output: one line per case: VERDICT <TAB> VERDICT_THREADED, each true | false|reason
 */
package ee.ivxv.audit.shuffle;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
// ThreadedVerifier shuts its executor down only with the JVM: exit explicitly

public final class IvxvShuffleDiff {

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

    // MixerTool's two modes: Verifier (the default) and ThreadedVerifier (--threaded)
    static String verify(Path prot, Path dir, boolean threaded) {
        try {
            ShuffleProof proof = new ShuffleProof(prot, dir, new Quiet());
            Verifier v = threaded ? new ThreadedVerifier(new Quiet(), proof, 2) : new Verifier(new Quiet(), proof);
            return v.verify_all() ? "true" : "false|verify_all returned false";
        } catch (Throwable e) {
            return "false|" + e.getClass().getSimpleName() + ": " + String.valueOf(e.getMessage()).replace('\n', ' ').replace('\t', ' ').replace('|', ' ');
        }
    }

    public static void main(String[] a) throws Exception {
        List<String> lines = Files.readAllLines(Path.of(a[0]));
        for (String l : lines) {
            if (l.isBlank()) continue;
            String[] f = l.split("\t");
            System.out.println(verify(Path.of(f[0]), Path.of(f[1]), false) + "\t" + verify(Path.of(f[0]), Path.of(f[1]), true));
        }
        System.exit(0);
    }
}
