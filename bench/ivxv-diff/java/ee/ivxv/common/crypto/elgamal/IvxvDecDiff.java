/*
 * Our code, compiled alongside an unmodified IVXV build (CC BY-NC-ND 3.0; no
 * IVXV file is copied or changed). IVXV decryption proofs
 * (ElGamalDecryptionProof):
 *
 *   prove STATEMENTS.tsv   lines "p g eid x c1 c2" (decimal; eid a string without tabs):
 *                          IVXV's ElGamalPrivateKey.provableDecrypt (its own randomness);
 *                          prints "pk ct msg proof" as hex DER, the encodings IVXV produces
 *   verify CASES.tsv       lines "pk ct msg proof" (hex DER): verified as the auditor's
 *                          DecryptTool does -- the key from its X.509 encoding, the plaintext
 *                          by group.getElement, the ciphertext and the proof from their
 *                          encodings, then verifyProof(); any exception is a rejection
 *                          (DecryptTool counts a MathException as an invalid proof)
 */
package ee.ivxv.common.crypto.elgamal;

import java.math.BigInteger;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HexFormat;

import ee.ivxv.common.math.GroupElement;
import ee.ivxv.common.math.ModPGroup;
import ee.ivxv.common.math.ModPGroupElement;

public final class IvxvDecDiff {
    static final HexFormat HEX = HexFormat.of();

    public static void main(String[] a) throws Exception {
        for (String l : Files.readAllLines(Path.of(a[1]))) {
            if (l.isBlank()) continue;
            String[] f = l.split("\t");
            if (a[0].equals("prove")) {
                BigInteger p = new BigInteger(f[0]), g = new BigInteger(f[1]), x = new BigInteger(f[3]);
                ModPGroup grp = new ModPGroup(p);
                ElGamalParameters params = new ElGamalParameters(grp, new ModPGroupElement(grp, g), f[2]);
                ElGamalPrivateKey sk = new ElGamalPrivateKey(params, x);
                ElGamalCiphertext ct = new ElGamalCiphertext(new ModPGroupElement(grp, new BigInteger(f[4])),
                        new ModPGroupElement(grp, new BigInteger(f[5])), params.getOID());
                ElGamalDecryptionProof pr = sk.provableDecrypt(ct);
                System.out.println(HEX.formatHex(sk.getPublicKey().getBytes()) + "\t" + HEX.formatHex(ct.getBytes()) + "\t"
                        + HEX.formatHex(pr.decrypted.getBytes()) + "\t" + HEX.formatHex(pr.getBytes()));
            } else {
                String r;
                try {
                    ElGamalPublicKey pub = new ElGamalPublicKey(HEX.parseHex(f[0]));
                    GroupElement decrypted = pub.getParameters().getGroup().getElement(HEX.parseHex(f[2]));
                    ElGamalCiphertext ct = new ElGamalCiphertext(pub.getParameters(), HEX.parseHex(f[1]));
                    ElGamalDecryptionProof proof = new ElGamalDecryptionProof(ct, decrypted, pub, HEX.parseHex(f[3]));
                    r = proof.verifyProof() ? "true" : "false\tverifyProof returned false";
                } catch (Throwable e) {
                    r = "false\t" + e.getClass().getSimpleName() + ": " + String.valueOf(e.getMessage()).replace('\n', ' ').replace('\t', ' ');
                }
                System.out.println(r);
            }
        }
    }
}
