/*
 * Headless driver for the Swiss Post Verifier (verifier-backend): starts its
 * Spring context (web server on a random port, unused), takes every
 * verification bean, and runs the setup verifications on SETUP_DIR and the
 * tally verifications on TALLY_DIR synchronously, in the order of their ids,
 * by calling verify(Path) as AbstractVerification.executeVerify does. The
 * encrypted-zip upload of the GUI is bypassed: SETUP_DIR holds context/, and
 * TALLY_DIR holds context/ and tally/, as in the Verifier's own tests.
 *
 *   VerifierCli KEYSTORE PASSWORD_FILE SETUP_DIR TALLY_DIR [setup|tally|all]
 *
 * One line per verification: block id status name [message]; exit code 0 iff
 * every verification is OK.
 */
package ch.post.it.evoting.verifier.backend;

import java.nio.file.Path;
import java.util.Comparator;
import java.util.List;

import org.springframework.boot.builder.SpringApplicationBuilder;
import org.springframework.context.ConfigurableApplicationContext;

public final class VerifierCli {

	public static void main(final String[] args) {
		final String mode = args.length > 4 ? args[4] : "all";
		// command-line properties: they override application.yaml, whose mandatory keys are empty
		final ConfigurableApplicationContext ctx = new SpringApplicationBuilder(Application.class).run(
				"--server.port=0",
				"--direct.trust.keystore.location=" + args[0],
				"--direct.trust.keystore.password.location=" + args[1],
				"--direct.trust.keystore.type=PKCS12",
				"--import.zip.decryption.password=Unused-Import-Passw0rd-For-CLI!",
				"--logging.file.name=" + System.getProperty("java.io.tmpdir") + "/verifier-cli.log",
				"--spring.main.banner-mode=off",
				"--logging.level.root=WARN");
		final List<AbstractVerification> vs = ctx.getBeansOfType(AbstractVerification.class).values().stream()
				.sorted(Comparator.<AbstractVerification, String>comparing(v -> v.getVerificationDefinition().getBlock()).reversed()
						.thenComparing(v -> Double.parseDouble(v.getVerificationDefinition().getId())))
				.toList();
		boolean ok = true;
		for (final AbstractVerification v : vs) {
			final VerificationDefinition d = v.getVerificationDefinition();
			if (!mode.equals("all") && !mode.equals(d.getBlock())) {
				continue;
			}
			final Path dir = Path.of(d.getBlock().equals("setup") ? args[2] : args[3]);
			VerificationResult r;
			try {
				r = v.verify(dir);
			} catch (final Exception e) {
				r = VerificationResult.error(d, e);
			}
			final String status = String.valueOf(r.getStatus());
			ok &= status.equals("OK");
			final String msg = r.getMessage() == null ? "" : String.valueOf(r.getMessage().get(Language.EN));
			final String err = r.getErrorStack() == null || r.getErrorStack().isEmpty() ? "" : " | " + r.getErrorStack().get(0);
			System.out.printf("%s\t%s\t%s\t%s\t%s%s%n", d.getBlock(), d.getId(), status, d.getName(),
					msg.equals("null") ? "" : msg.replace('\n', ' '), err.replace('\n', ' '));
		}
		ctx.close();
		System.exit(ok ? 0 : 1);
	}
}
