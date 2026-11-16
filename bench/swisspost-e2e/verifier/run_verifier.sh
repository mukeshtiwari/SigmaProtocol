#!/bin/sh
# Runs the Swiss Post Verifier headlessly (VerifierCli.java) on one election
# dataset laid out as in the testdata repository.
#
# usage: run_verifier.sh VERIFIER_CHECKOUT TESTDATA_CHECKOUT DATASET [setup|tally|all]
#   VERIFIER_CHECKOUT  verifier repository, built with build.sh
#   TESTDATA_CHECKOUT  testdata repository (for the verifier's direct-trust keystore)
#   DATASET            directory with D2/ (setup: context/) and D3/ (tally: context/, tally/)
# needs JAVA_HOME = a JDK 25
set -e
v=$(cd "$1" && pwd)/verifier-backend; td=$(cd "$2" && pwd); ds=$(cd "$3" && pwd); here=$(cd "$(dirname "$0")" && pwd)
java=${JAVA_HOME:+$JAVA_HOME/bin/}java
out=$v/target/cli-classes
if [ ! -f "$out/ch/post/it/evoting/verifier/backend/VerifierCli.class" ] || [ "$here/VerifierCli.java" -nt "$out/ch/post/it/evoting/verifier/backend/VerifierCli.class" ]; then
  mkdir -p "$out"
  "${JAVA_HOME:+$JAVA_HOME/bin/}javac" -nowarn -proc:none -d "$out" -cp "$v/target/classes:$(cat "$v/cp.txt")" "$here/VerifierCli.java"
fi
exec "$java" -cp "$out:$v/target/classes:$(cat "$v/cp.txt")" ch.post.it.evoting.verifier.backend.VerifierCli \
  "$td/direct-trust/verifier/local_direct_trust_keystore_verifier.p12" "$td/direct-trust/verifier/local_direct_trust_pw_verifier.txt" \
  "$ds/D2" "$ds/D3" "${4:-all}"
