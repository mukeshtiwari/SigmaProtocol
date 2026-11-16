#!/bin/sh
# Compiles the Swiss Post crypto-primitives library (main sources, and the
# JSON fixture parsers of its test suite) together with the drivers *.java
# of this directory (package internal.mixnet) as one
# Java module. The upstream pom needs an in-house Maven plugin, so Maven is
# only used to fetch the dependency jars.
#
# usage: bench/swisspost-diff/build.sh bench/crypto-primitives BUILD_DIR
# (the submodule: git submodule update --init bench/crypto-primitives)
# needs a JDK >= 25 (JAVA_HOME) and Maven
set -e
src=$(cd "$1" && pwd); out=$2; here=$(cd "$(dirname "$0")" && pwd)
javac=${JAVA_HOME:+$JAVA_HOME/bin/}javac
mkdir -p "$out"; out=$(cd "$out" && pwd)
rm -rf "$out/stage" "$out/classes"
(cd "$src" && mvn -q -B dependency:copy-dependencies -DincludeScope=test -DoutputDirectory="$out/lib")
mkdir -p "$out/mods"
cp "$out"/lib/guava-*.jar "$out"/lib/failureaccess-*.jar "$out"/lib/bc*-jdk18on-*.jar "$out"/lib/slf4j-api-*.jar \
   "$out"/lib/jackson-*.jar "$out"/lib/jspecify-*.jar "$out"/lib/error_prone_annotations-*.jar "$out"/lib/j2objc-*.jar "$out/mods/"

stage=$out/stage; T=src/test/java/ch/post/it/evoting/cryptoprimitives
mkdir -p "$stage"
cp -r "$src/src/main/java/." "$stage/"
mkdir -p "$stage/ch/post/it/evoting/cryptoprimitives/test/tools/serialization"
cp "$src/$T/test/tools/serialization/"*.java "$stage/ch/post/it/evoting/cryptoprimitives/test/tools/serialization/"
cp "$src/$T/internal/mixnet/TestContextParser.java" "$src/$T/internal/mixnet/TestArgumentParser.java" \
   "$src/$T/internal/mixnet/TestParser.java" "$here/"*.java "$stage/ch/post/it/evoting/cryptoprimitives/internal/mixnet/"
# the module also reads Jackson and opens the fixture classes to it
perl -0pi -e 's/(requires org\.slf4j;)/$1\n\trequires tools.jackson.databind;\n\topens ch.post.it.evoting.cryptoprimitives.test.tools.serialization to tools.jackson.databind;/' "$stage/module-info.java"
find "$stage" -name '*.java' > "$out/sources.txt"
"$javac" -nowarn -proc:none --release 25 -d "$out/classes" --module-path "$out/mods" @"$out/sources.txt"
cp -r "$src/src/main/resources/." "$out/classes/"
echo "built $out/classes"
