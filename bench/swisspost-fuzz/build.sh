#!/bin/sh
# Compiles the Swiss Post crypto-primitives library (main sources) and the fuzz
# targets of src/ for Jazzer, which loads targets from the class path. On the
# class path (the unnamed module) a sealed type may only permit subclasses of
# its own package, so the build strips sealed/permits from a copy of the
# sources (VerificationResult, Base16/32/64, Alphabet, GqElement); nothing
# else changes. The targets live in the library's packages to reach its
# package-private services.
#
# usage: bench/swisspost-fuzz/build.sh bench/crypto-primitives JAZZER_DIR BUILD_DIR
# needs JDK 25 (JAVA_HOME; the Jazzer 0.30 instrumentation cannot read the
# class files of later JDKs) and Maven; JAZZER_DIR holds jazzer_standalone.jar
set -e
src=$(cd "$1" && pwd); jazzer=$(cd "$2" && pwd); out=$3; here=$(cd "$(dirname "$0")" && pwd)
javac=${JAVA_HOME:+$JAVA_HOME/bin/}javac
mkdir -p "$out"; out=$(cd "$out" && pwd)
rm -rf "$out/stage" "$out/classes"
(cd "$src" && mvn -q -B dependency:copy-dependencies -DincludeScope=compile -DoutputDirectory="$out/lib")

stage=$out/stage
mkdir -p "$stage"
cp -r "$src/src/main/java/." "$stage/"
rm "$stage/module-info.java"
find "$stage" -name '*.java' -exec perl -0pi -e 's/\bsealed\s+(class|interface)\s+(\w+)([^{]*?)\s*\bpermits\b[^{]*\{/$1 $2$3 {/g' {} +
if grep -rqE '^[^*/]*\b(sealed|non-sealed)\b' "$stage" --include='*.java'; then echo "sealed types left" >&2; exit 1; fi
cp -r "$here/src/." "$stage/"
find "$stage" -name '*.java' > "$out/sources.txt"
"$javac" -nowarn -proc:none --release 25 -d "$out/classes" -cp "$out/lib/*:$jazzer/jazzer_standalone.jar" @"$out/sources.txt"
cp -r "$src/src/main/resources/." "$out/classes/"
echo "built $out/classes"
