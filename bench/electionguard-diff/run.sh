#!/bin/sh
# Reproduces the ElectionGuard differential campaign end to end:
#   1. fetches electionguard-kotlin-multiplatform (egk) at the pinned commit and
#      checks it, builds it with the pinned Gradle (checksum verified) and JDK 17
#      in an isolated Gradle home;
#   2. builds the certified verifier (dune, opam switch "default");
#   3. checks the fixtures against fixtures.sha256 (or regenerates them with
#      --regen, which makes new elections: egk draws its randomness from
#      SecureRandom, so the verdict tables, not the files, are what reproduce);
#   4. runs campaign.py twice with the same seed and checks that the two verdict
#      tables (results/run1/summary.tsv, results/run2/summary.tsv) are identical.
#
# usage: bench/electionguard-diff/run.sh WORK_DIR [SEED] [--regen]
#   JAVA_HOME must point to a JDK 17 (egk's jvmToolchain(17)); default:
#   /opt/homebrew/opt/openjdk@17/libexec/openjdk.jdk/Contents/Home
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=$1; seed=${2:-1}; regen=${3:-}
mkdir -p "$work"; work=$(cd "$work" && pwd)

EGK_URL=https://github.com/JohnLCaron/electionguard-kotlin-multiplatform.git
EGK_COMMIT=194b9c788ccaecda8719c227bd41ce57a3b857be     # final commit, v2.0.4-SNAPSHOT, 2024-02-18 (repository archived)
GRADLE_SHA256=9631d53cf3e74bfa726893aee1f8994fee4e060c401335946dba2156f440f24c   # gradle-8.6-bin.zip (the wrapper's distribution)
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk@17/libexec/openjdk.jdk/Contents/Home}
java="$JAVA_HOME/bin/java"
"$java" -version 2>&1 | head -1 | grep -q '"17\.' || { echo "JAVA_HOME must be a JDK 17"; exit 1; }

# ---- 1. egk ----
egk="$work/egk"
if [ ! -d "$egk/.git" ]; then git clone -q "$EGK_URL" "$egk"; fi
git -C "$egk" checkout -q "$EGK_COMMIT"
[ "$(git -C "$egk" rev-parse HEAD)" = "$EGK_COMMIT" ] || { echo "egk commit mismatch"; exit 1; }
props="$egk/gradle/wrapper/gradle-wrapper.properties"
grep -q distributionSha256Sum "$props" || echo "distributionSha256Sum=$GRADLE_SHA256" >> "$props"
jar="$egk/egkliball/build/libs/egklib-all.jar"
if [ ! -f "$jar" ]; then
  (cd "$egk" && JAVA_HOME="$JAVA_HOME" GRADLE_USER_HOME="$work/gradle-home" ./gradlew --no-daemon --max-workers=4 -q :egklib:jvmJar \
     && JAVA_HOME="$JAVA_HOME" GRADLE_USER_HOME="$work/gradle-home" ./gradlew --no-daemon --max-workers=4 -q :egkliball:fatJar > /dev/null)
fi

# ---- 2. the certified verifier ----
(cd "$root" && eval "$(opam env --switch=default 2>/dev/null)" && dune build src/Executable/Egverifier/main.exe 2>/dev/null)
ours="$root/_build/default/src/Executable/Egverifier/main.exe"

# ---- 3. fixtures ----
fixtures="$here/fixtures"
if [ "$regen" = "--regen" ]; then
  fixtures="$work/fixtures"; rm -rf "$fixtures"
  "$here/gen_elections.sh" "$jar" "$java" "$fixtures"
else
  (cd "$fixtures" && shasum -a 256 -c --quiet "$here/fixtures.sha256") || { echo "fixtures changed"; exit 1; }
fi

# ---- versions ----
mkdir -p "$here/results"
{
  echo "egk $EGK_COMMIT"; echo "egklib-all.jar sha256 $(shasum -a 256 "$jar" | cut -d' ' -f1)"
  echo "java: $("$java" -version 2>&1 | head -1)"; echo "gradle 8.6 sha256 $GRADLE_SHA256"
  echo "python: $(python3 --version)"; echo "ocaml: $(cd "$root" && eval "$(opam env --switch=default 2>/dev/null)" && ocamlfind ocamlc -version)"
  echo "certified verifier: $(cd "$root" && git rev-parse HEAD) + working tree; main.exe sha256 $(shasum -a 256 "$ours" | cut -d' ' -f1)"
  echo "seed $seed"
} > "$here/results/versions.txt"

# ---- 4. the campaign, twice ----
for run in run1 run2; do
  python3 -I "$here/campaign.py" --jar "$jar" --java "$java" --ours "$ours" --fixtures "$fixtures" \
    --egk-data "$egk/egklib/src/commonTest/data/workflow" --work "$work/$run" --out "$here/results/$run" --seed "$seed" --jobs 4
done
if cmp -s "$here/results/run1/summary.tsv" "$here/results/run2/summary.tsv"; then
  echo "the two runs with seed $seed give identical verdict tables"; cp "$here/results/run1/summary.tsv" "$here/results/summary.tsv"
else
  echo "the two runs differ:"; diff "$here/results/run1/summary.tsv" "$here/results/run2/summary.tsv" | head -20; exit 1
fi
