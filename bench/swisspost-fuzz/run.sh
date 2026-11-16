#!/bin/sh
# Runs one fuzz target for a bounded time, keeping its corpus, crashing
# inputs and Java reproducers in WORK_DIR/TARGET; with a crashing input as
# extra argument, runs that input once instead.
#
# usage: bench/swisspost-fuzz/run.sh TARGET SECONDS BUILD_DIR JAZZER_DIR WORK_DIR [INPUT]
#   TARGET: ShuffleFuzz | CommitmentKeyFuzz | RecursiveHashFuzz | EncodingFuzz
# needs JDK 25 (JAVA_HOME)
set -e
target=$1; secs=$2; build=$(cd "$3" && pwd); jazzer=$(cd "$4" && pwd); work=$5; input=$6
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
case $target in
  ShuffleFuzz)       class=ch.post.it.evoting.cryptoprimitives.internal.mixnet.ShuffleFuzz; export SECURITY_LEVEL=TESTING_ONLY ;;
  CommitmentKeyFuzz) class=ch.post.it.evoting.cryptoprimitives.internal.mixnet.CommitmentKeyFuzz ;;
  RecursiveHashFuzz) class=ch.post.it.evoting.cryptoprimitives.internal.hashing.RecursiveHashFuzz ;;
  EncodingFuzz)      class=ch.post.it.evoting.cryptoprimitives.fuzz.EncodingFuzz ;;
  *) echo "unknown target $target" >&2; exit 2 ;;
esac
export FUZZ_FIXTURE="$root/src/Executable/Bgverifier/data/verify-shuffle-argument.json"
dir=$work/$target; mkdir -p "$dir/corpus"; dir=$(cd "$dir" && pwd)
cp=$build/classes; for j in "$build"/lib/*.jar; do cp=$cp:$j; done   # Jazzer does not expand lib/*
set -- --cp="$cp" --target_class=$class \
  --instrumentation_includes='ch.post.it.evoting.cryptoprimitives.**' --custom_hook_includes='ch.post.it.evoting.cryptoprimitives.**' \
  --jvm_args=-Xmx4g --keep_going=1000 --reproducer_path="$dir" -artifact_prefix="$dir/" -timeout=120 -rss_limit_mb=8192
if [ -n "$input" ]; then
  exec "$jazzer/jazzer" "$@" "$input"
fi
exec "$jazzer/jazzer" "$@" -max_total_time="$secs" -print_final_stats=1 "$dir/corpus"
