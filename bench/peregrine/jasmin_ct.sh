#!/usr/bin/env bash
# Constant-time check of the Jasmin modules ed25519_bedrock.jazz and
# fieldl_bedrock.jazz with jasmin-ct (JASMIN_CT, default jasmin-ct).
#
#   bench/peregrine/jasmin_ct.sh [PASS ...]
#
# Each export function gets a ct signature (the security level of the
# contents of each buffer argument and of each returned buffer):
#   jasmin_ed25519_smul_bytes(p_ox, p_oy, p_x, p_y, p_k): the scalar p_k is
#     secret, the coordinates public, the outputs secret; and, a second time,
#     every input secret;
#   the functions the constant-time glue calls (twice_d, from_affine, add,
#     to_affine, fe25519 byte and word conversions, carry_sub): every input
#     secret, the output buffer's initial contents public;
#   jasmin_zl_{add,sub,mul}_bytes(p_out, p_a, p_b), jasmin_zl_opp_bytes(p_out,
#     p_a): the inputs and the output secret.
# jasmin-ct then checks that no branch condition and no memory address
# depends on a secret, in the source (pass typing) and after each compiler
# pass given as argument (default: inline unroll lowering propagate; the
# later passes need register allocation, which jasmin-ct runs without
# jasminc's -auto-spill and which fails on these modules).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
CT=${JASMIN_CT:-jasmin-ct}
PASSES=${*:-inline unroll lowering propagate}
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT

annotate() {  # annotate in.jazz out.jazz symbol=signature ...
  python3 - "$@" <<'PY'
import sys
t = open(sys.argv[1]).read()
for a in sys.argv[3:]:
    sym, sig = a.split('=', 1)
    k = 'export fn ' + sym + '('
    assert t.count(k) == 1, sym
    t = t.replace(k, '#[ct = "' + sig + '"]\n' + k)
open(sys.argv[2], 'w').write(t)
PY
}

annotate "$HERE/ed25519_bedrock.jazz" "$T/ed25519_k.jazz" \
  "jasmin_ed25519_smul_bytes=public * public * public * public * secret -> secret * secret" \
  "jasmin_ed25519_twice_d=public -> secret" \
  "jasmin_from_affine=public * secret * secret -> secret" \
  "jasmin_add=public * secret * secret * secret -> secret" \
  "jasmin_to_affine=public * secret -> secret" \
  "jasmin_fe25519_from_bytes=public * secret -> secret" \
  "jasmin_fe25519_to_bytes=public * secret -> secret" \
  "jasmin_fe25519_from_word=public * secret -> secret" \
  "jasmin_fe25519_carry_sub=public * secret * secret -> secret"
annotate "$HERE/ed25519_bedrock.jazz" "$T/ed25519_all.jazz" \
  "jasmin_ed25519_smul_bytes=secret * secret * secret * secret * secret -> secret * secret" \
  "jasmin_ed25519_twice_d=public -> secret" \
  "jasmin_from_affine=public * secret * secret -> secret" \
  "jasmin_add=public * secret * secret * secret -> secret" \
  "jasmin_to_affine=public * secret -> secret" \
  "jasmin_fe25519_from_bytes=public * secret -> secret" \
  "jasmin_fe25519_to_bytes=public * secret -> secret" \
  "jasmin_fe25519_from_word=public * secret -> secret" \
  "jasmin_fe25519_carry_sub=public * secret * secret -> secret"
annotate "$HERE/fieldl_bedrock.jazz" "$T/fieldl.jazz" \
  "jasmin_zl_mul_bytes=public * secret * secret -> secret" \
  "jasmin_zl_add_bytes=public * secret * secret -> secret" \
  "jasmin_zl_sub_bytes=public * secret * secret -> secret" \
  "jasmin_zl_opp_bytes=public * secret -> secret"

status=0
for m in ed25519_k ed25519_all fieldl; do
  for p in typing $PASSES; do
    if "$CT" --compile="$p" "$T/$m.jazz" > "$T/out" 2>&1; then
      echo "$m after $p: constant time"
    else
      echo "$m after $p: rejected"
      grep -v -e deprecated -e '^"[^"]*", line [0-9]* ([0-9-]*)$' "$T/out" | sed 's/^/  /'
      status=1
    fi
  done
done
exit $status
