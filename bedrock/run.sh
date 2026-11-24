#!/bin/bash
# Compile one file of the Ed25519 bedrock2 bridge:  bedrock/run.sh File.v
#   SIGMA_SRC  the dune build of this repository (default: _build/default/src)
#   AUCURVES   AUCurves' fiat-crypto and bedrock2 builds, laid out as
#              $AUCURVES/fiat (logical root Crypto) and $AUCURVES/bed
#              (logical root Bedrock), with EdwardsXYZT64.v and
#              Field25519_64.v compiled; Affine.v also needs fiat-crypto's
#              Arithmetic/FLia.v, Bedrock/Field/Interface/Compilation2.v and
#              Bedrock/Group/AdditionChains.v (the verified fe25519_inv)
#              compiled under $AUCURVES/fiat; FieldL.v also needs
#              fiat-crypto's Bedrock/Field/Synthesis/New/WordByWordMontgomery.v
#              (with PushButtonSynthesis/WordByWordMontgomery.v and its
#              reification caches) compiled there
# The files load this library (root Sigma, vendored fiat-crypto root Fiat) and
# AUCurves' fiat-crypto (root Crypto) in one session; FieldTransport.v relates
# their coordinate fields Zmod p and F p, ExecDouble.v states AUCurves'
# verified bedrock2 doubling in terms of this library's extended points,
# ExecReadd.v its readdition (addition up to projective equality),
# ToCached2.v a halving-free cached-point preparation [to_cached2] and the
# addition [add] of two run-time points by [to_cached2] and [readd],
# Affine.v the conversions [from_affine] and [to_affine] (the latter with
# fiat-crypto's verified inversion), ScalarMult.v a double-and-add scalar
# multiplication [scalarmult] over [double] and [add], related to
# [Ed.gpow_fast], ScalarMultCT.v its constant-time variant [scalarmult_ct]
# (both the double and the sum are computed each iteration and selected by a
# masked word-wise copy [cmov]), SmulBytes.v the byte-level entry point
# [ed25519_smul_bytes] (coordinates and scalar as 32-byte encodings, the
# constant 2d computed inside by [ed25519_twice_d]), related to
# [Ed.gpow_fast], and EmitC.v prints these functions and the field operations
# they call as C (ed25519_bedrock.out), with the theorem
# [ed25519_smul_bytes_e2e] for the printed list of functions.
# FieldL.v derives the arithmetic modulo the group order l (64-bit
# word-by-word Montgomery, fiat-crypto's pipeline), ExecFieldL.v states it on
# this library's scalar field Zl.F = Zmod l, ZlBytes.v composes it into
# byte-level operations [zl_add_bytes], [zl_sub_bytes], [zl_mul_bytes],
# [zl_opp_bytes] on 32-byte encodings, and EmitFieldL.v prints these as C
# (fieldl_bedrock.out).
set -euo pipefail
cd "$(dirname "$0")"
S=${SIGMA_SRC:-../_build/default/src}
: "${AUCURVES:?set AUCURVES to the directory holding fiat/ and bed/}"
ulimit -s unlimited
rocq compile -q -native-compiler no -async-proofs-tac-j 0 \
  -Q "$S/Algebra" Algebra -Q "$S/Utility" Utility -Q "$S/Probability" Probability \
  -Q "$S/Fiat" Fiat -Q "$S/Curve" Curve -Q "$S/Crypto" Sigma \
  -R "$AUCURVES/fiat" Crypto -R "$AUCURVES/bed" Bedrock -Q . Bridge "$@"
