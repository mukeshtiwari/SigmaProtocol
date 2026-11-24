#!/bin/bash
# Compile one file of the Ed25519 bedrock2 bridge:  bedrock/run.sh File.v
#   SIGMA_SRC  the dune build of this repository (default: _build/default/src)
#   AUCURVES   AUCurves' fiat-crypto and bedrock2 builds, laid out as
#              $AUCURVES/fiat (logical root Crypto) and $AUCURVES/bed
#              (logical root Bedrock), with EdwardsXYZT64.v and
#              Field25519_64.v compiled
# The files load this library (root Sigma, vendored fiat-crypto root Fiat) and
# AUCurves' fiat-crypto (root Crypto) in one session; FieldTransport.v relates
# their coordinate fields Zmod p and F p, ExecDouble.v states AUCurves'
# verified bedrock2 doubling in terms of this library's extended points,
# ExecReadd.v its readdition (addition up to projective equality).
set -euo pipefail
cd "$(dirname "$0")"
S=${SIGMA_SRC:-../_build/default/src}
: "${AUCURVES:?set AUCURVES to the directory holding fiat/ and bed/}"
ulimit -s unlimited
rocq compile -q -native-compiler no -async-proofs-tac-j 0 \
  -Q "$S/Algebra" Algebra -Q "$S/Utility" Utility -Q "$S/Probability" Probability \
  -Q "$S/Fiat" Fiat -Q "$S/Curve" Curve -Q "$S/Crypto" Sigma \
  -R "$AUCURVES/fiat" Crypto -R "$AUCURVES/bed" Bedrock -Q . Bridge "$@"
