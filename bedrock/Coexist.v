(* Goal 2: SigmaProtocol's Curve.Ed25519 (vendored fiat-crypto under the
   root Fiat, own theory Sigma) and AUCurves' bedrock2 Edwards XYZT file
   (fiat-crypto under the root Crypto) loaded in one session. *)
From Curve Require Ed25519.
From Sigma Require Sigma.
Require Bedrock.End2End.Ed25519.EdwardsXYZT64.

Check Curve.Ed25519.Ed25519.Ed.xdouble.
Check Curve.Ed25519.Ed25519.Ed.gpow_fast_eq.
Print Curve.Ed25519.Ed25519.Ed.xpoint.
Check Fiat.Spec.Curve25519.E.d.
Check Crypto.Spec.Curve25519.E.d.
Check Bedrock.End2End.Ed25519.EdwardsXYZT64.Ed25519XYZT64.double64_ok.
Print Bedrock.End2End.Ed25519.EdwardsXYZT64.Ed25519XYZT64.spec_of_double64.
