(* Pocklington certificate for q = 2^256 - 189, the order of the
   ElectionGuard 2.0 group, generated with sympy (bench/pocklington.py). *)
From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma prime_q_eg : prime 115792089237316195423570985008687907853269984665640564039457584007913129639747.
Proof.
 apply (Pocklington_refl
  (Pock_certif 115792089237316195423570985008687907853269984665640564039457584007913129639747 2 ((440208639276132997491800604758226661590679912188273141493, 1)::(2, 1):: nil) 1)
  (Pock_certif 440208639276132997491800604758226661590679912188273141493 2 ((14220365526706201077871, 1)::(2, 2):: nil) 42838182102817719206930 ::
   Pock_certif 14220365526706201077871 3 ((973591, 1)::(87881, 1)::(2, 1):: nil) 1 ::
   Pock_certif 973591 3 ((83, 1)::(2, 1):: nil) 220 ::
   Pock_certif 87881 3 ((13, 3)::(2, 3):: nil) 1 ::
   Pock_certif 83 2 ((41, 1)::(2, 1):: nil) 1 ::
   Pock_certif 41 3 ((2, 3):: nil) 1 ::
   Pock_certif 13 2 ((2, 2):: nil) 1 ::
   Proof_certif 2 prime2 ::
   nil)).
 vm_cast_no_check (refl_equal true).
Qed.

