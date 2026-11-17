(** * Primality certificate for the ElectionGuard 2.0 subgroup order *)

(** This file proves that [q = 2^256 - 189], written out in decimal as

[[
115792089237316195423570985008687907853269984665640564039457584007913129639747
]]

is prime. It is the 256-bit order of the subgroup of [Z_p^*] fixed by the
ElectionGuard 2.0 specification (section 3.1.1), where [p] is the 4096-bit
prime of [primePEG.v] and [p - 1 = q·r]. It is used by
[Examples/ElectionGuardIns.v].

The proof is a Pocklington certificate, generated with sympy by the helper
script [bench/pocklington.py] of the repository and checked by reflection
with Coqprime ([Pocklington_refl]). Each [Pock_certif N a factors sqrt]
entry gives a witness base [a] and a factored part of [N - 1] whose
square exceeds [N]; the prime factors in that list, 440208…493, 14220…871,
973591, 87881, 83, 41 and 13, each get their own certificate, down to the
base case [prime2]. The boolean checker is run with [vm_compute]. *)

From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

(** [prime_q_eg]: the ElectionGuard 2.0 subgroup order [q = 2^256 - 189] is
    prime. *)
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
