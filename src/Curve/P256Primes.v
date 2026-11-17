(** * Primality of the NIST P-256 parameters *)

(** Machine-checked primality proofs for the two primes of the NIST P-256
    curve (FIPS 186-4, SEC 2 secp256r1):

    - [prime_p256_p]: the field modulus
      [p = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1];
    - [prime_p256_n]: the group order [n] of the base point.

    Each proof is a Pocklington certificate in the format of the Coqprime
    library. A [Pock_certif N a factors r] entry asserts that [N] is prime
    because [a] is a Pocklington witness for [N] with respect to a partial
    factorisation ([factors], a list of (prime, exponent) pairs) of [N - 1];
    the list chains such certificates down to the base case [prime_2], so
    every prime factor used is itself certified. [Pocklington_refl] reduces
    the claim to a boolean check, which is evaluated by the kernel's virtual
    machine ([vm_cast_no_check] defers the conversion check to [Qed]; the
    check is still performed by the kernel). The certificates were generated
    externally; only their verification is trusted to Rocq.

    These lemmas are used in [Curve/P256.v] to build the scalar field [Z_n]
    and the base field [F_p]. *)
From Stdlib Require Import ZArith Znumtheory List. Import ListNotations.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.
Local Open Scope positive_scope.

(** The P-256 field modulus [p] is prime. *)
Lemma prime_p256_p : prime 115792089210356248762697446949407573530086143415290314195533631308867097853951.
Proof.
 simple refine (Pocklington_refl
  (Pock_certif 115792089210356248762697446949407573530086143415290314195533631308867097853951 3 ((835945042244614951780389953367877943453916927241, 1)::(2, 1):: nil) 1)
  (Pock_certif 835945042244614951780389953367877943453916927241 7 ((774023187263532362759620327192479577272145303, 1)::(2, 3):: nil) 1 ::
   Pock_certif 774023187263532362759620327192479577272145303 3 ((46076956964474543, 1)::(2, 1):: nil) 171713375463676744 ::
   Pock_certif 46076956964474543 5 ((704251, 1)::(2, 1):: nil) 2397572 ::
   Pock_certif 704251 2 ((313, 1)::(2, 1):: nil) 1 ::
   Pock_certif 313 5 ((2, 3):: nil) 5 ::
   Proof_certif 2 prime_2 ::
   nil) _).
 vm_cast_no_check (@eq_refl bool true).
Qed.

(** The P-256 group order [n] is prime. *)
Lemma prime_p256_n : prime 115792089210356248762697446949407573529996955224135760342422259061068512044369.
Proof.
 simple refine (Pocklington_refl
  (Pock_certif 115792089210356248762697446949407573529996955224135760342422259061068512044369 7 ((2624747550333869278416773953, 1)::(2, 4):: nil) 37018846469043163594359850612)
  (Pock_certif 2624747550333869278416773953 5 ((208150935158385979, 1)::(2, 6):: nil) 1 ::
   Pock_certif 208150935158385979 2 ((191039911, 1)::(2, 1):: nil) 1 ::
   Pock_certif 191039911 3 ((155317, 1)::(2, 1):: nil) 1 ::
   Pock_certif 155317 2 ((43, 2)::(2, 2):: nil) 1 ::
   Pock_certif 43 2 ((7, 1)::(2, 1):: nil) 1 ::
   Pock_certif 7 3 ((2, 1):: nil) 1 ::
   Proof_certif 2 prime_2 ::
   nil) _).
 vm_cast_no_check (@eq_refl bool true).
Qed.
