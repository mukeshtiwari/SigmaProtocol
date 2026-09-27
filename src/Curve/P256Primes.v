(* Pocklington certificates for the P-256 (secp256r1) field prime p and
   group order n, generated with bench/pocklington.py (Z-based checker of
   Coqprime.PrimalityTest.PocklingtonCertificat, no axioms):
     pocklington.py "2**256-2**224+2**192+2**96-1" prime_p256_p
     pocklington.py "0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551" prime_p256_n *)
From Stdlib Require Import ZArith Znumtheory List. Import ListNotations.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.
Local Open Scope positive_scope.

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

