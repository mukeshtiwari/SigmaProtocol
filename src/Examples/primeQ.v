(** * Primality certificate for the 256-bit Helios subgroup order q *)

(** This file proves that the 256-bit integer

[[
q = 61329566248342901292543872769978950870633559608669337131139375508370458778917
]]

is prime. It is the order of the subgroup of [Z_p^*] used by the default
ElGamal parameters of Helios, where [p] is the 2048-bit prime of
[primeP.v] and [p = k·q + 1]. The same group is used by the Helios tally
instance ([Examples/HeliosTallyIns.v]) and by the Verificatum instance
([Examples/VerificatumIns.v]).

The proof is a Pocklington certificate checked by reflection with Coqprime.
Pocklington's criterion states that [N] is prime if some factored part [F] of
[N - 1] with [F² > N] admits a witness [a] with [a^(N-1) ≡ 1 mod N] and
[gcd(a^((N-1)/r) - 1, N) = 1] for every prime [r] dividing [F]. Each
[Pock_certif N a factors sqrt] entry records the base [a], the factored
part of [N - 1] as a list of (prime, exponent) pairs and an auxiliary
square-root hint; each smaller prime factor in turn carries its own
certificate, and the small primes 2 to 139 are closed by Coqprime's
precomputed lemmas. [Pocklington_refl] reduces the whole chain to a
boolean check, evaluated with [vm_compute] (via [vm_cast_no_check]). *)

From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

(** [prime_q]: the Helios subgroup order [q] is prime, by the Pocklington
    certificate described above. *)
Lemma prime_q : prime 61329566248342901292543872769978950870633559608669337131139375508370458778917.
Proof.
 apply (Pocklington_refl
         (Pock_certif 61329566248342901292543872769978950870633559608669337131139375508370458778917 5 ((6350820103, 1)::(4223919769, 1)::(97, 1)::(23, 1)::(7, 1)::(3, 3)::(2,2)::nil) 23858495663773412360561306)
        ((Pock_certif 6350820103 3 ((32074849, 1)::(2,1)::nil) 1) ::
         (Pock_certif 4223919769 7 ((139, 1)::(2,3)::nil) 2117) ::
         (Pock_certif 32074849 17 ((3, 2)::(2,5)::nil) 199) ::
         (Proof_certif 139 prime139) ::
         (Proof_certif 97 prime97) ::
         (Proof_certif 23 prime23) ::
         (Proof_certif 7 prime7) ::
         (Proof_certif 3 prime3) ::
         (Proof_certif 2 prime2) ::
          nil)).
 vm_cast_no_check (refl_equal true).
Qed.
