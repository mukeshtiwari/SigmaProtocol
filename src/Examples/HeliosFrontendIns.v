From Stdlib Require Import Utf8 ZArith Vector Psatz.
From Crypto Require Import Sigma EncProof Elgamal.
From Frontend Require Import Approval.
From Utility Require Import Zpstar Util.
From Examples Require Import HeliosTallyIns.
Import Vspace Schnorr Zpfield Zpgroup VectorNotations.

(* Frontend (voting-client) functions instantiated at the 2048-bit
   Helios parameters from HeliosTallyIns. Used to benchmark ballot
   encryption and proof generation at real-world parameters. *)

Section HeliosFrontend.

  Definition helios_encrypt_ballot {n : nat} (h : @Schnorr_group p q)
    (rs ms : Vector.t (@Zp q) n) :
    Vector.t (@Schnorr_group p q * @Schnorr_group p q) n.
  Proof.
    refine(@encrypt_ballot (@Zp q) (@Schnorr_group p q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow k p q safe_prime prime_p prime_q)
      _ g h rs ms).
    all: (try eapply prime_q).
    all: (try eapply prime_p).
    all: (try eapply safe_prime).
  Defined.

  Definition helios_encrypt_ballot_and_generate_enc_proof {n : nat}
    (h : @Schnorr_group p q)
    (rs ms : Vector.t (@Zp q) n)
    (uscs : Vector.t (Vector.t (@Zp q) 3) n)
    (c : Vector.t (@Zp q) n) :
    Vector.t ((@Schnorr_group p q) * (@Schnorr_group p q) *
      @Sigma.sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n.
  Proof.
    refine(@encrypt_ballot_and_generate_enc_proof (@Zp q)
      Zpfield.zero Zpfield.one zp_add zp_mul zp_sub
      zp_opp zp_dec (@Schnorr_group p q)
      (@inv_schnorr_group k p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow k p q safe_prime prime_p prime_q) _
      g h rs ms uscs c).
    all: (try eapply prime_q).
    all: (try eapply prime_p).
    all: (try eapply safe_prime).
  Defined.

  Definition helios_generate_ballot_commitment {n : nat}
    (h : @Schnorr_group p q)
    (rs ms : Vector.t (@Zp q) n)
    (uscs : Vector.t (Vector.t (@Zp q) 3) n) :
    Vector.t (Vector.t (@Schnorr_group p q * @Schnorr_group p q) 2) n.
  Proof.
    set (cp := helios_encrypt_ballot h rs ms).
    refine(Vector.map (fun '(uscs', cp') =>
      @construct_encryption_proof_elgamal_commitment
      (@Zp q) zp_opp (@Schnorr_group p q)
      (@inv_schnorr_group k p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow k p q safe_prime prime_p prime_q) 1 0 uscs'
      [(@pow k p q safe_prime prime_p prime_q) g Zpfield.zero;
       (@pow k p q safe_prime prime_p prime_q) g Zpfield.one] g h cp')
      (zip_with (fun u v => (u, v)) uscs cp)).
    all: (try eapply prime_q).
    all: (try eapply prime_p).
    all: (try eapply safe_prime).
  Defined.

  (* unfold a vector of commitment pairs into a flat vector of
     group elements, used as input to the random oracle *)
  Definition helios_vector_unfold : ∀ {n : nat},
    Vector.t (Vector.t (@Schnorr_group p q * @Schnorr_group p q) 2) n ->
    Vector.t (@Schnorr_group p q) (4 * n).
  Proof.
    refine
    (fix fn {n : nat} (v : Vector.t (Vector.t (@Schnorr_group p q * @Schnorr_group p q) 2) n) :
      Vector.t ((@Schnorr_group p q)) (4 * n) :=
      match v as v' in Vector.t _ n' return
        Vector.t ((@Schnorr_group p q)) (4 * n')
      with
      | [] =>  []
      | @Vector.cons _ vh nt vt =>
         let ret := fn vt in _
      end).
    assert (ha : 4 * S nt = 4 + 4 * nt). nia.
    rewrite ha; clear ha.
    destruct (vector_inv_S vh) as ((vha, vhb) & vht & _).
    destruct (vector_inv_S vht) as ((vhta, vhtb) & _ & _).
    exact (vha :: vhb :: vhta :: vhtb :: ret).
  Defined.

  Definition helios_nizk_encrypt_ballot_and_generate_enc_proof {n : nat}
    (fn : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> Vector.t (@Zp q) n)
    (h : @Schnorr_group p q)
    (rs ms : Vector.t (@Zp q) n)
    (uscs : Vector.t (Vector.t (@Zp q) 3) n) :
    Vector.t ((@Schnorr_group p q) * (@Schnorr_group p q) *
      @Sigma.sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n.
  Proof.
    set (comm := helios_generate_ballot_commitment h rs ms uscs).
    set (c := fn _ ([inl p; inl q; inr g; inr h] ++
      Vector.map inr (helios_vector_unfold comm))).
    exact(helios_encrypt_ballot_and_generate_enc_proof h rs ms uscs c).
  Defined.

  Definition helios_verify_encryption_ballot_proof {n : nat}
    (h : @Schnorr_group p q)
    (proof : Vector.t ((@Schnorr_group p q) * (@Schnorr_group p q) *
    @Sigma.sigma_proto (@Zp q)
    (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n) : bool.
  Proof.
    refine(@verify_encryption_ballot_proof (@Zp q)
      Zpfield.zero Zpfield.one zp_add zp_dec
      (@Schnorr_group p q)
      (@inv_schnorr_group k p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow k p q safe_prime prime_p prime_q)
      Schnorr.dec_zpstar _ g h proof).
    all: (try eapply prime_q).
    all: (try eapply prime_p).
    all: (try eapply safe_prime).
  Defined.

End HeliosFrontend.
