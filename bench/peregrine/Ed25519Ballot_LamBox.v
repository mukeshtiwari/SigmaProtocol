(** * The approval ballot at Ed25519, extracted to λ□ for Peregrine's C backend

    The fixed 7-candidate ballot of [Ballot_LamBox.v] (encryption and 0-or-1
    proofs), in the prime-order group of Ed25519 ([Curve/Ed25519.v], scalar
    multiplication [Ed.gpow_fast]) with the base point [g] and the public key
    [h = 3 g] of [Examples/Ed25519Ins.v]. The scalars are those of
    [Helios2048Defs.v] reduced modulo the group order [l].

    [ed25519_verify] must print [true]; [ed25519_forged] swaps the two
    components of every ciphertext and must print [false]; [ed25519_digest]
    packs every number of the ballot (the affine coordinates of its points and
    its scalars) into one integer, 256 bits each, so that two compilations of
    the ballot can be compared on their output. Each entry point reads its
    result in a [match], so that Peregrine's dead-code elimination keeps the
    computation.

    The ballot is computed by the prover without a branch on the votes
    ([encrypt_ballot_and_generate_enc_proof_ct_ins]), from secrets given by
    [secret], and every value of the ballot passes through [publish_F] or
    [publish_G]. The constant-time build of [build.sh] (programs [*_ct])
    replaces [secret] by a function reading a buffer of bytes, the
    publication functions by declassification for valgrind's memcheck, and
    the scalars, points and their operations by 32- and 64-byte values and
    verified bedrock2 code. [ed25519_branching_digest] is the digest of the
    same ballot computed by the prover that branches on the votes, a
    control for that test. *)
From Stdlib Require Import ZArith Zmod Vector List.
From Curve Require Import Ed25519.
From Sigma Require Import Sigma.
From Examples Require Import Ed25519Ins.
From Peregrine.Plugin Require Import Loader.
Import Ed25519 VectorNotations.

Module Ed25519Ballot.

  Local Notation F := Zl.F.
  Local Notation G := Ed.G.

  (** A scalar from its integer representative. *)
  Definition s (z : Z) : F := of_Z z.

  (** The secret scalars of the ballot, in this order: the encryption
      randomness of the seven votes (indices 0 to 6), the votes (7 to 13),
      the proof randomness of each vote (commitment exponents and simulated
      challenge, 14 to 34) and the decryption key [x = 3] of
      [Examples/Ed25519Ins.v] (35). [gen_secrets.py] reads this list to
      build the secret input of the constant-time build. (A list: Peregrine's
      erasure of a vector literal of this length takes too long.) *)
  Definition secrets : list F :=
    (s 1683376730399275664522599405009454118513405217930488150353475658559999300036 ::
     s 5155043013974961047699678904619379724306680916079161635487800538311564990502 ::
     s 3220613530292467455295148401934293656273200679932433399759454335318993973239 ::
     s 5381944221669096069370962904913584813501760050305818886175735501457987651267 ::
     s 2538727342298837510820520063198872278307669877555811445236853162198190299289 ::
     s 4999702740104418494152807927976580484714439170278564221602720526218082315986 ::
     s 554480601557843661269880427784192405151995328751607868635188743039427436908 ::
     s 1 ::
     s 0 ::
     s 1 ::
     s 0 ::
     s 1 ::
     s 1 ::
     s 0 ::
     s 1842287122955118845886144128824665310743055824495230831982489593993063855031 ::
     s 2309800207884843084616273193428263558991837744054038317558104945598945324622 ::
     s 1364347561950295892850738071349846664478244569890385528294345855247260599110 ::
     s 6486191323308865580804578711279738793665590272667180505508744822666534736157 ::
     s 4050638425680413764040738446051195332771350106076429047724754723223528681215 ::
     s 3839405539871984760044179926670719094411450170877449670513462800450588966895 ::
     s 7111237969449476459265818250687441935305612195714021441928560457996928924936 ::
     s 5845273331300740958022292611056484369238652574082028051600427065851512379185 ::
     s 6180007682113933634079295372182835474074582319194835822303022249455876468458 ::
     s 7054112363136963452827300411388209559011637964653073497950403128535142203199 ::
     s 176687192850760116290699120076045950202478159928929065132178462734038433717 ::
     s 832642807261969651737710755843279206580494383667266661818410112103981303452 ::
     s 3637372052788598466420146433043537929916209138616999720534878254835941808727 ::
     s 5548119983324162586727272245568218143502350436577033995359091515765722465607 ::
     s 3685175928145089308118246312898951853896299819703942862795351930175958492173 ::
     s 7018468225341733097758751788831699401447771956569948043173404986782995756827 ::
     s 473597841020529975344002251489941126158407350409723456201788962692351964276 ::
     s 2909631896802061410873353565488564116530439607515790551569984538381756447861 ::
     s 1708842438543908929142226980949167446672898799427190374644070389338572201636 ::
     s 3637499688209730735346489100134175564791424479652034023347516805455673109494 ::
     s 4589664988749278980216261963496455562658755590938286581565825375159485682238 ::
     s 3 :: nil)%list.

  (** The [i]-th secret scalar. The constant-time build (programs [*_ct]
      of [build.sh]) replaces this function by one that reads the [i]-th
      32-byte entry of a buffer, so that the secrets enter the C program
      as bytes. *)
  Definition secret (i : nat) : F := List.nth i secrets Zl.zero.

  (** The fixed encryption randomness of the seven votes. *)
  Definition bench_rs : Vector.t F 7 :=
    [secret 0; secret 1; secret 2; secret 3; secret 4; secret 5; secret 6].

  (** The fixed approvals (1, 0, 1, 0, 1, 1, 0). *)
  Definition bench_ms : Vector.t F 7 :=
    [secret 7; secret 8; secret 9; secret 10; secret 11; secret 12; secret 13].

  (** The fixed proof randomness (commitment exponents and simulated
      challenge) of each 0-or-1 proof. *)
  Definition bench_uscs : Vector.t (Vector.t F 3) 7 :=
    [[secret 14; secret 15; secret 16];
     [secret 17; secret 18; secret 19];
     [secret 20; secret 21; secret 22];
     [secret 23; secret 24; secret 25];
     [secret 26; secret 27; secret 28];
     [secret 29; secret 30; secret 31];
     [secret 32; secret 33; secret 34]].

  (** The fixed challenges of the seven proofs. *)
  Definition bench_cs : Vector.t F 7 :=
    [s 3497024620016564272261708509335678011571590718658911013602117402169906125166; s 127928903253224512842234093786879975705891910327554517013979295977619600038; s 697222428066774064688836702697866616436597850385289362215903730256225742585; s 2256024421933871660138955862469534973938614353800078831257859192314108578477; s 1246582288939022370373363375929094965275492523497321760079073344698489439024; s 680658134655224210000291942810198806724493654693369488326736068988387634399; s 4340032650012244201744696889716417043643543429250080387477375763914788985751].

  (** Publication of a scalar and of a point: the identity. The
      constant-time build replaces both by functions that declare their
      argument public (for valgrind's memcheck, see [main_ct.c]); every
      value of a ballot passes through them before it is output. *)
  Definition publish_F (x : F) : F := x.
  Definition publish_G (x : G) : G := x.

  (** Publication of an encrypted vote with its proof. *)
  Definition publish_vote (v : G * G * @sigma_proto F (G * G) 2 3 2) :
    G * G * @sigma_proto F (G * G) 2 3 2 :=
    match v with
    | (c1, c2, pf) =>
        (publish_G c1, publish_G c2,
         mk_sigma _ _ _
           (Vector.map (fun '(a, b) => (publish_G a, publish_G b)) (announcement pf))
           (Vector.map publish_F (challenge pf))
           (Vector.map publish_F (response pf)))
    end.

  (** Encryption and proofs of the full 7-candidate ballot, by the prover
      without a branch on the votes; it equals
      [encrypt_ballot_and_generate_enc_proof_ins bench_rs bench_ms bench_uscs
      bench_cs] since the votes are 0 or 1
      ([encrypt_ballot_and_generate_enc_proof_ct_ins_eq]). *)
  Definition ballot_bench :=
    Vector.map publish_vote
      (encrypt_ballot_and_generate_enc_proof_ct_ins bench_rs bench_ms bench_uscs bench_cs).

  (** Verification of [ballot_bench] (expected [true]). *)
  Definition ballot_verify_bench : bool :=
    verify_encryption_ballot_proof_ins ballot_bench.

  (** The numbers of a ballot, in order: for each vote the two components
      of its ciphertext, the announcement of its proof (coordinates [x],
      [y] of every point), its challenges and its responses. *)
  Definition point_nums (P : G) : list Z :=
    let (x, y) := point_to_Z P in (x :: y :: nil)%list.
  Definition pair_nums (c : G * G) : list Z :=
    (point_nums (fst c) ++ point_nums (snd c))%list.
  Definition vote_nums (v : G * G * @sigma_proto F (G * G) 2 3 2) : list Z :=
    match v with
    | (c1, c2, pf) =>
        point_nums c1 ++ point_nums c2 ++
        List.flat_map pair_nums (Vector.to_list (announcement pf)) ++
        List.map to_Z (Vector.to_list (challenge pf)) ++
        List.map to_Z (Vector.to_list (response pf))
    end%list.

  (** The numbers [z_1, ..., z_k] (each below [2^256]) as the integer whose
      256-bit digits, most significant first, are [1, z_1, ..., z_k]. *)
  Definition pack (zs : list Z) : Z :=
    List.fold_left (fun acc z => Z.lor (Z.shiftl acc 256) z) zs 1%Z.

  Definition digest_of (b : Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) 7) : Z :=
    pack (List.flat_map vote_nums (Vector.to_list b)).

  Definition ballot_digest : Z := digest_of ballot_bench.

  (** The ballot by the prover [encrypt_ballot_and_generate_enc_proof_ins],
      which branches on each vote; a control for the constant-time test,
      which must report these branches. *)
  Definition ballot_bench_branching :=
    Vector.map publish_vote
      (encrypt_ballot_and_generate_enc_proof_ins bench_rs bench_ms bench_uscs bench_cs).

End Ed25519Ballot.

(** Swap the two components of every ciphertext of a ballot. *)
Definition swap_ballot {G P : Type} {n : nat} (b : Vector.t (G * G * P) n) :
  Vector.t (G * G * P) n :=
  Vector.map (fun x => match x with (c1, c2, pf) => (c2, c1, pf) end) b.

(** The [return] clauses keep the elaborator from abstracting the
    scrutinee in the result type, which would compute the ballot by
    conversion. *)
Definition ed25519_verify : bool :=
  if Ed25519Ballot.ballot_verify_bench return bool then true else false.
Definition ed25519_forged : bool :=
  if verify_encryption_ballot_proof_ins (swap_ballot Ed25519Ballot.ballot_bench)
  return bool then true else false.
Definition ed25519_digest : Z :=
  match Ed25519Ballot.ballot_digest return Z with Z0 => Z0 | z => z end.

Peregrine Extract "ed25519_verify.ast" ed25519_verify.
Peregrine Extract "ed25519_forged.ast" ed25519_forged.
Definition ed25519_branching_digest : Z :=
  match Ed25519Ballot.digest_of Ed25519Ballot.ballot_bench_branching return Z with
  | Z0 => Z0 | z => z end.

Peregrine Extract "ed25519_digest.ast" ed25519_digest.
Peregrine Extract "ed25519_branching_digest.ast" ed25519_branching_digest.

