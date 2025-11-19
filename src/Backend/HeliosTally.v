From Stdlib Require Import Setoid
  Lia Vector Utf8 Fin Permutation
  String.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Crypto Require Import 
  Elgamal EncProof Sigma DecProof
  DistElgamal.
From Frontend Require Import Approval.
Import VectorNotations.

(* This file all the primitives to verify Helios function *)
Section HeliosTally.
  (* Underlying Field of Vector Space *)
  Context 
    {F : Type}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}. 
    (* decidable equality on Field *)

  (* Vector Element *)
  Context 
    {G : Type} 
    {gid : G} 
    {ginv : G -> G}
    {gop : G -> G -> G} 
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.
    (* decidable equality on G *)
    

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  Section Defs.

    Context {n m : nat}
     (g h : G).
    (* A Helios tallysheet  *)
    (* https://vote.heliosvoting.org/helios/elections/a447fe8a-80c8-11ef-923c-7aae6cdba09d/ballots/43156ade-df5c-409d-bdda-0b04e63a6da5/last 
    
   

    Record ballot := mk_ballot {
      cast_at : string;
      ciphertext : Vector.t (G * G) n;
      encryption_proof : Vector.t (@Sigma.sigma_proto F (G * G) 2 3 2) n;
      election_hash : string;
      election_uuid : string;
      vote_hash : string;
      voter_hash : string;
      voter_uuid : string
    }.
    *)

    Definition ballot : Type := (string * Vector.t (G * G) n * 
      Vector.t (@Sigma.sigma_proto F (G * G) 2 3 2) n * 
      string * string * string * string)%type.

    Definition get_ballot_ciphertext (b : ballot) : Vector.t (G * G) n :=
      match b with
      | (_, c, _, _, _, _, _) => c
      end.

    Definition get_ballot_encryption_proof (b : ballot) : 
      Vector.t (@Sigma.sigma_proto F (G * G) 2 3 2) n :=
      match b with
      | (_, _, c, _, _, _, _) => c
      end.

    (*
    https://vote.heliosvoting.org/helios/elections/a447fe8a-80c8-11ef-923c-7aae6cdba09d/trustees/
    decryption_factors	[ (7)[…] ]
    decryption_proofs	[ (7)[…] ]
    email	"maria.naya_plasencia@inria.fr"
    pok	{ challenge: "306214915239604678249840621552418207878444713267", commitment: "8382330916747893209814367850396966737301608245540785224323755492771465124730518883712738605831291155661360592894054961446283…710652092986060404473418754485784689104916788054496403423937019767633277862690348105977368634069292644659422405160557068621", response: "26640980998205482791502950475151259855679473786798972470890567233658919576242" }
    public_key	{ g: "1488749222496318763428242153718604080130400801774349230448173738257193393756872447384710602991504015078403188220609028693866…997131166130259700604433891232298182348403175947450284433411265966789131024573629546048637848902243503970966798589660808533", p: "1632863208493301000238405503380545732960161477118595538973916730908621480040646579903858363495375294167564556218249812075026…899013750306107738002364137917426595737403871114187750804346564731250609196846638183903982387884578266136503697493474682071", q: "61329566248342901292543872769978950870633559608669337131139375508370458778917", … }
    public_key_hash	"Q/dFIZoRuQcmS9B2bKOqv4xicXO1EX//JfX11clQrRM"
    uuid	"d6defeb6-80c8-11ef-923c-7aae6cdba09d"
    
    Record tallier := mk_tallier {
      decryption_factor : Vector.t G n;
      decryption_proof : Vector.t (@Sigma.sigma_proto F G 2 1 1) n;
      email : string;
      pok : @Sigma.sigma_proto F G 1 1 1;
      public_key : G * F * F * G (* g, p, q, y *);
      public_key_hash : string;
      uuid : string
    }.
    *)
    Definition tallier : Type := (Vector.t G n * 
      Vector.t (@Sigma.sigma_proto F G 2 1 1) n * 
      string * (@Sigma.sigma_proto F G 1 1 1) * 
      (G * F * F * G) * string * string)%type.

    Definition get_tallier_decryption_factor (t : tallier) : Vector.t G n :=
      match t with
      | (d, _, _, _, _, _, _) => d
      end.

    
    Definition get_tallier_decryption_proof (t : tallier) : 
      Vector.t (@Sigma.sigma_proto F G 2 1 1) n :=
      match t with
      | (_, p, _, _, _, _, _) => p
      end.

    Definition get_tallier_pok (t : tallier) : 
      @Sigma.sigma_proto F G 1 1 1 :=
      match t with
      | (_, _, _, p, _, _, _) => p
      end.

    Definition get_tallier_public_key (t : tallier) : 
      (G * F * F * G) :=
      match t with
      | (_, _, _, _, pk, _, _) => pk
      end.

    
      


    (* ---------------------------------------------------------------------- *)
    (* The state of the tallying process.

      - [partial us vbs inbs ms] represents an intermediate tally state:
          us   : all ballots seen so far (valid + invalid)
          vbs  : ballots validated as correct (well-formed + proof ok)
          inbs : ballots rejected as invalid
          ms   : current encrypted aggregate (the running encrypted tally)

      - [finished us vbs inbs ts pt b] is the terminal state:
          ts   : talliers’ decryption factors + proofs
          pt   : plaintext tally claimed by the tallysheet
          b    : final verification boolean
    *)
    Inductive state : Type :=
    | partial : list ballot ->  list ballot -> list ballot -> 
      Vector.t (G * G) n -> state
    | finished : list ballot ->  list ballot -> list ballot ->
      Vector.t tallier (1 + m) -> Vector.t F n -> bool -> state.

     
      (* ---------------------------------------------------------------------- *)
      (* Judgment [count s] expresses: “state s is reachable from a correct  
      initial state by applying the tallying rules.”

      The constructors below specify a small-step operational semantics for the
      entire election verification procedure.
    *)

    Inductive count : state -> Type :=
   (* [ax] — Initial state.

      - [ms] is the initial vector of ciphertexts, expected to be (gid, gid)
        for all positions, i.e., an encryption of zero everywhere.

      This rule bootstraps the protocol: no ballots have been seen, validated,
      or rejected yet, and the tally is the neutral encrypted tally.
  *)
    | ax  (ms : Vector.t (G * G) n) :  
      (∀ (i : Fin.t n), Vector.nth ms i = (gid, gid)) -> 
      count (partial (@List.nil ballot) (@List.nil ballot) (@List.nil ballot) ms)
    (* [cvalid] — Processing a **valid ballot**.

      Preconditions:
        - The previous state is a valid partial state.
        - [Permutation us (vbs ++ inbs)] ensures the bookkeeping invariant:
          “us is always exactly the concatenation of vbs and inbs”, up to
          permutation.
        - [verify_encryption_ballot_proof ... = true] certifies that the
          ballot contains a correct ZK proof that its ciphertexts encrypt
          values in {0,1}.
        - [nms = mul_encrypted_ballots ms ctxt] updates the encrypted tally
          homomorphically.

      Postcondition:
        The ballot is added to:
          - [us]   (total seen ballots)
          - [vbs]  (valid ballots)
        And the running encrypted tally is updated.
  *)
    | cvalid (upf : ballot) (us vbs inbs : list ballot) 
      (ms nms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) -> Permutation us (vbs ++ inbs) -> 
      (* upf is valid vote *)
      @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h (zip_with pair (get_ballot_ciphertext upf)
        (get_ballot_encryption_proof upf)) = true ->
      nms = @mul_encrypted_ballots G gop _ ms (get_ballot_ciphertext upf) ->
      count (partial (@List.cons _ upf us) (@List.cons _ upf vbs) inbs nms)
    (* [cinvalid] — Processing an **invalid ballot**.

      Everything is as in [cvalid], except:
        - The ZK proof check returns false.
        - The encrypted tally [ms] is NOT updated.
        - The ballot is appended to [inbs] instead of [vbs].

      This keeps the bookkeeping invariant intact while ignoring the
      contribution of invalid ballots.
  *)
    | cinvalid (upf : ballot) (us vbs inbs : list ballot) 
      (ms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) -> Permutation us (vbs ++ inbs) -> 
      (* upf is invalid vote *)
      @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h (zip_with pair (get_ballot_ciphertext upf) 
        (get_ballot_encryption_proof upf)) = false  ->
      count (partial (@List.cons _ upf us) vbs (@List.cons _ upf inbs) ms)
      (* [finish] — Finalisation rule.

      Once all ballots have been processed, this rule checks the talliers’
      decryptions and the published plaintext tally.

      Arguments:

        us, vbs, inbs : final lists of all / valid / invalid ballots.
        ms            : final encrypted tally.
        ts            : talliers’ public keys, decryption factors, proofs.
        pt            : published plaintext tally.
        ds            : decrypted ciphertexts (computed here).
        bptds         : whether pt matches the recovered ds.
        bdec          : whether all decryption proofs are valid.
        bpok          : whether talliers' POK proofs are valid.
        bhmul         : whether talliers’ public keys multiply to h.
        b             : final boolean = conjunction of all checks.

      Each premise enforces one part of the end-to-end verification:

        - ds = decrypt_ballot_value ... ms factors
              Ensures ds is computed correctly from talliers’ factors.

        - vector_forallb ... = bptds
              Ensures plaintext pt matches decrypted ds.

        - vector_forallb decryption_proof_accepting_conversations_vector = bdec
              Verifies correctness of talliers’ decryption proofs.

        - vector_forallb accepting_conversation = bpok
              Checks talliers' proofs of knowledge of their secret key.

        - Gdec h (product of tallier keys) = bhmul
              Ensures the election public key h matches the talliers'.

        - b = andb bptds (andb bdec (andb bpok bhmul))
              The final verification result.

      If all checks succeed, we reach [finished ...].
    *)
    | finish (us vbs inbs : list ballot) (ms : Vector.t (G * G) n) 
      (ts : Vector.t tallier (1 + m))  (pt : Vector.t F n) (ds : Vector.t G n)
      (bptds bdec bpok bhmul b : bool) :
      count (partial us vbs inbs ms) -> Permutation us (vbs ++ inbs) -> 
      (* ds is the correct decryption *)
      ds = @decrypt_ballot_value G ginv gop _ _ ms 
        (Vector.map  get_tallier_decryption_factor ts) ->
      (* pt is the correct plaintext tally *)
      (vector_forallb (fun u => u) 
        (zip_with (fun u v => match Gdec (g ^ u) v with
        | left _ => true
        | _ => false
        end) pt ds)) = bptds ->
      (* all talliers' decryption factor and proofs are valid *)
      (vector_forallb (fun u => 
        @decryption_proof_accepting_conversations_vector F G ginv gop gpow 
          Gdec _ g (match get_tallier_public_key u with
          | (_, _, _, pk_y) => pk_y
          end) ms (get_tallier_decryption_factor u)
          (get_tallier_decryption_proof u)) ts = bdec) ->
      (* talliers' pok is valid *)
      (vector_forallb (fun u =>
      match get_tallier_public_key u with
      | (_, _, _, pk_y) => 
        @accepting_conversation F G gop gpow Gdec g pk_y 
        (get_tallier_pok u)
      end) ts = bpok) ->
      (* public key h is equal to all public keys of talliers *)
      (match Gdec h (Vector.fold_right gop 
      (Vector.map (fun u => match get_tallier_public_key u with
        | (_, _, _, pk_y) => pk_y
        end) ts) gid) 
      with
      | left _ => true
      | _ => false
      end) = bhmul ->
      b = andb bptds (andb bdec (andb bpok bhmul)) ->
      count (finished us vbs inbs ts pt b). 


    (* walk through the ballots and compute the final tally. 
    Only include valid ballots in the tally  and exclude invalid ballots 
    vbs is the valid ballots and included in the count 
    inbs is the invalid ballots *)
    Definition compute_final_tally :  
      ∀ (bs : list ballot), 
      existsT (vbs inbs :  list ballot)
        (ms : Vector.t (G * G) n), (count (partial bs vbs inbs ms) *
        Permutation bs (vbs ++ inbs))%type.
    Proof.
      (* we walk through the whole bs and and build up a tally bottom-up *)
      refine(fix fn (bs : list ballot) {struct bs} := 
        match bs with 
        | @List.nil _ => _ 
        | @List.cons _ bh bt => _ 
        end).
      + 
        set (ms := repeat_ntimes n (gid, gid)).
        exists (@List.nil ballot), (@List.nil ballot), ms.
        refine(pair (ax ms _) _).
         ++
          intros *.
          unfold ms.
          eapply repeat_ntimes_correct.
        ++
          reflexivity.
      +
        (* check if bh is valid ballot or not *)
        refine 
        (match @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h (zip_with pair (get_ballot_ciphertext bh)
        (get_ballot_encryption_proof bh)) as v 
        return @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
          _ g h (zip_with pair (get_ballot_ciphertext bh)
          (get_ballot_encryption_proof bh)) = v -> existsT (vbs inbs :  list ballot)
          (ms : Vector.t (G * G) n), (count (partial (bh :: bt) vbs inbs ms) *
          Permutation (bh :: bt) (vbs ++ inbs))%type
        with
        | true => fun ha => _
        | false => fun ha => _
        end eq_refl).
        ++
          (* true case *) 
          (* the encryption proof is valid *)
          destruct (fn bt) as [vbs [inbs [ms [Hcount Hperm]]]].
          exists (@List.cons _ bh vbs), inbs.
          set (nms := @mul_encrypted_ballots G gop _ ms (get_ballot_ciphertext bh)).
          exists nms.
          refine(pair _ _).
          * 
            eapply cvalid. exact Hcount.
            exact Hperm.
            exact ha.
            unfold nms.
            exact eq_refl.
          *
            cbn.
            eapply Permutation_cons;
            [reflexivity | exact Hperm].
        ++
          (* false case *)
          (* the encryption proof is invalid *)
          destruct (fn bt) as [vbs [inbs [ms [Hcount Hperm]]]].
          exists vbs, (@List.cons _ bh inbs).
          exists ms.
          refine(pair _ _).
          * 
            eapply cinvalid. exact Hcount.
            exact Hperm.
            exact ha.
          *
            cbn.
            eapply Permutation_trans with (l' := List.cons bh (vbs ++ inbs)).
            eapply Permutation_cons;[
              reflexivity | exact Hperm].
            eapply Permutation_middle.
    Defined.

    (* Forall list of ballots bs, talliers' decryption factors ts, 
      and final tally pt, we can construct an element of type 
      count (finished bs vbs inbs ts pt bfinal). This is called 
      correct by construction. *)
    Definition compute_final_count : 
      ∀ (bs : list ballot) (ts : Vector.t tallier (1 + m)) (pt : Vector.t F n), 
      existsT (bfinal : bool) (vbs inbs : list ballot),
        count (finished bs vbs inbs ts pt bfinal).
    Proof.
      intros *.
      destruct (compute_final_tally bs) as [vbs [inbs [ms [Hcount Hperm]]]].
      set (ds := @decrypt_ballot_value G ginv gop _ _ ms 
        (Vector.map get_tallier_decryption_factor ts)).
      set (bptds := (vector_forallb (fun u => u) 
        (zip_with (fun u v => match Gdec (g ^ u) v with
        | left _ => true
        | _ => false
        end) pt ds))).
      set (bdec := (vector_forallb (fun u => 
        @decryption_proof_accepting_conversations_vector F G ginv gop gpow 
          Gdec _ g (match get_tallier_public_key u with
          | (pk_g, pk_p, pk_q, pk_y) => pk_y
          end) ms (get_tallier_decryption_factor u)
          (get_tallier_decryption_proof u)) ts)).
      set (bpok := (vector_forallb (fun u =>
      match get_tallier_public_key u with
      | (_, _, _, pk_y) => 
        @accepting_conversation F G gop gpow Gdec g pk_y 
        (get_tallier_pok u)
      end) ts)).
      set (bhmul := (match Gdec h (Vector.fold_right gop 
      (Vector.map (fun u => match get_tallier_public_key u with
        | (_, _, _, pk_y) => pk_y
        end) ts) gid) 
      with
      | left _ => true
      | _ => false
      end)).
      set (bfinal := andb bptds (andb bdec (andb bpok bhmul))).
      exists bfinal, vbs, inbs.
      eapply finish with (ms := ms) (ds := ds);
      try assumption.
      + 
        unfold ds.
        exact eq_refl.
      +
        unfold bptds.
        exact eq_refl.
      +
        unfold bdec.
        exact eq_refl.
      +
        unfold bpok.
        exact eq_refl.
      +
        unfold bhmul.
        exact eq_refl.
      +
        unfold bfinal.
        exact eq_refl.
    Defined.

  End Defs.
End HeliosTally.