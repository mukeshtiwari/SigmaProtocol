From Stdlib Require Import Setoid
  setoid_ring.Field Psatz Vector Utf8 Fin Lia ZArith List FunctionalExtensionality.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space Product_space.
From Utility Require Import 
  Util.
From Crypto Require Import 
  Elgamal EncProof OrSigmaGen Sigma ChaumPedersen DecProof.
From Frontend Require Import Approval Schulze.
From Probability Require Import Prob Distr.
From Stdlib Require Import Permutation.
Import VectorNotations.

(* Receipt-free Schulze tally.

   SchulzeZ is the plaintext reference: defeat strengths, the 
   closure certificate cert_ok, Schulze winners, and the theorem that a 
   certificate characterises the min-max closure (cert_ok_is_closure, 
   closure_unique). Part 2 is the cryptographic tally: the trustees prove 
   the certificate on encrypted margins without decrypting them publicly.

   Encrypted tally. Everything is an ElGamal ciphertext under the trustees'
   key (g, h), h = g^x, and every statement is a membership proof of a 
   plaintext in a small set (EncProof) or a disjunction of two such 
   statements (OrSigmaGen over the product group G × G, branch k being the 
   Schnorr statement (c₁, c₂ / m_k) = (g, h)^r for its own ciphertext 
   (c₁, c₂) and message m_k). N is the number of ballots, K = 2N + 1.

   1. Fresh margins: the trustees publish Enc'(D_ij) with randomness they 
      know and prove with DecProof that Enc'(D_ij) / Enc(D_ij) decrypts to 
      the identity. All later statements are on ciphertexts whose randomness 
      the trustees know.
   2. Defeats: Enc(d_ij) with d_ij ∈ {0..N} (EncProof) and the disjunction, 
      with Δ = D_ij - D_ji,
        (K d_ij + Δ ∈ {-N..0})  ∨  (K (d_ij - D_ij) + Δ ∈ {1..N}),
      an OrSigmaGen with S N + N branches. Since d_ij, D_ij, D_ji ∈ [0, N], 
      the first branch forces d_ij = 0 ∧ Δ ≤ 0 and the second 
      d_ij = D_ij ∧ Δ ≥ 1: this is 
        (D_ji - D_ij ∈ {0..N} ∧ d_ij = 0) ∨ (D_ij - D_ji ∈ {1..N} ∧ d_ij = D_ij).
   3. Closure: Enc(p_ij); p_ij - d_ij ∈ {0..N} (EncProof); for all i, j, k 
      the disjunction (p_ij - p_ik ∈ {0..N}) ∨ (p_ij - p_kj ∈ {0..N}) 
      (OrSigmaGen, S N + S N branches); and for every pair a witness path 
      i → ... → j with d_uv - p_ij ∈ {0..N} on every edge (EncProof). A 
      witness is required for every pair, also when p_ij = 0, where the 
      direct edge always works.
   4. Winner: p_wj - p_jw ∈ {0..N} for every j.

   All challenges are supplied by the caller (interactive form, as in 
   Approval.v); nizk_generate_tally and nizk_verify_tally derive them by
   Fiat-Shamir. *)

(* ------------------------------------------------------------------ *)
(* Part 1: the plaintext Schulze method and the closure certificate     *)
(* ------------------------------------------------------------------ *)

Section SchulzeZ.
  Local Open Scope Z_scope.
  Context {m : nat}.
  Local Notation node := (Fin.t m).
  Local Notation matrix := (node -> node -> Z).

  (* defeat strength: D i j when i beats j, else 0 *)
  Definition defeat (D : matrix) (i j : node) : Z :=
    if Z.ltb (D j i) (D i j) then D i j else 0.

  (* strength of the walk u → v₁ → ... → vₖ (l = [v₁; ...; vₖ], k ≥ 1):
     the minimum of its edges; 0 for the empty walk *)
  Fixpoint strength (d : matrix) (u : node) (l : list node) : Z :=
    match l with
    | List.nil => 0
    | List.cons v l' => 
      match l' with
      | List.nil => d u v
      | _ => Z.min (d u v) (strength d v l')
      end
    end.

  (* a path from i to j: the vertex sequence i :: l, l ≠ [], ending in j *)
  Definition path_from_to (i j : node) (l : list node) : Prop :=
    match l with
    | List.nil => False
    | List.cons u l' => u = i ∧ l' <> List.nil ∧ List.last l' i = j
    end.

  Definition path_strength (d : matrix) (l : list node) : Z :=
    match l with
    | List.nil => 0
    | List.cons u l' => strength d u l'
    end.

  (* the closure certificate: p dominates d, is closed under one-step 
     extension, and every entry is realised by a witness path *)
  Definition cert_ok (d p : matrix) (paths : node -> node -> list node) : Prop :=
    (∀ i j, d i j <= p i j) ∧
    (∀ i j k, Z.min (p i k) (p k j) <= p i j) ∧
    (∀ i j, path_from_to i j (paths i j) ∧ p i j <= path_strength d (paths i j)).

  Definition schulze_winner (p : matrix) (w : node) : Prop := 
    ∀ j, p j w <= p w j.

  (* p is the min-max closure of d: p i j is the largest strength of a 
     path from i to j, or 0 when no path has positive strength *)
  Definition is_closure (d p : matrix) : Prop :=
    ∀ i j, 
      0 <= p i j ∧
      (∀ l, path_from_to i j l -> path_strength d l <= p i j) ∧
      (0 < p i j -> ∃ l, path_from_to i j l ∧ p i j <= path_strength d l).

  Lemma last_default : ∀ (l : list node) (a b : node), 
    l <> List.nil -> List.last l a = List.last l b.
  Proof.
    induction l as [| x l ih]; intros a b h; [contradiction |].
    destruct l as [| y l]; [reflexivity |].
    cbn; apply ih; discriminate.
  Qed.

  Lemma strength_cons : ∀ (d : matrix) (u v w : node) (l : list node),
    strength d u (v :: w :: l)%list = Z.min (d u v) (strength d v (w :: l)%list).
  Proof. reflexivity. Qed.

  Lemma strength_le : ∀ (d p : matrix),
    (∀ i j, d i j <= p i j) -> (∀ i j k, Z.min (p i k) (p k j) <= p i j) ->
    ∀ (l : list node) (u j : node), 
    l <> List.nil -> List.last l u = j -> strength d u l <= p u j.
  Proof.
    intros d p h1 h2 l; induction l as [| v l' ih]; intros u j hne hl.
    + contradiction.
    + destruct l' as [| w l''].
      - cbn in hl; subst; cbn; apply h1.
      - rewrite strength_cons.
        assert (hne' : (w :: l'')%list <> List.nil) by discriminate.
        assert (hl' : List.last (w :: l'')%list v = j).
        { rewrite (last_default _ v u hne'); exact hl. }
        specialize (ih v j hne' hl').
        specialize (h1 u v); specialize (h2 u j v).
        destruct (Z.min_spec (d u v) (strength d v (w :: l'')%list)) as [[? ?] | [? ?]];
        destruct (Z.min_spec (p u v) (p v j)) as [[? ?] | [? ?]]; lia.
  Qed.

  (* THE key lemma: a certificate pins down the closure *)
  Theorem cert_ok_is_closure : ∀ (d p : matrix) (paths : node -> node -> list node),
    (∀ i j, 0 <= d i j) -> cert_ok d p paths -> is_closure d p.
  Proof.
    intros d p paths hd (h1 & h2 & h3) i j; split; [| split].
    + specialize (hd i j); specialize (h1 i j); lia.
    + intros l hl; destruct l as [| u l']; [contradiction |].
      destruct hl as (-> & hne & hlast); cbn.
      exact (strength_le d p h1 h2 l' i j hne hlast).
    + intro hp; exists (paths i j); exact (h3 i j).
  Qed.

  Theorem closure_unique : ∀ (d p p' : matrix), 
    is_closure d p -> is_closure d p' -> ∀ i j, p i j = p' i j.
  Proof.
    intros d p p' hp hp' i j.
    destruct (hp i j) as (h0 & hub & hat); destruct (hp' i j) as (h0' & hub' & hat').
    assert (ha : p i j <= p' i j).
    { destruct (Z_lt_le_dec 0 (p i j)) as [hlt | hle]; [| lia].
      destruct (hat hlt) as (l & hl & hs); specialize (hub' l hl); lia. }
    assert (hb : p' i j <= p i j).
    { destruct (Z_lt_le_dec 0 (p' i j)) as [hlt | hle]; [| lia].
      destruct (hat' hlt) as (l & hl & hs); specialize (hub l hl); lia. }
    lia.
  Qed.

  (* a certified winner is a Schulze winner of the (unique) closure *)
  Corollary cert_winner : ∀ (d p : matrix) (paths : node -> node -> list node) (w : node), 
    (∀ i j, 0 <= d i j) -> cert_ok d p paths -> schulze_winner p w ->
    ∀ p', is_closure d p' -> schulze_winner p' w.
  Proof.
    intros d p paths w hd hc hw p' hp' j.
    pose proof (closure_unique d p p' (cert_ok_is_closure d p paths hd hc) hp') as he.
    rewrite <- !he; apply hw.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* computable closure, witness paths and winner, for the honest prover.
     Their correctness is not part of the trusted base and is not proved 
     here: the trustees check the computed certificate with cert_ok_b 
     before publishing (verify_tally_complete_auto), and verify_tally_sound 
     does not depend on how the certificate was produced. The algorithm is 
     the Kleene iteration of the min-max semiring, verified in the 
     Semiring_graph_algorithm development (mat_star, kleene_fixed_point_least). *)

  Definition max_fin (f : node -> Z) (z : Z) : Z := 
    Vector.fold_right (fun i acc => Z.max (f i) acc) (fin_enum m) z.

  Definition closure_step (d p : matrix) : matrix := 
    fun i j => Z.max (p i j) (max_fin (fun k => Z.min (p i k) (d k j)) 0).

  (* the matrix as a table, so that each iteration is computed once: iterating
     closure_step on functions re-evaluates the previous step at every
     access, (2m)^m evaluations in all *)
  Definition tab (p : matrix) : Vector.t (Vector.t Z m) m :=
    Vector.map (fun i => Vector.map (p i) (fin_enum m)) (fin_enum m).
  Definition untab (t : Vector.t (Vector.t Z m) m) : matrix := fun i j => t[@i][@j].

  (* after m steps every walk of at most m + 1 edges has been considered *)
  Definition minmax_closure (d : matrix) : matrix :=
    untab (Nat.iter m (fun t => tab (closure_step d (untab t))) (tab d)).

  Definition first_some {A : Type} (f : node -> option A) : option A :=
    Vector.fold_right (fun i acc => match f i with Some a => Some a | None => acc end) 
      (fin_enum m) None.

  Definition in_node (k : node) (l : list node) : bool :=
    List.existsb (fun v => if Fin.eq_dec k v then true else false) l.

  (* breadth-first search for a walk u → ... → j with every edge ≥ s; the
     frontier holds (node, the nodes after the start, reversed) *)
  Fixpoint bfs_walk (d : matrix) (s : Z) (fuel : nat) (j : node)
    (frontier : list (node * list node)) (visited : list node) : option (list node) :=
    match fuel with
    | O => None
    | S fuel' =>
      match frontier with
      | List.nil => None
      | List.cons (u, path) rest =>
        if Z.leb s (d u j) then Some (List.rev (List.cons j path))
        else
          let nexts := List.filter (fun k => (Z.leb s (d u k) && negb (in_node k visited))%bool)
            (Vector.to_list (fin_enum m)) in
          bfs_walk d s fuel' j (rest ++ List.map (fun k => (k, List.cons k path)) nexts)%list
            (nexts ++ visited)%list
      end
    end.

  Definition find_walk (d : matrix) (s : Z) (u j : node) : option (list node) :=
    bfs_walk d s (S (m * m)) j (List.cons (u, List.nil) List.nil) (List.cons u List.nil).

  Definition witness_path (d p : matrix) (i j : node) : list node :=
    match find_walk d (p i j) i j with
    | Some l => List.cons i l
    | None => List.cons i (List.cons j List.nil)
    end.

  (* ---------------------------------------------------------------- *)
  (* the certificate as a boolean check, so that the trustees can verify 
     their plaintext certificate before publishing it *)

  Definition path_from_to_b (i j : node) (l : list node) : bool :=
    match l with
    | List.nil => false
    | List.cons u l' => 
      ((if Fin.eq_dec u i then true else false) &&
       (match l' with List.nil => false | _ => true end) &&
       (if Fin.eq_dec (List.last l' i) j then true else false))%bool
    end.

  Definition cert_ok_b (d p : matrix) (paths : node -> node -> list node) : bool :=
    (forall_fin m (fun i => forall_fin m (fun j => Z.leb (d i j) (p i j))) &&
     forall_fin m (fun i => forall_fin m (fun j => forall_fin m (fun k => 
       Z.leb (Z.min (p i k) (p k j)) (p i j)))) &&
     forall_fin m (fun i => forall_fin m (fun j => 
       (path_from_to_b i j (paths i j) && 
        Z.leb (p i j) (path_strength d (paths i j)))%bool)))%bool.

  Definition schulze_winner_b (p : matrix) (w : node) : bool := 
    forall_fin m (fun j => Z.leb (p j w) (p w j)).

  Lemma path_from_to_b_sound : ∀ (i j : node) (l : list node), 
    path_from_to_b i j l = true -> path_from_to i j l.
  Proof.
    intros i j [| u l'] h; [discriminate |]; cbn in h |- *.
    apply andb_prop in h; destruct h as (h & h3); apply andb_prop in h; destruct h as (h1 & h2).
    destruct (Fin.eq_dec u i); [| discriminate].
    destruct (Fin.eq_dec (List.last l' i) j); [| discriminate].
    destruct l'; [discriminate |].
    split; [assumption | split; [discriminate | assumption]].
  Qed.

  Lemma cert_ok_b_sound : ∀ (d p : matrix) (paths : node -> node -> list node), 
    cert_ok_b d p paths = true -> cert_ok d p paths.
  Proof.
    intros d p paths h; unfold cert_ok_b in h.
    apply andb_prop in h; destruct h as (h & h3); apply andb_prop in h; destruct h as (h1 & h2).
    split; [| split].
    + intros i j; apply Z.leb_le. 
      exact (proj1 (forall_fin_true _ _) (proj1 (forall_fin_true _ _) h1 i) j).
    + intros i j k; apply Z.leb_le. 
      exact (proj1 (forall_fin_true _ _) 
        (proj1 (forall_fin_true _ _) (proj1 (forall_fin_true _ _) h2 i) j) k).
    + intros i j. 
      pose proof (proj1 (forall_fin_true _ _) (proj1 (forall_fin_true _ _) h3 i) j) as hij.
      apply andb_prop in hij; destruct hij as (ha & hb).
      split; [apply path_from_to_b_sound; exact ha | apply Z.leb_le; exact hb].
  Qed.

  Lemma schulze_winner_b_sound : ∀ (p : matrix) (w : node), 
    schulze_winner_b p w = true -> schulze_winner p w.
  Proof. intros p w h j; apply Z.leb_le; exact (proj1 (forall_fin_true _ _) h j). Qed.

  Definition winner_of (p : matrix) : option node :=
    first_some (fun w => 
      if forall_fin m (fun j => Z.leb (p j w) (p w j)) then Some w else None).

End SchulzeZ.

(* ------------------------------------------------------------------ *)
(* Part 2: the cryptographic tally                                      *)
(* ------------------------------------------------------------------ *)

Section SchulzeTally.

  Context 
    {F : Type}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  Context 
    {G : Type} 
    {gid : G} 
    {ginv : G -> G}
    {gop : G -> G -> G} 
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "+" := add.
  Local Notation natF := (nat_to_F zero one add).

  (* the ciphertext algebra and the membership proofs of Frontend/Schulze.v, 
     at this section's parameters *)
  Local Notation cmul := (Schulze.cmul (gop := gop)).
  Local Notation cinv := (Schulze.cinv (ginv := ginv)).
  Local Notation cpow := (Schulze.cpow (gpow := gpow)).
  Local Notation cdec := (Schulze.cdec (ginv := ginv) (gop := gop) (gpow := gpow)).
  Local Notation membership_proof k := (@Schulze.membership_proof F G k).
  Local Notation verify_membership := (Schulze.verify_membership (F := F) (zero := zero) 
    (add := add) (Fdec := Fdec) (G := G) (ginv := ginv) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation prove_membership := (Schulze.prove_membership (F := F) (zero := zero) 
    (add := add) (mul := mul) (sub := sub) (opp := opp) (G := G) (ginv := ginv) (gop := gop) 
    (gpow := gpow)).

  (* the product group G × G, in which a ciphertext statement is a Schnorr 
     statement (c₁, c₂ / m) = (g, h)^r *)
  Local Notation G2 := (G * G)%type.
  Definition gop2 : G2 -> G2 -> G2 := padd (vadd1 := gop) (vadd2 := gop).
  Definition gpow2 : G2 -> F -> G2 := psmul (smul1 := gpow) (smul2 := gpow).
  Definition Gdec2 : forall x y : G2, {x = y} + {x <> y} := prod_dec Gdec Gdec.

  Definition or_statement (cp : G2) (msg : G) : G2 := (fst cp, gop (snd cp) (ginv msg)).

  (* discrete logarithm of y in base g among g^0 .. g^k, by search *)
  Fixpoint dlog_le (g y : G) (k : nat) : option nat :=
    match k with
    | 0 => if Gdec y (g ^ natF 0) then Some 0 else None
    | S k' => 
      match dlog_le g y k' with
      | Some r => Some r
      | None => if Gdec y (g ^ natF (S k')) then Some (S k') else None
      end
    end.

  Section Verifier.
    (* m candidates, N ballots *)
    Context {m N : nat} (g h : G).
    Local Notation matrix A := (Vector.t (Vector.t A m) m).
    Definition mget {A : Type} (M : matrix A) (i j : Fin.t m) : A := 
      Vector.nth (Vector.nth M i) j.

    (* g^0 .. g^N : the set {0..N} *)
    Definition msgs_range : Vector.t G (S N) :=
      Vector.map (fun k => g ^ natF (fin_idx k)) (fin_enum (S N)).

    (* K = 2N + 1 *)
    Definition tally_shift : nat := S (N + N).

    Definition or_proof (k : nat) : Type := @sigma_proto F G2 k (S k) k.

    Definition verify_or {k : nat} (hs : Vector.t G2 k) (pf : or_proof k) : bool :=
      @generalised_or_accepting_conversations F zero add Fdec G2 gop2 gpow2 Gdec2 k 
        (Vector.const (g, h) k) hs pf.

    Definition verify_range (cp : G2) (pf : membership_proof (S N)) : bool :=
      verify_membership g h msgs_range cp pf.

    (* the two ciphertexts of the defeat disjunction for the pair (i, j):
       V₂ = Enc(d)^K · Enc(D_ij) / Enc(D_ji)   on which  K d + Δ ∈ {-N..0}
       V₁ = (Enc(d) / Enc(D_ij))^K · Enc(D_ij) / Enc(D_ji)   on which  
            K (d - D_ij) + Δ ∈ {1..N} *)
    Definition defeat_statements (encD' enc_d : matrix G2) (i j : Fin.t m) : 
      Vector.t G2 (S N + N) :=
      let Dij := mget encD' i j in
      let Dji := mget encD' j i in
      let dij := mget enc_d i j in
      let delta := cmul Dij (cinv Dji) in
      let V2 := cmul (cpow dij (natF tally_shift)) delta in
      let V1 := cmul (cpow (cmul dij (cinv Dij)) (natF tally_shift)) delta in
      Vector.map (fun t => or_statement V2 (ginv (g ^ natF (fin_idx t)))) (fin_enum (S N)) ++
      Vector.map (fun t => or_statement V1 (g ^ natF (S (fin_idx t)))) (fin_enum N).

    (* p_ij - p_ik ∈ {0..N}  ∨  p_ij - p_kj ∈ {0..N} *)
    Definition upper_statements (enc_p : matrix G2) (k i j : Fin.t m) : 
      Vector.t G2 (S N + S N) :=
      let pij := mget enc_p i j in
      let A := cmul pij (cinv (mget enc_p i k)) in
      let B := cmul pij (cinv (mget enc_p k j)) in
      Vector.map (fun t => or_statement A (g ^ natF (fin_idx t))) (fin_enum (S N)) ++
      Vector.map (fun t => or_statement B (g ^ natF (fin_idx t))) (fin_enum (S N)).

    Record tally_proof : Type := mk_tally_proof {
      tp_encD'   : matrix G2;                       (* fresh Enc'(D_ij) *)
      tp_dec     : matrix (@sigma_proto F G 2 1 1); (* Enc'(D_ij) / Enc(D_ij) decrypts to 1 *)
      tp_enc_d   : matrix G2;                       (* Enc(d_ij) *)
      tp_enc_p   : matrix G2;                       (* Enc(p_ij) *)
      tp_d_range : matrix (membership_proof (S N)); (* d_ij ∈ {0..N} *)
      tp_defeat  : matrix (or_proof (S N + N));     (* the defeat disjunction *)
      tp_lower   : matrix (membership_proof (S N)); (* p_ij - d_ij ∈ {0..N} *)
      tp_upper   : Vector.t (matrix (or_proof (S N + S N))) m; 
                                                    (* [k][i][j] : p_ij ≥ p_ik ∨ p_ij ≥ p_kj *)
      tp_paths   : matrix (list (Fin.t m));         (* witness path i :: ... :: j *)
      tp_edges   : matrix (list (membership_proof (S N))); 
                                                    (* d_uv - p_ij ∈ {0..N} per edge (u, v) *)
      tp_winner  : Vector.t (membership_proof (S N)) m (* p_wj - p_jw ∈ {0..N} *)
    }.

    (* the edges (u, v) of the path u :: l, with one proof each *)
    Fixpoint verify_edges (enc_d : matrix G2) (pij : G2) (u : Fin.t m) 
      (l : list (Fin.t m)) (pfs : list (membership_proof (S N))) : bool :=
      match l, pfs with
      | List.nil, List.nil => true
      | List.cons v l', List.cons pf pfs' => 
        (verify_range (cmul (mget enc_d u v) (cinv pij)) pf && 
         verify_edges enc_d pij v l' pfs')%bool
      | _, _ => false
      end.

    Definition verify_path (enc_d enc_p : matrix G2) (i j : Fin.t m) 
      (l : list (Fin.t m)) (pfs : list (membership_proof (S N))) : bool :=
      match l with
      | List.nil => false
      | List.cons u l' => 
        ((if Fin.eq_dec u i then true else false) &&
         (match l' with List.nil => false | _ => true end) &&
         (if Fin.eq_dec (List.last l' i) j then true else false) &&
         verify_edges enc_d (mget enc_p i j) u l' pfs)%bool
      end.

    Definition forall_pairs (f : Fin.t m -> Fin.t m -> bool) : bool :=
      forall_fin m (fun i => forall_fin m (fun j => f i j)).

    (* the seven checks of the tally, separately (for diagnostics) *)
    Definition tally_checks (encD : matrix G2) (w : Fin.t m) (pf : tally_proof) : list bool :=
      let encD' := tp_encD' pf in
      let enc_d := tp_enc_d pf in
      let enc_p := tp_enc_p pf in
      (* 1. Enc'(D_ij) / Enc(D_ij) decrypts to the identity *)
      (forall_pairs (fun i j => 
        let c := cmul (mget encD' i j) (cinv (mget encD i j)) in
        decryption_proof_accepting_conversations (F := F) (G := G) (ginv := ginv) 
          (gop := gop) (gpow := gpow) (Gdec := Gdec) g h 
          (fst c) (snd c) gid (mget (tp_dec pf) i j)) ::
      (* 2. d_ij ∈ {0..N} and the defeat disjunction *)
       forall_pairs (fun i j => verify_range (mget enc_d i j) (mget (tp_d_range pf) i j)) ::
       forall_pairs (fun i j => 
        verify_or (defeat_statements encD' enc_d i j) (mget (tp_defeat pf) i j)) ::
      (* 3. closure: p ≥ d, one-step closed, witness paths *)
       forall_pairs (fun i j => 
        verify_range (cmul (mget enc_p i j) (cinv (mget enc_d i j))) (mget (tp_lower pf) i j)) ::
       forall_fin m (fun k => forall_pairs (fun i j => 
        verify_or (upper_statements enc_p k i j) (mget (Vector.nth (tp_upper pf) k) i j))) ::
       forall_pairs (fun i j => 
        verify_path enc_d enc_p i j (mget (tp_paths pf) i j) (mget (tp_edges pf) i j)) ::
      (* 4. winner *)
       forall_fin m (fun j => 
        verify_range (cmul (mget enc_p w j) (cinv (mget enc_p j w))) 
          (Vector.nth (tp_winner pf) j)) :: List.nil)%list.

    Definition verify_tally (encD : matrix G2) (w : Fin.t m) (pf : tally_proof) : bool :=
      List.forallb (fun b => b) (tally_checks encD w pf).

  End Verifier.

  (* ---------------------------------------------------------------- *)
  (* the honest trustees: m = S n candidates, N = S n' ballots           *)

  Section Prover.
    Context {n n' : nat} (x : F) (g h : G).
    Local Notation m := (S n).
    Local Notation N := (S n').
    Local Notation matrix A := (Vector.t (Vector.t A m) m).

    (* randomness: a source of field elements indexed by a slot number; 
       slot (tag, i, j, k) spans [slot, slot + stride) *)
    Definition stride : nat := 4 * N + 8.
    Definition slot (tag i j k : nat) : nat := 
      ((((tag * m + i) * m + j) * m + k) * stride)%nat.
    Definition rvec (rnd : nat -> F) (base : nat) (k : nat) : Vector.t F k :=
      Vector.map (fun t => rnd (base + fin_idx t)%nat) (fin_enum k).

    Definition nat_of_Z (z : Z) : nat := Z.to_nat z.

    (* membership of the value v ∈ {0..N} in Enc(v) with randomness r *)
    Definition prove_range (v : Z) (r : F) (uscs : Vector.t F ((2 + n') + (1 + n'))) 
      (cp : G2) (c : F) : membership_proof (S N) :=
      prove_membership g h (msgs_range (N := N) g) (fin_of_nat_default (nat_of_Z v) N) 
        r uscs cp c.

    Definition prove_or {k : nat} (rindex : Fin.t (2 + k)) (r : F) (hs : Vector.t G2 (2 + k))
      (uscs : Vector.t F ((2 + k) + (1 + k))) (c : F) : or_proof (2 + k) :=
      generalised_construct_or_conversations_schnorr (F := F) (zero := zero) (add := add) 
        (mul := mul) (sub := sub) (opp := opp) (G := G2) (gop := gop2) (gpow := gpow2) 
        (n := k) rindex r (Vector.const (g, h) (2 + k)) hs uscs c.

    Definition mat_of {A : Type} (f : Fin.t m -> Fin.t m -> A) : matrix A :=
      Vector.map (fun i => Vector.map (fun j => f i j) (fin_enum m)) (fin_enum m).

    Definition fun_of (M : matrix Z) : Fin.t m -> Fin.t m -> Z := fun i j => mget M i j.

    (* the plaintext margins, by decryption with x and a search up to N *)
    Definition decrypt_margins (encD : matrix G2) : matrix Z :=
      Vector.map (Vector.map (fun c => 
        match dlog_le g (cdec x c) N with Some k => Z.of_nat k | None => 0%Z end)) encD.

    (* the edge proofs d_uv - p_ij ∈ {0..N} along the path u :: l, edge 
       counter e *)
    Fixpoint edge_proofs (d p : Fin.t m -> Fin.t m -> Z) (enc_d enc_p : matrix G2) 
      (rd rp : Fin.t m -> Fin.t m -> F) (rnd : nat -> F) (chal : F) (i j u : Fin.t m) 
      (l : list (Fin.t m)) (e : nat) : list (membership_proof (S N)) :=
      match l with
      | List.nil => List.nil
      | List.cons v l' => 
        List.cons (prove_range (d u v - p i j) (sub (rd u v) (rp i j)) 
          (rvec rnd (slot 13 (fin_idx i) (fin_idx j) e) _)
          (cmul (mget enc_d u v) (cinv (mget enc_p i j))) 
          chal) 
          (edge_proofs d p enc_d enc_p rd rp rnd chal i j v l' (S e))
      end.

    (* the tally proof for the winner w, with randomness rnd, from the 
       trustees' plaintext margins D, strongest paths p and witness paths *)
    Definition generate_tally_with (encD : matrix G2) 
      (D p : Fin.t m -> Fin.t m -> Z) (paths : Fin.t m -> Fin.t m -> list (Fin.t m))
      (w : Fin.t m) (rnd : nat -> F) (chal : F) : @tally_proof m N :=
      let d := @defeat m D in
      let K := natF (tally_shift (N := N)) in
      (* randomness of the ciphertexts *)
      let rD := fun i j => rnd (slot 0 (fin_idx i) (fin_idx j) 0) in
      let rd := fun i j => rnd (slot 3 (fin_idx i) (fin_idx j) 0) in
      let rp := fun i j => rnd (slot 4 (fin_idx i) (fin_idx j) 0) in
      let encD' := mat_of (fun i j => @enc F G gop gpow g h (natF (nat_of_Z (D i j))) (rD i j)) in
      let enc_d := mat_of (fun i j => @enc F G gop gpow g h (natF (nat_of_Z (d i j))) (rd i j)) in
      let enc_p := mat_of (fun i j => @enc F G gop gpow g h (natF (nat_of_Z (p i j))) (rp i j)) in
      let dec := mat_of (fun i j => 
        let c := cmul (mget encD' i j) (cinv (mget encD i j)) in
        construct_decryption_proof_elgamal_real (F := F) (add := add) (mul := mul) 
          (G := G) (gpow := gpow) x g c 
          (rnd (slot 1 (fin_idx i) (fin_idx j) 0)) chal) in
      let d_range := mat_of (fun i j => 
        prove_range (d i j) (rd i j) (rvec rnd (slot 5 (fin_idx i) (fin_idx j) 0) _) 
          (mget enc_d i j) chal) in
      let defeat_pf := mat_of (fun i j => 
        let delta := (D i j - D j i)%Z in
        let rdelta := sub (rD i j) (rD j i) in
        let hs := defeat_statements (N := N) g encD' enc_d i j in
        let uscs := rvec rnd (slot 7 (fin_idx i) (fin_idx j) 0) _ in
        let c := chal in
        if Z.ltb 0 delta
        then (* d = D_ij : branch S N + (Δ - 1) on V₁, randomness K (rd - rD) + rdelta *)
          prove_or (k := n' + S n') (fin_of_nat_default (N + nat_of_Z delta) (N + N)) 
            ((K * sub (rd i j) (rD i j)) + rdelta) hs uscs c
        else (* d = 0 : branch -Δ on V₂, randomness K rd + rdelta *)
          prove_or (k := n' + S n') (fin_of_nat_default (nat_of_Z (- delta)) (N + N)) 
            ((K * rd i j) + rdelta) hs uscs c) in
      let lower := mat_of (fun i j => 
        prove_range (p i j - d i j) (sub (rp i j) (rd i j)) 
          (rvec rnd (slot 9 (fin_idx i) (fin_idx j) 0) _)
          (cmul (mget enc_p i j) (cinv (mget enc_d i j))) 
          chal) in
      let upper := Vector.map (fun k => mat_of (fun i j => 
        let hs := upper_statements (N := N) g enc_p k i j in
        let uscs := rvec rnd (slot 11 (fin_idx i) (fin_idx j) (fin_idx k)) _ in
        let c := chal in
        if Z.leb (p i k) (p i j)
        then prove_or (k := n' + S (S n')) 
          (fin_of_nat_default (nat_of_Z (p i j - p i k)) (N + S N)) 
          (sub (rp i j) (rp i k)) hs uscs c
        else prove_or (k := n' + S (S n')) 
          (fin_of_nat_default (S N + nat_of_Z (p i j - p k j)) (N + S N)) 
          (sub (rp i j) (rp k j)) hs uscs c)) (fin_enum m) in
      let edges := mat_of (fun i j => 
        match paths i j with
        | List.nil => List.nil
        | List.cons u l => edge_proofs d p enc_d enc_p rd rp rnd chal i j u l 0
        end) in
      let winner := Vector.map (fun j => 
        prove_range (p w j - p j w) (sub (rp w j) (rp j w)) 
          (rvec rnd (slot 15 (fin_idx j) 0 0) _)
          (cmul (mget enc_p w j) (cinv (mget enc_p j w))) 
          chal) (fin_enum m) in
      mk_tally_proof encD' dec enc_d enc_p d_range defeat_pf lower upper 
        (mat_of paths) edges winner.

    (* the tally proof with the margins decrypted by the trustees and the 
       closure and witness paths computed from them *)
    Definition generate_tally (encD : matrix G2) (w : Fin.t m) (rnd : nat -> F) (chal : F) : 
      @tally_proof m N :=
      let D := fun_of (decrypt_margins encD) in
      let d := @defeat m D in
      let p := @minmax_closure m d in
      generate_tally_with encD D p (@witness_path m d p) w rnd chal.

    (* the winner the trustees announce *)
    Definition tally_winner (encD : matrix G2) : option (Fin.t m) :=
      let D := fun_of (decrypt_margins encD) in
      @winner_of m (@minmax_closure m (@defeat m D)).

  End Prover.

  (* ---------------------------------------------------------------- *)
  (* non-interactive tally (Fiat-Shamir): one challenge for all the 
     sub-proofs, the hash of the statement and of all announcements      *)

  Inductive tr_item : Type := TrC (c : G2) | TrG (a : G) | TrN (k : nat).

  Section TallyNIZK.
    Context {n n' : nat} (x : F) (g h : G) (H : list tr_item -> F).
    Local Notation m := (S n).
    Local Notation N := (S n').
    Local Notation matrix A := (Vector.t (Vector.t A m) m).

    Definition tr_mat_pf {A : Type} (M : matrix A) (f : A -> list tr_item) : list tr_item :=
      List.concat (Vector.to_list (Vector.map (fun i => 
        List.concat (Vector.to_list (Vector.map (fun j => f (mget M i j)) (fin_enum m)))) 
        (fin_enum m))).
    Definition tr_ann2 {k l r : nat} (pf : @sigma_proto F G2 k l r) : list tr_item :=
      List.map TrC (Vector.to_list (Sigma.announcement pf)).
    Definition tr_ann1 (pf : @sigma_proto F G 2 1 1) : list tr_item :=
      List.map TrG (Vector.to_list (Sigma.announcement pf)).

    (* the statement (winner, aggregate, published ciphertexts, paths) and 
       every announcement, in a fixed order *)
    Definition tally_transcript (encD : matrix G2) (w : Fin.t m) (pf : @tally_proof m N) : 
      list tr_item :=
      (TrN (fin_idx w) :: 
       tr_mat_pf encD (fun c => TrC c :: List.nil) ++
       tr_mat_pf (tp_encD' pf) (fun c => TrC c :: List.nil) ++
       tr_mat_pf (tp_enc_d pf) (fun c => TrC c :: List.nil) ++
       tr_mat_pf (tp_enc_p pf) (fun c => TrC c :: List.nil) ++
       tr_mat_pf (tp_paths pf) (List.map (fun u => TrN (fin_idx u))) ++
       tr_mat_pf (tp_dec pf) tr_ann1 ++
       tr_mat_pf (tp_d_range pf) tr_ann2 ++
       tr_mat_pf (tp_defeat pf) tr_ann2 ++
       tr_mat_pf (tp_lower pf) tr_ann2 ++
       List.concat (Vector.to_list (Vector.map (fun k => tr_mat_pf (tp_upper pf)[@k] tr_ann2) 
         (fin_enum m))) ++
       tr_mat_pf (tp_edges pf) (fun l => List.concat (List.map tr_ann2 l)) ++
       List.concat (Vector.to_list (Vector.map (fun j => tr_ann2 (tp_winner pf)[@j]) 
         (fin_enum m))))%list.

    Definition is_chal1 (c : F) (pf : @sigma_proto F G 2 1 1) : bool :=
      if Fdec (Vector.hd (Sigma.challenge pf)) c then true else false.
    Definition is_chal2 (c : F) {k l r : nat} (pf : @sigma_proto F G2 k (S l) r) : bool :=
      if Fdec (Vector.hd (Sigma.challenge pf)) c then true else false.

    Definition tally_challenges_are (c : F) (pf : @tally_proof m N) : bool :=
      (forall_pairs (fun i j => is_chal1 c (mget (tp_dec pf) i j)) &&
       forall_pairs (fun i j => is_chal2 c (mget (tp_d_range pf) i j)) &&
       forall_pairs (fun i j => is_chal2 c (mget (tp_defeat pf) i j)) &&
       forall_pairs (fun i j => is_chal2 c (mget (tp_lower pf) i j)) &&
       forall_fin m (fun k => forall_pairs (fun i j => is_chal2 c (mget (tp_upper pf)[@k] i j))) &&
       forall_pairs (fun i j => List.forallb (is_chal2 c) (mget (tp_edges pf) i j)) &&
       forall_fin m (fun j => is_chal2 c (tp_winner pf)[@j]))%bool.

    Definition nizk_verify_tally (encD : matrix G2) (w : Fin.t m) (pf : @tally_proof m N) : bool :=
      (tally_challenges_are (H (tally_transcript encD w pf)) pf && 
       verify_tally (N := N) g h encD w pf)%bool.

    (* the trustees: announcements first (with the challenge zero), then the 
       proofs with the hashed challenge *)
    Definition nizk_generate_tally_with (encD : matrix G2) 
      (D p : Fin.t m -> Fin.t m -> Z) (paths : Fin.t m -> Fin.t m -> list (Fin.t m))
      (w : Fin.t m) (rnd : nat -> F) : @tally_proof m N :=
      let pf0 := generate_tally_with (n' := n') x g h encD D p paths w rnd zero in
      generate_tally_with (n' := n') x g h encD D p paths w rnd (H (tally_transcript encD w pf0)).

    Definition nizk_generate_tally (encD : matrix G2) (w : Fin.t m) (rnd : nat -> F) : 
      @tally_proof m N :=
      let D := fun_of (n := n) (decrypt_margins (n := n) (n' := n') x g encD) in
      let d := @defeat m D in
      let p := @minmax_closure m d in
      nizk_generate_tally_with encD D p (@witness_path m d p) w rnd.
  End TallyNIZK.

  (* ---------------------------------------------------------------- *)
  (* the tally as a state machine, in the style of HeliosTally.v: the 
     ballots are read one by one, the valid ones are aggregated into the 
     encrypted margins, and the published certificate is checked against 
     the aggregate. count s is the evidence that s was reached by these 
     rules; compute_final_count builds it (correct by construction).      *)

  Section SchulzeCount.
    Context {n n' : nat} (g h : G) (Hb : list (G * G) -> F) (Ht : list tr_item -> F).
    Local Notation m := (S n).
    Local Notation N := (S n').
    Local Notation ballot := (@ballot F G m).
    Local Notation matrix A := (Vector.t (Vector.t A m) m).
    Local Notation nizk_verify_ballot := (Schulze.nizk_verify_ballot (zero := zero) (one := one) 
      (add := add) (Fdec := Fdec) (ginv := ginv) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
    Local Notation ballot_bits := (Schulze.ballot_bits (F := F) (G := G)).
    Local Notation cid := (Schulze.cid (gid := gid)).

    (* the running encrypted margins *)
    Definition init_margins : matrix G2 := Vector.const (Vector.const cid m) m.
    Definition add_ballot (b : ballot) (ms : matrix G2) : matrix G2 :=
      Vector.map2 (Vector.map2 cmul) (ballot_bits b) ms.
    Definition aggregate_list (vbs : list ballot) : matrix G2 :=
      List.fold_right add_ballot init_margins vbs.

    (* partial us vbs inbs ms : ballots seen, valid, invalid, running margins;
       finished us vbs inbs w pf b : the announced winner, the certificate 
       and the verdict *)
    Inductive state : Type :=
    | partial : list ballot -> list ballot -> list ballot -> matrix G2 -> state
    | finished : list ballot -> list ballot -> list ballot -> 
        Fin.t m -> @tally_proof m N -> bool -> state.

    Inductive count : state -> Type :=
    (* the initial margins encrypt zero everywhere *)
    | ax (ms : matrix G2) : 
        (∀ i j, mget ms i j = cid) -> 
        count (partial List.nil List.nil List.nil ms)
    (* a ballot whose proofs verify is aggregated *)
    | cvalid (b : ballot) (us vbs inbs : list ballot) (ms nms : matrix G2) :
        count (partial us vbs inbs ms) -> Permutation us (vbs ++ inbs) ->
        nizk_verify_ballot g h Hb b = true ->
        nms = add_ballot b ms ->
        count (partial (b :: us) (b :: vbs) inbs nms)
    (* a ballot whose proofs do not verify is set aside *)
    | cinvalid (b : ballot) (us vbs inbs : list ballot) (ms : matrix G2) :
        count (partial us vbs inbs ms) -> Permutation us (vbs ++ inbs) ->
        nizk_verify_ballot g h Hb b = false ->
        count (partial (b :: us) vbs (b :: inbs) ms)
    (* the certificate is checked against the aggregate; the number of 
       valid ballots must be within the range N of the certificate *)
    | finish (us vbs inbs : list ballot) (ms : matrix G2) (w : Fin.t m) 
        (pf : @tally_proof m N) (bsize bpf bfinal : bool) :
        count (partial us vbs inbs ms) -> Permutation us (vbs ++ inbs) ->
        Nat.leb (List.length vbs) N = bsize ->
        nizk_verify_tally g h Ht ms w pf = bpf ->
        bfinal = andb bsize bpf ->
        count (finished us vbs inbs w pf bfinal).

    (* the running margins are the aggregate of the valid ballots *)
    Lemma count_partial_aggregate : ∀ (us vbs inbs : list ballot) (ms : matrix G2),
      count (partial us vbs inbs ms) -> ms = aggregate_list vbs.
    Proof.
      intros * hc.
      remember (partial us vbs inbs ms) as st eqn:hst.
      revert us vbs inbs ms hst.
      induction hc as [ms0 h0 | b us0 vbs0 inbs0 ms0 nms0 hc ih hp hv hn 
        | b us0 vbs0 inbs0 ms0 hc ih hp hv | ]; intros us' vbs' inbs' ms' hst; 
        try discriminate; injection hst; intros ? ? ? ?; subst.
      + apply (proj1 (Vector.eq_nth_iff _ _ _ _)); intros i i' <-.
        apply (proj1 (Vector.eq_nth_iff _ _ _ _)); intros j j' <-.
        unfold aggregate_list, init_margins; cbn [List.fold_right]; rewrite !Vector.const_nth.
        pose proof (h0 i j) as hij; unfold mget in hij; exact hij.
      + rewrite (ih _ _ _ _ eq_refl); reflexivity.
      + exact (ih _ _ _ _ eq_refl).
    Qed.

    Lemma count_valid_ballots : ∀ (us vbs inbs : list ballot) (ms : matrix G2),
      count (partial us vbs inbs ms) -> 
      ∀ b, List.In b vbs -> nizk_verify_ballot g h Hb b = true.
    Proof.
      intros * hc.
      remember (partial us vbs inbs ms) as st eqn:hst.
      revert us vbs inbs ms hst.
      induction hc as [ms0 h0 | b0 us0 vbs0 inbs0 ms0 nms0 hc ih hp hv hn 
        | b0 us0 vbs0 inbs0 ms0 hc ih hp hv | ]; intros us' vbs' inbs' ms' hst; 
        try discriminate; injection hst; intros ? ? ? ?; subst.
      + intros b hin; contradiction.
      + intros b' [<- | hin]; [exact hv | exact (ih _ _ _ _ eq_refl b' hin)].
      + exact (ih _ _ _ _ eq_refl).
    Qed.

    (* what a successful final state means *)
    Lemma count_finished_true : ∀ (us vbs inbs : list ballot) (w : Fin.t m) 
      (pf : @tally_proof m N),
      count (finished us vbs inbs w pf true) ->
      (∀ b, List.In b vbs -> nizk_verify_ballot g h Hb b = true) ∧
      List.length vbs <= N ∧
      nizk_verify_tally g h Ht (aggregate_list vbs) w pf = true.
    Proof.
      intros * hc.
      remember (finished us vbs inbs w pf true) as st eqn:hst.
      destruct hc as [| | | us0 vbs0 inbs0 ms0 w0 pf0 bsize bpf bfinal hc hp hsize hpf hb]; 
        try discriminate.
      injection hst; intros; subst us vbs inbs w pf.
      assert (hb' : andb bsize bpf = true) by (rewrite <- hb; assumption).
      rewrite <- hsize, <- hpf in hb'; apply andb_prop in hb'; destruct hb' as (hb1 & hb2).
      rewrite (count_partial_aggregate _ _ _ _ hc) in hb2.
      split; [exact (count_valid_ballots _ _ _ _ hc) |].
      split; [apply Nat.leb_le; exact hb1 | exact hb2].
    Qed.

    (* walking through the ballots *)
    Definition compute_final_tally : ∀ (bs : list ballot),
      existsT (vbs inbs : list ballot) (ms : matrix G2), 
        (count (partial bs vbs inbs ms) * Permutation bs (vbs ++ inbs))%type.
    Proof.
      refine (fix fn (bs : list ballot) {struct bs} :=
        match bs with
        | List.nil => _
        | List.cons bh bt => _
        end).
      + exists List.nil, List.nil, init_margins.
        refine (pair (ax init_margins _) (Permutation_refl _)).
        intros i j; unfold init_margins, mget; rewrite !Vector.const_nth; reflexivity.
      + refine (match nizk_verify_ballot g h Hb bh as v 
          return nizk_verify_ballot g h Hb bh = v -> 
            existsT (vbs inbs : list ballot) (ms : matrix G2), 
              (count (partial (bh :: bt) vbs inbs ms) * Permutation (bh :: bt) (vbs ++ inbs))%type
          with
          | true => fun hv => _
          | false => fun hv => _
          end eq_refl).
        * destruct (fn bt) as (vbs & inbs & ms & hc & hp).
          exists (bh :: vbs)%list, inbs, (add_ballot bh ms).
          refine (pair (cvalid bh bt vbs inbs ms _ hc hp hv eq_refl) _).
          cbn; apply Permutation_cons; [reflexivity | exact hp].
        * destruct (fn bt) as (vbs & inbs & ms & hc & hp).
          exists vbs, (bh :: inbs)%list, ms.
          refine (pair (cinvalid bh bt vbs inbs ms hc hp hv) _).
          eapply Permutation_trans; [apply Permutation_cons; [reflexivity | exact hp] |].
          apply Permutation_middle.
    Defined.

    (* the whole verification: correct by construction *)
    Definition compute_final_count : ∀ (bs : list ballot) (w : Fin.t m) (pf : @tally_proof m N),
      existsT (bfinal : bool) (vbs inbs : list ballot), count (finished bs vbs inbs w pf bfinal).
    Proof.
      intros bs w pf.
      destruct (compute_final_tally bs) as (vbs & inbs & ms & hc & hp).
      exists (andb (Nat.leb (List.length vbs) N) (nizk_verify_tally g h Ht ms w pf)), vbs, inbs.
      exact (finish bs vbs inbs ms w pf _ _ _ hc hp eq_refl eq_refl eq_refl).
    Defined.

    Definition final_verdict (bs : list ballot) (w : Fin.t m) (pf : @tally_proof m N) : bool :=
      projT1 (compute_final_count bs w pf).
  End SchulzeCount.

  (* ---------------------------------------------------------------- *)
  Section Proofs.

    Context
      {Hvec: @vector_space F (@eq F) zero one add mul sub 
        div opp inv G (@eq G) gid ginv gop gpow}.

    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    Local Notation enc := (@enc F G gop gpow).

    (* the algebra of Frontend/Schulze.v at this vector space; always used 
       by name: Product_space's global instances make typeclass search for 
       the group laws diverge in this file *)
    Local Notation gop_assoc := (gop_assoc (Hvec := Hvec)).
    Local Notation gop_comm := (gop_comm (Hvec := Hvec)).
    Local Notation gop_gid_l := (gop_gid_l (Hvec := Hvec)).
    Local Notation gop_gid_r := (gop_gid_r (Hvec := Hvec)).
    Local Notation gop_ginv_l := (gop_ginv_l (Hvec := Hvec)).
    Local Notation gop_ginv_r := (gop_ginv_r (Hvec := Hvec)).
    Local Notation ginv_gid := (ginv_gid (Hvec := Hvec)).
    Local Notation pow_one := (pow_one (Hvec := Hvec)).
    Local Notation pow_add := (pow_add (Hvec := Hvec)).
    Local Notation pow_mul := (pow_mul (Hvec := Hvec)).
    Local Notation pow_opp := (pow_opp (Hvec := Hvec)).
    Local Notation gop_pow := (gop_pow (Hvec := Hvec)).
    Local Notation ginv_pow := (ginv_pow (Hvec := Hvec)).
    Local Notation gop_rearrange := (gop_rearrange (Hvec := Hvec)).
    Local Notation ginv_gop := (ginv_gop (Hvec := Hvec)).
    Local Notation gop_cancel := (gop_cancel (Hvec := Hvec)).
    Local Notation enc_mul := (enc_mul (Hvec := Hvec)).
    Local Notation enc_inv := (enc_inv (Hvec := Hvec)).
    Local Notation enc_pow := (enc_pow (Hvec := Hvec)).
    Local Notation enc_div := (enc_div (Hvec := Hvec)).
    Local Notation prove_membership_valid := (prove_membership_valid (Hvec := Hvec)).

    Ltac fin_idx_default :=
      match goal with
      | [ |- context [ @fin_idx ?N (fin_of_nat_default ?i ?n) ] ] =>
          let e := fresh "hidx" in
          assert (e : @fin_idx N (fin_of_nat_default i n) = i) 
            by (apply fin_of_nat_default_idx; lia);
          rewrite e; clear e
      end.

    (* the product vector space G × G *)
    Definition gid2 : G2 := pid (vid1 := gid) (vid2 := gid).
    Definition ginv2 : G2 -> G2 := popp (vopp1 := ginv) (vopp2 := ginv).
    Definition vspace2 : @vector_space F (@eq F) zero one add mul sub div opp inv
      G2 (@eq G2) gid2 ginv2 gop2 gpow2 := prod_vspace (H1 := Hvec) (H2 := Hvec).

    (* ---------------------------------------------------------------- *)
    (* plaintext facts about defeats, paths and certificates             *)

    Lemma defeat_le : ∀ {m : nat} (D : Fin.t m -> Fin.t m -> Z) (i j : Fin.t m),
      (0 <= D i j)%Z -> (0 <= defeat D i j <= D i j)%Z.
    Proof.
      intros; unfold defeat; destruct (Z.ltb (D j i) (D i j)); lia.
    Qed.

    (* every edge of a walk is at least the strength of the walk *)
    Fixpoint edges_ge {m : nat} (d : Fin.t m -> Fin.t m -> Z) (s : Z) 
      (u : Fin.t m) (l : list (Fin.t m)) : Prop :=
      match l with
      | List.nil => True
      | List.cons v l' => (s <= d u v)%Z ∧ edges_ge d s v l'
      end.

    Lemma strength_edges_ge : ∀ {m : nat} (d : Fin.t m -> Fin.t m -> Z) (s : Z) 
      (l : list (Fin.t m)) (u : Fin.t m),
      l <> List.nil -> (s <= strength d u l)%Z -> edges_ge d s u l.
    Proof.
      intros m d s l; induction l as [| v l' ih]; intros u hne hs.
      + contradiction.
      + destruct l' as [| w l''].
        - cbn in *; split; [exact hs | exact I].
        - rewrite strength_cons in hs.
          destruct (Z.min_spec (d u v) (strength d v (w :: l'')%list)) as [[? ?] | [? ?]];
          split; try lia; apply ih; [discriminate | lia | discriminate | lia].
    Qed.

    (* a certified p is bounded by the bound of d *)
    Lemma cert_ok_bound : ∀ {m : nat} (d p : Fin.t m -> Fin.t m -> Z) 
      (paths : Fin.t m -> Fin.t m -> list (Fin.t m)) (B : Z),
      (∀ i j, d i j <= B)%Z -> cert_ok d p paths -> ∀ i j, (p i j <= B)%Z.
    Proof.
      intros * hd (_ & _ & h3) i j.
      destruct (h3 i j) as (hp & hs).
      destruct (paths i j) as [| u l'] eqn:hl; [contradiction |].
      destruct hp as (-> & hne & _); cbn in hs.
      destruct l' as [| v l'']; [contradiction |].
      destruct (strength_edges_ge d (p i j) _ i hne hs) as (he & _).
      specialize (hd i v); lia.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* the statements of the sub-proofs                                   *)

    Lemma mget_mat_of : ∀ {n : nat} (A : Type) (f : Fin.t (S n) -> Fin.t (S n) -> A) 
      (i j : Fin.t (S n)),
      mget (mat_of (n := n) f) i j = f i j.
    Proof. intros; unfold mget, mat_of; apply nth_mat. Qed.


    Lemma or_statement_enc : ∀ (g h : G) (m r : F) (msg : G),
      msg = g ^ m -> or_statement (enc g h m r) msg = gpow2 (g, h) r.
    Proof.
      intros * ->; unfold or_statement, gpow2, psmul, enc; cbn.
      rewrite gop_cancel; reflexivity.
    Qed.

    Lemma or_statement_enc_ext : ∀ (g h : G) (m r r' : F) (msg : G),
      r = r' -> msg = g ^ m -> or_statement (enc g h m r) msg = gpow2 (g, h) r'.
    Proof. intros * -> ->; apply or_statement_enc; reflexivity. Qed.

    (* natF of a difference of non-negative integers *)
    Lemma natF_Z_sub : ∀ (a b : Z), (0 <= b <= a)%Z -> 
      natF (Z.to_nat (a - b)) = sub (natF (Z.to_nat a)) (natF (Z.to_nat b)).
    Proof.
      intros a b hb.
      rewrite Z2Nat.inj_sub; [| lia].
      apply (natF_sub (Hvec := Hvec)).
      apply Z2Nat.inj_le; lia.
    Qed.

    Lemma prove_or_valid : ∀ (g h : G) (k : nat) (rindex : Fin.t (2 + k)) (r : F) 
      (hs : Vector.t G2 (2 + k)) (uscs : Vector.t F ((2 + k) + (1 + k))) (c : F),
      hs[@rindex] = gpow2 (g, h) r ->
      verify_or g h hs (prove_or g h rindex r hs uscs c) = true.
    Proof.
      intros * hr.
      unfold verify_or, prove_or.
      apply (generalised_construct_or_conversations_schnorr_completeness 
        (Hvec := prod_vspace (H1 := Hvec) (H2 := Hvec))).
      rewrite Vector.const_nth; exact hr.
    Qed.

    Lemma prove_range_valid : ∀ (n' : nat) (g h : G) (v : Z) (r : F) 
      (uscs : Vector.t F ((2 + n') + (1 + n'))) (cp : G2) (c : F),
      (0 <= v <= Z.of_nat (S n'))%Z -> cp = enc g h (natF (Z.to_nat v)) r ->
      verify_range (N := S n') g h cp (prove_range (n' := n') g h v r uscs cp c) = true.
    Proof.
      intros * hv hc.
      unfold verify_range, prove_range.
      eapply prove_membership_valid; [exact hc |].
      unfold msgs_range.
      rewrite (nth_enum _ _ (fun k => g ^ natF k)).
      unfold nat_of_Z; fin_idx_default; reflexivity.
    Qed.

    (* the re-encryption proof *)
    Lemma reenc_dec_valid : ∀ (x : F) (g h : G) (c : G2) (D : nat) (rD u cc : F),
      h = g ^ x -> cdec x c = g ^ natF D ->
      let c' := cmul (enc g h (natF D) rD) (cinv c) in
      decryption_proof_accepting_conversations (F := F) (G := G) (ginv := ginv) 
        (gop := gop) (gpow := gpow) (Gdec := Gdec) g h (fst c') (snd c') gid
        (construct_decryption_proof_elgamal_real (F := F) (add := add) (mul := mul) 
          (G := G) (gpow := gpow) x g c' u cc) = true.
    Proof.
      intros * hh hd; destruct c as (c1, c2); cbn.
      apply construct_decryption_proof_elgamal_real_completeness.
      split; [symmetry; exact hh |].
      unfold cdec in hd; cbn in hd.
      rewrite gop_pow, ginv_pow, <- pow_mul.
      rewrite ginv_gid, gop_gid_r.
      rewrite hh, <- pow_mul.
      assert (hc2 : c2 = gop (g ^ natF D) (c1 ^ x)).
      { rewrite <- hd, <- gop_assoc, gop_ginv_l, gop_gid_r; reflexivity. }
      rewrite hc2, ginv_gop.
      rewrite gop_rearrange, gop_ginv_r, gop_gid_l.
      f_equal; f_equal; field.
    Qed.

    Lemma to_nat_le : ∀ (z : Z) (k : nat), (z <= Z.of_nat k)%Z -> Z.to_nat z <= k.
    Proof.
      intros z k hz; destruct z as [| q | q]; [cbn; lia | | cbn; lia].
      rewrite <- (Nat2Z.id k); apply Z2Nat.inj_le; lia.
    Qed.

    Lemma defeat_statements_nth : ∀ (n n' : nat) (g : G) 
      (encD' enc_d : Vector.t (Vector.t G2 (S n)) (S n)) (i j : Fin.t (S n)) 
      (idx : Fin.t (S (S n') + S n')),
      (defeat_statements (N := S n') g encD' enc_d i j)[@idx] =
      let Dij := mget encD' i j in
      let Dji := mget encD' j i in
      let dij := mget enc_d i j in
      let delta := cmul Dij (cinv Dji) in
      let V2 := cmul (cpow dij (natF (tally_shift (N := S n')))) delta in
      let V1 := cmul (cpow (cmul dij (cinv Dij)) (natF (tally_shift (N := S n')))) delta in
      if Nat.ltb (fin_idx idx) (S (S n')) 
      then or_statement V2 (ginv (g ^ natF (fin_idx idx)))
      else or_statement V1 (g ^ natF (S (fin_idx idx - S (S n')))).
    Proof.
      intros; unfold defeat_statements; cbv zeta.
      set (Dij := mget encD' i j).
      set (Dji := mget encD' j i).
      set (dij := mget enc_d i j).
      set (delta := cmul Dij (cinv Dji)).
      set (V2 := cmul (cpow dij (natF (tally_shift (N := S n')))) delta).
      set (V1 := cmul (cpow (cmul dij (cinv Dij)) (natF (tally_shift (N := S n')))) delta).
      exact (nth_enum_append _ (S (S n')) (S n') 
        (fun t => or_statement V2 (ginv (g ^ natF t))) 
        (fun t => or_statement V1 (g ^ natF (S t))) idx).
    Qed.

    Lemma upper_statements_nth : ∀ (n n' : nat) (g : G) 
      (enc_p : Vector.t (Vector.t G2 (S n)) (S n)) (k i j : Fin.t (S n)) 
      (idx : Fin.t (S (S n') + S (S n'))),
      (upper_statements (N := S n') g enc_p k i j)[@idx] =
      let pij := mget enc_p i j in
      let A := cmul pij (cinv (mget enc_p i k)) in
      let B := cmul pij (cinv (mget enc_p k j)) in
      if Nat.ltb (fin_idx idx) (S (S n')) 
      then or_statement A (g ^ natF (fin_idx idx))
      else or_statement B (g ^ natF (fin_idx idx - S (S n'))).
    Proof.
      intros; unfold upper_statements; cbv zeta.
      set (pij := mget enc_p i j).
      set (A := cmul pij (cinv (mget enc_p i k))).
      set (B := cmul pij (cinv (mget enc_p k j))).
      exact (nth_enum_append _ (S (S n')) (S (S n')) 
        (fun t => or_statement A (g ^ natF t)) 
        (fun t => or_statement B (g ^ natF t)) idx).
    Qed.

    Lemma edge_proofs_valid : ∀ (n n' : nat) (g h : G) 
      (d p : Fin.t (S n) -> Fin.t (S n) -> Z)
      (rd rp : Fin.t (S n) -> Fin.t (S n) -> F) (rnd : nat -> F) (chal : F) (i j : Fin.t (S n)),
      (∀ u v, (0 <= d u v <= Z.of_nat (S n'))%Z) -> (0 <= p i j)%Z ->
      ∀ (l : list (Fin.t (S n))) (u : Fin.t (S n)) (e : nat),
      edges_ge d (p i j) u l ->
      verify_edges (N := S n') g h 
        (mat_of (n := n) (fun a b => enc g h (natF (nat_of_Z (d a b))) (rd a b)))
        (mget (mat_of (n := n) (fun a b => enc g h (natF (nat_of_Z (p a b))) (rp a b))) i j) u l
        (edge_proofs (n' := n') g h d p 
          (mat_of (n := n) (fun a b => enc g h (natF (nat_of_Z (d a b))) (rd a b)))
          (mat_of (n := n) (fun a b => enc g h (natF (nat_of_Z (p a b))) (rp a b))) 
          rd rp rnd chal i j u l e) = true.
    Proof.
      intros * hd hp l; induction l as [| v l' ih]; intros u e hl.
      + reflexivity.
      + destruct hl as (hv & hl'); cbn [edge_proofs verify_edges].
        apply Bool.andb_true_iff; split.
        - rewrite !mget_mat_of, enc_div.
          apply prove_range_valid; [specialize (hd u v); lia |].
          apply enc_ext; [| reflexivity].
          unfold nat_of_Z; rewrite natF_Z_sub; [reflexivity | specialize (hd u v); lia].
        - apply ih; exact hl'.
    Qed.

    (* encD encrypts the margin matrix D under x *)
    Definition encrypts {m : nat} (x : F) (g : G) 
      (encD : Vector.t (Vector.t (G * G) m) m) (D : Fin.t m -> Fin.t m -> Z) : Prop :=
      ∀ i j, cdec x (mget encD i j) = g ^ natF (Z.to_nat (D i j)).

    (* completeness: honest trustees with a correct plaintext certificate 
       produce an accepting transcript *)
    Theorem verify_tally_complete : ∀ (n n' : nat) (x : F) (g h : G) 
      (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) 
      (D p : Fin.t (S n) -> Fin.t (S n) -> Z) 
      (paths : Fin.t (S n) -> Fin.t (S n) -> list (Fin.t (S n)))
      (w : Fin.t (S n)) (rnd : nat -> F) (chal : F),
      h = g ^ x -> encrypts x g encD D -> 
      (∀ i j, (0 <= D i j <= Z.of_nat (S n'))%Z) ->
      cert_ok (defeat D) p paths -> schulze_winner p w ->
      verify_tally (N := S n') g h encD w 
        (generate_tally_with (n' := n') x g h encD D p paths w rnd chal) = true.
    Proof.
      intros * hh he hb hc hw.
      assert (hdN : ∀ i j, (0 <= defeat D i j <= Z.of_nat (S n'))%Z) 
        by (intros i j; pose proof (defeat_le D i j (proj1 (hb i j))); specialize (hb i j); lia).
      pose proof (cert_ok_bound _ _ _ _ (fun i j => proj2 (hdN i j)) hc) as hpN.
      assert (hp0 : ∀ i j, (0 <= p i j)%Z) 
        by (intros i j; destruct hc as (h1 & _); specialize (h1 i j); specialize (hdN i j); lia).
      destruct hc as (hc1 & hc2 & hc3).
      unfold verify_tally, tally_checks, generate_tally_with; 
      cbn [List.forallb tp_encD' tp_dec tp_enc_d tp_enc_p tp_d_range tp_defeat 
        tp_lower tp_upper tp_paths tp_edges tp_winner].
      rewrite !Bool.andb_true_iff; repeat split; try reflexivity.
      (* 1. re-encryption *)
      - unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite !mget_mat_of.
        apply reenc_dec_valid; [exact hh | apply he].
      (* 2. d in range *)
      - unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite !mget_mat_of.
        apply prove_range_valid; [apply hdN | reflexivity].
      (* 3. the defeat disjunction *)
      - unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite !mget_mat_of.
        pose proof (hb i j) as hbij; pose proof (hb j i) as hbji.
        destruct (Z.ltb 0 (D i j - D j i)) eqn:hlt.
        + apply Z.ltb_lt in hlt.
          assert (hd : defeat D i j = D i j) 
            by (unfold defeat; rewrite (proj2 (Z.ltb_lt _ _)); lia).
          pose proof (to_nat_le (D i j - D j i) (S n') ltac:(lia)) as hle.
          apply prove_or_valid.
          etransitivity; [exact (defeat_statements_nth _ _ _ _ _ _ _ _) |]; cbv zeta.
          unfold nat_of_Z in *; fin_idx_default.
          rewrite (proj2 (Nat.ltb_ge _ _)); [| lia].
          rewrite !mget_mat_of.
          repeat (rewrite enc_div || rewrite enc_pow || rewrite enc_mul).
          apply or_statement_enc_ext; [field |].
          replace (S (S n' + Z.to_nat (D i j - D j i) - S (S n'))) 
            with (Z.to_nat (D i j - D j i)) by lia.
          rewrite hd, natF_Z_sub; [| lia].
          f_equal; field.
        + apply Z.ltb_ge in hlt.
          assert (hd : defeat D i j = 0%Z) 
            by (unfold defeat; rewrite (proj2 (Z.ltb_ge _ _)); lia).
          pose proof (to_nat_le (- (D i j - D j i)) (S n') ltac:(lia)) as hle.
          apply prove_or_valid.
          etransitivity; [exact (defeat_statements_nth _ _ _ _ _ _ _ _) |]; cbv zeta.
          unfold nat_of_Z in *; fin_idx_default.
          rewrite (proj2 (Nat.ltb_lt _ _)); [| lia].
          rewrite !mget_mat_of.
          repeat (rewrite enc_div || rewrite enc_pow || rewrite enc_mul).
          apply or_statement_enc_ext; [field |].
          rewrite <- pow_opp; f_equal.
          rewrite hd; cbn [Z.to_nat].
          replace (- (D i j - D j i))%Z with (D j i - D i j)%Z by lia.
          rewrite natF_Z_sub; [| lia].
          cbn [nat_to_F]; field.
      (* 4. p ≥ d *)
      - unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite !mget_mat_of, enc_div.
        pose proof (hc1 i j); pose proof (hdN i j); pose proof (hpN i j).
        apply prove_range_valid; [lia |].
        apply enc_ext; [| reflexivity].
        unfold nat_of_Z; rewrite natF_Z_sub; [reflexivity | lia].
      (* 5. one-step closed *)
      - apply forall_fin_true; intro k; unfold forall_pairs; 
        apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite (Vector.nth_map _ _ k k eq_refl), fin_enum_nth, !mget_mat_of.
        pose proof (hc2 i j k) as hmin; pose proof (hpN i j); pose proof (hpN i k); 
        pose proof (hpN k j); pose proof (hp0 i j); pose proof (hp0 i k); pose proof (hp0 k j).
        destruct (Z.leb (p i k) (p i j)) eqn:hle.
        + apply Z.leb_le in hle.
          pose proof (to_nat_le (p i j - p i k) (S n') ltac:(lia)) as hle'.
          apply prove_or_valid.
          etransitivity; [exact (upper_statements_nth _ _ _ _ _ _ _ _) |]; cbv zeta.
          unfold nat_of_Z in *; fin_idx_default.
          rewrite (proj2 (Nat.ltb_lt _ _)); [| lia].
          rewrite !mget_mat_of, enc_div.
          apply or_statement_enc_ext; [reflexivity |].
          rewrite natF_Z_sub; [reflexivity | lia].
        + apply Z.leb_gt in hle.
          destruct (Z.min_spec (p i k) (p k j)) as [[? ?] | [? ?]]; [lia |].
          pose proof (to_nat_le (p i j - p k j) (S n') ltac:(lia)) as hle'.
          apply prove_or_valid.
          etransitivity; [exact (upper_statements_nth _ _ _ _ _ _ _ _) |]; cbv zeta.
          unfold nat_of_Z in *; fin_idx_default.
          rewrite (proj2 (Nat.ltb_ge _ _)); [| lia].
          rewrite !mget_mat_of, enc_div.
          apply or_statement_enc_ext; [reflexivity |].
          replace (S (S n') + Z.to_nat (p i j - p k j) - S (S n')) 
            with (Z.to_nat (p i j - p k j)) by lia.
          rewrite natF_Z_sub; [reflexivity | lia].
      (* 6. witness paths *)
      - unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite !mget_mat_of.
        destruct (hc3 i j) as (hpath & hstr).
        unfold verify_path.
        destruct (paths i j) as [| u l] eqn:hl; [contradiction |].
        destruct hpath as (-> & hne & hlast).
        destruct (Fin.eq_dec i i) as [_ | hneq]; [| contradiction].
        destruct l as [| v l']; [contradiction |].
        destruct (Fin.eq_dec (List.last (v :: l')%list i) j) as [_ | hneq]; [| contradiction].
        cbn [andb].
        apply edge_proofs_valid; [exact hdN | apply hp0 |].
        apply strength_edges_ge; [exact hne | exact hstr].
      (* 7. winner *)
      - apply forall_fin_true; intro j.
        rewrite (Vector.nth_map _ _ j j eq_refl), fin_enum_nth, !mget_mat_of, enc_div.
        pose proof (hw j); pose proof (hpN w j); pose proof (hp0 j w).
        apply prove_range_valid; [lia |].
        apply enc_ext; [| reflexivity].
        unfold nat_of_Z; rewrite natF_Z_sub; [reflexivity | lia].
    Qed.

    (* the wrapper generate_tally, whose plaintext certificate is computed by 
       minmax_closure and witness_path: complete whenever the computed 
       certificate passes the boolean check (the trustees run it before 
       publishing) and the decrypted margins are the true ones *)
    Corollary verify_tally_complete_auto : ∀ (n n' : nat) (x : F) (g h : G) 
      (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) (w : Fin.t (S n)) (rnd : nat -> F) (chal : F),
      h = g ^ x ->
      let D := fun_of (n := n) (decrypt_margins (n := n) (n' := n') x g encD) in
      let d := defeat D in
      let p := minmax_closure d in
      encrypts x g encD D -> 
      (∀ i j, (0 <= D i j <= Z.of_nat (S n'))%Z) ->
      cert_ok_b d p (witness_path d p) = true -> schulze_winner_b p w = true ->
      verify_tally (N := S n') g h encD w (generate_tally (n' := n') x g h encD w rnd chal) = true.
    Proof.
      intros * hh D d p he hb hc hw.
      unfold generate_tally; cbv zeta.
      apply verify_tally_complete; auto using cert_ok_b_sound, schulze_winner_b_sound.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* soundness                                 *)

    Local Notation exp_injective := (Schulze.exp_injective (gpow := gpow)).
    Local Notation natF_injective := 
      (Schulze.natF_injective (zero := zero) (one := one) (add := add)).
    Local Notation cdec_cmul := (cdec_cmul (Hvec := Hvec)).
    Local Notation cdec_cinv := (cdec_cinv (Hvec := Hvec)).
    Local Notation cdec_cpow := (cdec_cpow (Hvec := Hvec)).
    Local Notation cdec_msg := (cdec_msg (Hvec := Hvec)).
    Local Notation gop_cancel_r := (gop_cancel_r (Hvec := Hvec)).
    Local Notation natF_mul := (natF_mul (Hvec := Hvec)).
    Local Notation natF_add := (natF_add (Hvec := Hvec)).

    (* the discrete-log search of the honest trustees is correct when 
       exponentiation is injective and the field has characteristic > N *)
    Lemma dlog_le_some : ∀ (g y : G) (N k : nat), 
      dlog_le g y N = Some k -> y = g ^ natF k ∧ k <= N.
    Proof.
      intros g y N; induction N as [| N ih]; intros k h; revert h; cbn.
      + destruct (Gdec _ _) as [e | ne]; intro h;
          [injection h as <-; split; [exact e | lia] | discriminate].
      + destruct (dlog_le g y N) as [r |] eqn:hr; intro h.
        * injection h as <-; destruct (ih r eq_refl) as (h1 & h2); split; [exact h1 | lia].
        * revert h; destruct (Gdec _ _) as [e | ne]; intro h;
            [injection h as <-; split; [exact e | lia] | discriminate].
    Qed.

    Lemma dlog_le_found : ∀ (g : G) (N k : nat), k <= N -> dlog_le g (g ^ natF k) N <> None.
    Proof.
      intros g N; induction N as [| N ih]; intros k hk; cbn.
      + assert (k = 0) by lia; subst k.
        destruct (Gdec _ _) as [e | ne]; [discriminate | exfalso; exact (ne eq_refl)].
      + destruct (dlog_le g (g ^ natF k) N) as [r |] eqn:hr; [discriminate |].
        destruct (Gdec _ _) as [e | ne]; [discriminate |].
        destruct (Nat.eq_dec k (S N)) as [-> | hne]; [exfalso; exact (ne eq_refl) |].
        exfalso; exact (ih k ltac:(lia) hr).
    Qed.

    Lemma dlog_le_inj : ∀ (g : G) (N k : nat), exp_injective g -> natF_injective N -> k <= N ->
      dlog_le g (g ^ natF k) N = Some k.
    Proof.
      intros g N k hinj hchar hk.
      destruct (dlog_le g (g ^ natF k) N) as [r |] eqn:hr.
      + destruct (dlog_le_some _ _ _ _ hr) as (h1 & h2).
        f_equal; apply hchar; [exact h2 | exact hk | apply hinj; exact (Logic.eq_sym h1)].
      + exfalso; exact (dlog_le_found g N k hk hr).
    Qed.

    Lemma decrypt_margins_correct : ∀ (n n' : nat) (x : F) (g : G) 
      (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) (D : Fin.t (S n) -> Fin.t (S n) -> Z),
      exp_injective g -> natF_injective (S n') -> encrypts x g encD D ->
      (∀ i j, (0 <= D i j <= Z.of_nat (S n'))%Z) ->
      fun_of (n := n) (decrypt_margins (n := n) (n' := n') x g encD) = D.
    Proof.
      intros * hinj hchar he hb.
      apply functional_extensionality_dep; intro i. 
      apply functional_extensionality_dep; intro j.
      unfold fun_of, decrypt_margins, mget.
      rewrite (Vector.nth_map _ _ i i eq_refl), (Vector.nth_map _ _ j j eq_refl).
      specialize (he i j); unfold mget in he; rewrite he.
      specialize (hb i j).
      assert (hle : Z.to_nat (D i j) <= S n').
      { apply Nat2Z.inj_le; rewrite Z2Nat.id; lia. }
      rewrite (dlog_le_inj g (S n') (Z.to_nat (D i j)) hinj hchar hle).
      rewrite Z2Nat.id; lia.
    Qed.

    (* completeness stated with the true margins D: the honest trustees 
       decrypt them correctly *)
    Corollary verify_tally_complete_inj : ∀ (n n' : nat) (x : F) (g h : G) 
      (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) 
      (D : Fin.t (S n) -> Fin.t (S n) -> Z) (w : Fin.t (S n)) (rnd : nat -> F) (chal : F),
      h = g ^ x -> exp_injective g -> natF_injective (S n') ->
      encrypts x g encD D -> (∀ i j, (0 <= D i j <= Z.of_nat (S n'))%Z) ->
      let d := defeat D in
      let p := minmax_closure d in
      cert_ok_b d p (witness_path d p) = true -> schulze_winner_b p w = true ->
      verify_tally (N := S n') g h encD w (generate_tally (n' := n') x g h encD w rnd chal) = true.
    Proof.
      intros * hh hinj hchar he hb d p hc hw.
      pose proof (verify_tally_complete_auto n n' x g h encD w rnd chal hh) as hauto.
      cbv zeta in hauto.
      rewrite (decrypt_margins_correct n n' x g encD D hinj hchar he hb) in hauto.
      exact (hauto he hb hc hw).
    Qed.

    (* extractor for a disjunction over G × G *)
    Lemma or_statement_sound : ∀ (g h : G) (V : G2) (msg : G) (y : F), 
      or_statement V msg = gpow2 (g, h) y -> V = (g ^ y, gop msg (h ^ y)).
    Proof.
      intros g h [v1 v2] msg y he; unfold or_statement, gpow2, psmul in he; cbn in he.
      injection he as h1 h2; subst v1; f_equal.
      rewrite <- h2, (gop_comm v2), gop_assoc, gop_ginv_r, gop_gid_l; reflexivity.
    Qed.

    Lemma or_sound : ∀ (g h : G) (k : nat) (hs : Vector.t G2 (2 + k)) (pf pf' : or_proof (2 + k)),
      Sigma.announcement pf = Sigma.announcement pf' -> 
      Vector.hd (Sigma.challenge pf) <> Vector.hd (Sigma.challenge pf') ->
      verify_or g h hs pf = true -> verify_or g h hs pf' = true -> 
      ∃ (f : Fin.t (2 + k)) (y : F), hs[@f] = gpow2 (g, h) y.
    Proof.
      intros * ha hc h1 h2.
      destruct pf as [a c r]; destruct pf' as [a' c' r']; cbn in ha, hc; subst a'.
      destruct (vector_inv_S c) as (c0 & cs & ->).
      destruct (vector_inv_S c') as (c0' & cs' & ->); cbn in hc.
      unfold verify_or in h1, h2.
      destruct (generalised_or_sigma_soundness_main (Hvec := vspace2) 
        (Vector.const (g, h) (2 + k)) hs a c0 c0' cs cs' r r' h1 h2 hc) as (f & y & hf).
      exists f, y; rewrite <- hf, Vector.const_nth; reflexivity.
    Qed.

    (* a range proof: the ciphertext decrypts to some t ≤ N *)
    Lemma range_sound : ∀ (n' : nat) (x : F) (g h : G) (cp : G2) 
      (pf pf' : membership_proof (S (S n'))),
      h = g ^ x ->
      Sigma.announcement pf = Sigma.announcement pf' -> 
      Vector.hd (Sigma.challenge pf) <> Vector.hd (Sigma.challenge pf') ->
      verify_range (N := S n') g h cp pf = true -> verify_range (N := S n') g h cp pf' = true ->
      ∃ t : nat, t <= S n' ∧ cdec x cp = g ^ natF t.
    Proof.
      intros * hh ha hc h1 h2; unfold verify_range in h1, h2.
      destruct (membership_sound (Hvec := Hvec) n' g h (msgs_range (N := S n') g) cp pf pf' 
        ha hc h1 h2) as (f & y & hf).
      exists (fin_idx f); split; [pose proof (fin_idx_lt _ f); lia |].
      rewrite (cdec_msg x g h cp _ y hh hf); unfold msgs_range.
      rewrite (nth_enum _ _ (fun k => g ^ natF k)); reflexivity.
    Qed.

    (* a re-encryption proof: both ciphertexts decrypt to the same element *)
    Lemma reenc_sound : ∀ (x : F) (g h : G) (c c' : G2) (pf pf' : @sigma_proto F G 2 1 1),
      h = g ^ x -> exp_injective g ->
      Sigma.announcement pf = Sigma.announcement pf' -> 
      Vector.hd (Sigma.challenge pf) <> Vector.hd (Sigma.challenge pf') ->
      decryption_proof_accepting_conversations (F := F) (G := G) (ginv := ginv) 
        (gop := gop) (gpow := gpow) (Gdec := Gdec) g h 
        (fst (cmul c' (cinv c))) (snd (cmul c' (cinv c))) gid pf = true ->
      decryption_proof_accepting_conversations (F := F) (G := G) (ginv := ginv) 
        (gop := gop) (gpow := gpow) (Gdec := Gdec) g h 
        (fst (cmul c' (cinv c))) (snd (cmul c' (cinv c))) gid pf' = true ->
      cdec x c' = cdec x c.
    Proof.
      intros * hh hinj ha hc h1 h2.
      destruct pf as [a cv r]; destruct pf' as [a' cv' r']; cbn in ha, hc; subst a'.
      destruct (vector_inv_S cv) as (c0 & cs & ->).
      destruct (vector_inv_S cv') as (c0' & cs' & ->); cbn in hc.
      destruct (vector_inv_S r) as (r0 & rs & ->).
      destruct (vector_inv_S r') as (r0' & rs' & ->).
      rewrite (vector_inv_0 cs), (vector_inv_0 cs'), (vector_inv_0 rs), (vector_inv_0 rs') in *.
      destruct (special_soundness_construct_decryption_proof_elgamal (Hvec := Hvec) 
        g h gid _ _ a c0 r0 c0' r0' hc h1 h2) as (y & hy & hcp).
      rewrite hh in hy; apply hinj in hy; subst y.
      rewrite ginv_gid, gop_gid_r in hcp.
      assert (hd : cdec x (cmul c' (cinv c)) = gid) 
        by (unfold cdec; rewrite <- hcp; apply gop_ginv_r).
      rewrite cdec_cmul, cdec_cinv in hd.
      apply (f_equal (fun z => gop z (cdec x c))) in hd.
      rewrite <- gop_assoc, gop_ginv_l, gop_gid_r, gop_gid_l in hd; exact hd.
    Qed.

    (* the defeat disjunction, decrypted *)
    Lemma defeat_sound : ∀ (n n' : nat) (x : F) (g h : G) 
      (encD' enc_d : Vector.t (Vector.t G2 (S n)) (S n)) (i j : Fin.t (S n))
      (pf pf' : or_proof (S (S n') + S n')),
      h = g ^ x ->
      Sigma.announcement pf = Sigma.announcement pf' -> 
      Vector.hd (Sigma.challenge pf) <> Vector.hd (Sigma.challenge pf') ->
      verify_or g h (defeat_statements (N := S n') g encD' enc_d i j) pf = true ->
      verify_or g h (defeat_statements (N := S n') g encD' enc_d i j) pf' = true ->
      let Dij := cdec x (mget encD' i j) in
      let Dji := cdec x (mget encD' j i) in
      let dij := cdec x (mget enc_d i j) in
      let K := natF (tally_shift (N := S n')) in
      ∃ t : nat, 
        (t <= S n' ∧ gop (dij ^ K) (gop Dij (ginv Dji)) = ginv (g ^ natF t)) ∨
        (t < S n' ∧ gop ((gop dij (ginv Dij)) ^ K) (gop Dij (ginv Dji)) = g ^ natF (S t)).
    Proof.
      intros * hh ha hc h1 h2; cbv zeta.
      destruct (or_sound g h (n' + S n') _ pf pf' ha hc h1 h2) as (f & y & hf).
      pose proof (eq_trans (eq_sym (defeat_statements_nth _ _ _ _ _ _ _ f)) hf) as hf'; 
      cbv zeta in hf'.
      pose proof (fin_idx_lt (S (S n') + S n')%nat f) as hfl.
      set (fi := @fin_idx (S (S n') + S n')%nat f) in *.
      case_eq (Nat.ltb fi (S (S n'))); intro hlt; rewrite hlt in hf'; cbv beta in hf'.
      + apply Nat.ltb_lt in hlt. exists fi; left; split; [lia |].
        apply or_statement_sound in hf'.
        rewrite <- (cdec_msg x g h _ _ y hh hf'), cdec_cmul, cdec_cpow, cdec_cmul, cdec_cinv.
        reflexivity.
      + apply Nat.ltb_ge in hlt. exists (fi - S (S n')); right; split; [lia |].
        apply or_statement_sound in hf'.
        rewrite <- (cdec_msg x g h _ _ y hh hf'), cdec_cmul, cdec_cpow, !cdec_cmul, !cdec_cinv.
        reflexivity.
    Qed.

    (* the closure disjunction, decrypted *)
    Lemma upper_sound : ∀ (n n' : nat) (x : F) (g h : G) 
      (enc_p : Vector.t (Vector.t G2 (S n)) (S n)) (k i j : Fin.t (S n))
      (pf pf' : or_proof (S (S n') + S (S n'))),
      h = g ^ x ->
      Sigma.announcement pf = Sigma.announcement pf' -> 
      Vector.hd (Sigma.challenge pf) <> Vector.hd (Sigma.challenge pf') ->
      verify_or g h (upper_statements (N := S n') g enc_p k i j) pf = true ->
      verify_or g h (upper_statements (N := S n') g enc_p k i j) pf' = true ->
      ∃ t : nat, t <= S n' ∧ 
        (gop (cdec x (mget enc_p i j)) (ginv (cdec x (mget enc_p i k))) = g ^ natF t ∨
         gop (cdec x (mget enc_p i j)) (ginv (cdec x (mget enc_p k j))) = g ^ natF t).
    Proof.
      intros * hh ha hc h1 h2.
      destruct (or_sound g h (n' + S (S n')) _ pf pf' ha hc h1 h2) as (f & y & hf).
      pose proof (eq_trans (eq_sym (upper_statements_nth _ _ _ _ _ _ _ f)) hf) as hf'; 
      cbv zeta in hf'.
      pose proof (fin_idx_lt (S (S n') + S (S n'))%nat f) as hfl.
      set (fi := @fin_idx (S (S n') + S (S n'))%nat f) in *.
      case_eq (Nat.ltb fi (S (S n'))); intro hlt; rewrite hlt in hf'; cbv beta in hf'.
      + apply Nat.ltb_lt in hlt. exists fi; split; [lia | left].
        apply or_statement_sound in hf'.
        rewrite <- (cdec_msg x g h _ _ y hh hf'), cdec_cmul, cdec_cinv; reflexivity.
      + apply Nat.ltb_ge in hlt. exists (fi - S (S n')); split; [lia | right].
        apply or_statement_sound in hf'.
        rewrite <- (cdec_msg x g h _ _ y hh hf'), cdec_cmul, cdec_cinv; reflexivity.
    Qed.

    (* decoding: g^(natF a - natF b) = g^(natF t) gives a = b + t *)
    Lemma diff_decode : ∀ (B : nat) (g : G), exp_injective g -> natF_injective B -> 
      ∀ (a b t : nat), a <= B -> (b + t <= B)%nat -> 
      gop (g ^ natF a) (ginv (g ^ natF b)) = g ^ natF t -> a = (b + t)%nat.
    Proof.
      intros B g hinj hchar a b t ha hb he.
      rewrite <- pow_opp, <- pow_add in he; apply hinj in he.
      apply hchar; [lia | lia |].
      rewrite natF_add, <- he; field.
    Qed.

    (* decoding the defeat disjunction: d = 0 ∧ D_ij ≤ D_ji, or 
       d = D_ij ∧ D_ji < D_ij *)
    Lemma defeat_decode : ∀ (N : nat) (g : G), exp_injective g -> 
      natF_injective (2 * N * N + 3 * N)%nat -> 
      ∀ (kd Dij Dji t : nat), kd <= N -> Dij <= N -> Dji <= N ->
      ((t <= N ∧ gop ((g ^ natF kd) ^ natF (S (N + N))) 
          (gop (g ^ natF Dij) (ginv (g ^ natF Dji))) = ginv (g ^ natF t)) ∨
       (t < N ∧ gop ((gop (g ^ natF kd) (ginv (g ^ natF Dij))) ^ natF (S (N + N))) 
          (gop (g ^ natF Dij) (ginv (g ^ natF Dji))) = g ^ natF (S t))) ->
      (kd = 0 ∧ Dij <= Dji) ∨ (kd = Dij ∧ Dji < Dij).
    Proof.
      intros N g hinj hchar kd Dij Dji t hkd hDij hDji [(ht & he) | (ht & he)].
      + rewrite <- !pow_opp, <- !pow_mul, <- !pow_add in he; apply hinj in he.
        assert (h1 : natF (kd * S (N + N) + Dij + t) = natF Dji).
        { rewrite !natF_add, natF_mul.
          transitivity ((natF kd * natF (S (N + N)) + (natF Dij + opp (natF Dji))) 
            + natF Dji + natF t); [field | rewrite he; field]. }
        apply hchar in h1; [| nia | nia].
        left; destruct kd; [lia | nia].
      + rewrite <- !pow_opp, <- !pow_add, <- !pow_mul, <- !pow_add in he; apply hinj in he.
        assert (h1 : natF (kd * S (N + N) + Dij) = natF (Dij * S (N + N) + Dji + S t)).
        { rewrite !natF_add, !natF_mul.
          transitivity (((natF kd + opp (natF Dij)) * natF (S (N + N)) 
            + (natF Dij + opp (natF Dji))) + natF Dij * natF (S (N + N)) + natF Dji); 
          [field | rewrite he; cbn [nat_to_F]; field]. }
        apply hchar in h1; [| nia | nia].
        right.
        assert (hk : kd = Dij) by nia.
        subst; split; [reflexivity | lia].
    Qed.

    (* every edge of a walk at least s gives strength at least s *)
    Lemma edges_ge_strength : ∀ {m : nat} (d : Fin.t m -> Fin.t m -> Z) (s : Z) 
      (l : list (Fin.t m)) (u : Fin.t m),
      l <> List.nil -> edges_ge d s u l -> (s <= strength d u l)%Z.
    Proof.
      intros m d s l; induction l as [| v l' ih]; intros u hne hl.
      + contradiction.
      + destruct hl as (hv & hl).
        destruct l' as [| w l'']; [cbn; exact hv |].
        rewrite strength_cons.
        specialize (ih v ltac:(discriminate) hl).
        destruct (Z.min_spec (d u v) (strength d v (w :: l'')%list)) as [[? ?] | [? ?]]; lia.
    Qed.

    (* the decrypted edge statements along a walk *)
    Fixpoint edges_dec {n : nat} (N : nat) (x : F) (g : G) 
      (enc_d : Vector.t (Vector.t G2 (S n)) (S n)) (pij : G2) (u : Fin.t (S n)) 
      (l : list (Fin.t (S n))) : Prop :=
      match l with
      | List.nil => True
      | List.cons v l' => 
        (∃ t : nat, t <= N ∧ cdec x (cmul (mget enc_d u v) (cinv pij)) = g ^ natF t) ∧ 
        edges_dec N x g enc_d pij v l'
      end.

    Lemma verify_edges_sound : ∀ (n n' : nat) (x : F) (g h : G) 
      (enc_d : Vector.t (Vector.t G2 (S n)) (S n)) (pij : G2) 
      (l : list (Fin.t (S n))) (pfs pfs' : list (membership_proof (S (S n')))) (u : Fin.t (S n)),
      h = g ^ x ->
      List.Forall2 (fun a b => Sigma.announcement a = Sigma.announcement b) pfs pfs' ->
      List.Forall2 (fun a b => Vector.hd (Sigma.challenge a) <> Vector.hd (Sigma.challenge b)) pfs pfs' ->
      verify_edges (N := S n') g h enc_d pij u l pfs = true -> 
      verify_edges (N := S n') g h enc_d pij u l pfs' = true ->
      edges_dec (S n') x g enc_d pij u l.
    Proof.
      intros n n' x g h enc_d pij l; induction l as [| v l' ih]; intros pfs pfs' u hh ha hc h1 h2.
      + exact I.
      + destruct pfs as [| p pfs]; [discriminate |].
        destruct pfs' as [| p' pfs']; [discriminate |].
        inversion_clear ha as [| ? ? ? ? han hal]; inversion_clear hc as [| ? ? ? ? hcn hcl].
        cbn [verify_edges] in h1, h2.
        apply andb_prop in h1; destruct h1 as (h1 & h1').
        apply andb_prop in h2; destruct h2 as (h2 & h2').
        split.
        - exact (range_sound n' x g h _ p p' hh han hcn h1 h2).
        - exact (ih pfs pfs' v hh hal hcl h1' h2').
    Qed.

    Lemma edges_dec_ge : ∀ (n N : nat) (x : F) (g : G) 
      (enc_d : Vector.t (Vector.t G2 (S n)) (S n)) (pij : G2) 
      (kd : Fin.t (S n) -> Fin.t (S n) -> nat) (kp : nat) (B : nat),
      exp_injective g -> natF_injective B -> 
      (∀ u v, kd u v <= B) -> (kp + N <= B)%nat ->
      (∀ u v, cdec x (mget enc_d u v) = g ^ natF (kd u v)) -> cdec x pij = g ^ natF kp ->
      ∀ (l : list (Fin.t (S n))) (u : Fin.t (S n)),
      edges_dec N x g enc_d pij u l -> 
      edges_ge (fun u v => Z.of_nat (kd u v)) (Z.of_nat kp) u l.
    Proof.
      intros * hinj hchar hkd hkp hd hp l; induction l as [| v l' ih]; intros u hl.
      + exact I.
      + destruct hl as ((t & ht & he) & hl); split; [| exact (ih v hl)].
        rewrite cdec_cmul, cdec_cinv, hd, hp in he.
        pose proof (diff_decode B g hinj hchar (kd u v) kp t (hkd u v) ltac:(lia) he); lia.
    Qed.

    Lemma verify_path_sound : ∀ (n n' : nat) (g h : G) 
      (enc_d enc_p : Vector.t (Vector.t G2 (S n)) (S n)) (i j : Fin.t (S n)) 
      (l : list (Fin.t (S n))) (pfs : list (membership_proof (S (S n')))),
      verify_path (N := S n') g h enc_d enc_p i j l pfs = true ->
      path_from_to_b i j l = true ∧ 
      match l with 
      | List.nil => False 
      | List.cons u l' => verify_edges (N := S n') g h enc_d (mget enc_p i j) u l' pfs = true 
      end.
    Proof.
      intros * hv; unfold verify_path in hv.
      destruct l as [| u l']; [discriminate |].
      apply andb_prop in hv; destruct hv as (h1 & h2).
      split; [exact h1 | exact h2].
    Qed.

    Lemma fin_choice2 : ∀ (n : nat) (A : Type) (P : Fin.t n -> Fin.t n -> A -> Prop),
      (∀ i j, ∃ a, P i j a) -> ∃ f : Fin.t n -> Fin.t n -> A, ∀ i j, P i j (f i j).
    Proof.
      intros n A P hP.
      destruct (fin_choice n (Fin.t n -> A) (fun i f => ∀ j, P i j (f j))) as (f & hf).
      + intro i; exact (fin_choice n A (P i) (hP i)).
      + exists f; exact hf.
    Qed.

    (* two tally transcripts with the same ciphertexts, paths and 
       announcements, and different challenges in every sub-proof *)
    Definition same_tally_announcements {m N : nat} (pf pf' : @tally_proof m N) : Prop :=
      tp_encD' pf = tp_encD' pf' ∧ tp_enc_d pf = tp_enc_d pf' ∧ 
      tp_enc_p pf = tp_enc_p pf' ∧ tp_paths pf = tp_paths pf' ∧
      (∀ i j, Sigma.announcement (mget (tp_dec pf) i j) = 
        Sigma.announcement (mget (tp_dec pf') i j)) ∧
      (∀ i j, Sigma.announcement (mget (tp_d_range pf) i j) = 
        Sigma.announcement (mget (tp_d_range pf') i j)) ∧
      (∀ i j, Sigma.announcement (mget (tp_defeat pf) i j) = 
        Sigma.announcement (mget (tp_defeat pf') i j)) ∧
      (∀ i j, Sigma.announcement (mget (tp_lower pf) i j) = 
        Sigma.announcement (mget (tp_lower pf') i j)) ∧
      (∀ k i j, Sigma.announcement (mget (tp_upper pf)[@k] i j) = 
        Sigma.announcement (mget (tp_upper pf')[@k] i j)) ∧
      (∀ i j, List.Forall2 (fun a b => Sigma.announcement a = Sigma.announcement b) 
        (mget (tp_edges pf) i j) (mget (tp_edges pf') i j)) ∧
      (∀ j, Sigma.announcement (tp_winner pf)[@j] = Sigma.announcement (tp_winner pf')[@j]).

    Definition different_tally_challenges {m N : nat} (pf pf' : @tally_proof m N) : Prop :=
      (∀ i j, Vector.hd (Sigma.challenge (mget (tp_dec pf) i j)) <> 
        Vector.hd (Sigma.challenge (mget (tp_dec pf') i j))) ∧
      (∀ i j, Vector.hd (Sigma.challenge (mget (tp_d_range pf) i j)) <> 
        Vector.hd (Sigma.challenge (mget (tp_d_range pf') i j))) ∧
      (∀ i j, Vector.hd (Sigma.challenge (mget (tp_defeat pf) i j)) <> 
        Vector.hd (Sigma.challenge (mget (tp_defeat pf') i j))) ∧
      (∀ i j, Vector.hd (Sigma.challenge (mget (tp_lower pf) i j)) <> 
        Vector.hd (Sigma.challenge (mget (tp_lower pf') i j))) ∧
      (∀ k i j, Vector.hd (Sigma.challenge (mget (tp_upper pf)[@k] i j)) <> 
        Vector.hd (Sigma.challenge (mget (tp_upper pf')[@k] i j))) ∧
      (∀ i j, List.Forall2 (fun a b => Vector.hd (Sigma.challenge a) <> Vector.hd (Sigma.challenge b)) 
        (mget (tp_edges pf) i j) (mget (tp_edges pf') i j)) ∧
      (∀ j, Vector.hd (Sigma.challenge (tp_winner pf)[@j]) <> 
        Vector.hd (Sigma.challenge (tp_winner pf')[@j])).

    (* special soundness of the tally: two accepting transcripts with the 
       same announcements and different challenges, on margins D ∈ [0, N] 
       encrypted under x, certify the closure of the defeats of D and a 
       Schulze winner (cert_winner then gives the winner of the unique 
       closure). Hypotheses as for ballot_sound, with the characteristic 
       above 2N² + 3N. *)
    Theorem verify_tally_sound : ∀ (n n' : nat) (x : F) (g h : G) 
      (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) 
      (D : Fin.t (S n) -> Fin.t (S n) -> Z) (w : Fin.t (S n)) 
      (pf pf' : @tally_proof (S n) (S n')),
      h = g ^ x -> exp_injective g -> natF_injective (2 * S n' * S n' + 3 * S n')%nat ->
      encrypts x g encD D -> (∀ i j, (0 <= D i j <= Z.of_nat (S n'))%Z) ->
      same_tally_announcements pf pf' -> different_tally_challenges pf pf' ->
      verify_tally (N := S n') g h encD w pf = true -> 
      verify_tally (N := S n') g h encD w pf' = true ->
      ∃ (d p : Fin.t (S n) -> Fin.t (S n) -> Z) (paths : Fin.t (S n) -> Fin.t (S n) -> list (Fin.t (S n))),
        (∀ i j, d i j = defeat D i j) ∧ cert_ok d p paths ∧ schulze_winner p w.
    Proof.
      intros * hh hinj hchar he hb 
        (hE & hd_eq & hp_eq & hpaths_eq & ha1 & ha2 & ha3 & ha4 & ha5 & ha6 & ha7)
        (hc1 & hc2 & hc3 & hc4 & hc5 & hc6 & hc7) hv hv'.
      unfold verify_tally, tally_checks in hv, hv'; cbn [List.forallb] in hv, hv'.
      rewrite !Bool.andb_true_iff in hv, hv'.
      destruct hv as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & _).
      destruct hv' as (h1' & h2' & h3' & h4' & h5' & h6' & h7' & _).
      rewrite <- hE, <- hd_eq, <- hp_eq, <- hpaths_eq in *.
      set (encD' := tp_encD' pf) in *.
      set (enc_d := tp_enc_d pf) in *.
      set (enc_p := tp_enc_p pf) in *.
      unfold forall_pairs in *.
      assert (hpair : ∀ (f : Fin.t (S n) -> Fin.t (S n) -> bool), 
        forall_fin (S n) (fun i => forall_fin (S n) (fun j => f i j)) = true -> ∀ i j, f i j = true).
      { intros f hf i j; rewrite forall_fin_true in hf; specialize (hf i); 
        rewrite forall_fin_true in hf; exact (hf j). }
      pose proof (hpair _ h1) as h1x; pose proof (hpair _ h2) as h2x; 
      pose proof (hpair _ h3) as h3x; pose proof (hpair _ h4) as h4x; 
      pose proof (hpair _ h6) as h6x.
      pose proof (hpair _ h1') as h1x'; pose proof (hpair _ h2') as h2x'; 
      pose proof (hpair _ h3') as h3x'; pose proof (hpair _ h4') as h4x'; 
      pose proof (hpair _ h6') as h6x'.
      clear h1 h2 h3 h4 h6 h1' h2' h3' h4' h6'.
      rename h1x into h1; rename h2x into h2; rename h3x into h3; 
      rename h4x into h4; rename h6x into h6.
      rename h1x' into h1'; rename h2x' into h2'; rename h3x' into h3'; 
      rename h4x' into h4'; rename h6x' into h6'.
      rewrite forall_fin_true in h5, h5', h7, h7'.
      (* the margins as naturals *)
      set (Dn := fun i j => Z.to_nat (D i j)).
      assert (hDz : ∀ i j, D i j = Z.of_nat (Dn i j)) 
        by (intros i j; unfold Dn; rewrite Z2Nat.id; [reflexivity | apply hb]).
      assert (hDn : ∀ i j, Dn i j <= S n') by (intros i j; apply to_nat_le; apply hb).
      (* 1. the re-encryptions decrypt to the margins *)
      assert (hD' : ∀ i j, cdec x (mget encD' i j) = g ^ natF (Dn i j)).
      { intros i j; unfold Dn; rewrite <- (he i j).
        exact (reenc_sound x g h _ _ _ _ hh hinj (ha1 i j) (hc1 i j) (h1 i j) (h1' i j)). }
      (* 2. the defeats decrypt to kd ≤ N *)
      destruct (fin_choice2 _ _ (fun i j t => t <= S n' ∧ 
        cdec x (mget enc_d i j) = g ^ natF t)) as (kd & hkd).
      { intros i j; exact (range_sound n' x g h _ _ _ hh (ha2 i j) (hc2 i j) (h2 i j) (h2' i j)). }
      (* 4. the lower proofs: p / d decrypts to kl ≤ N, so p decrypts to kl + kd *)
      destruct (fin_choice2 _ _ (fun i j t => t <= S n' ∧ 
        cdec x (cmul (mget enc_p i j) (cinv (mget enc_d i j))) = g ^ natF t)) as (kl & hkl).
      { intros i j; exact (range_sound n' x g h _ _ _ hh (ha4 i j) (hc4 i j) (h4 i j) (h4' i j)). }
      assert (hkp : ∀ i j, cdec x (mget enc_p i j) = g ^ natF (kl i j + kd i j)).
      { intros i j; destruct (hkl i j) as (_ & hl).
        rewrite cdec_cmul, cdec_cinv, (proj2 (hkd i j)) in hl.
        apply (f_equal (fun z => gop z (g ^ natF (kd i j)))) in hl.
        rewrite <- gop_assoc, gop_ginv_l, gop_gid_r in hl.
        rewrite hl, natF_add, pow_add; reflexivity. }
      exists (fun i j => Z.of_nat (kd i j)), (fun i j => Z.of_nat (kl i j + kd i j)), 
        (fun i j => mget (tp_paths pf) i j).
      split; [| split].
      (* 3. d = defeat D *)
      - intros i j.
        destruct (defeat_sound n n' x g h encD' enc_d i j _ _ hh (ha3 i j) (hc3 i j) 
          (h3 i j) (h3' i j)) as (t & ht); cbv zeta in ht.
        rewrite !hD', (proj2 (hkd i j)) in ht.
        unfold tally_shift in ht.
        destruct (defeat_decode (S n') g hinj hchar (kd i j) (Dn i j) (Dn j i) t 
          (proj1 (hkd i j)) (hDn i j) (hDn j i) ht) as [(hz & hle) | (heq & hlt)].
        + unfold defeat; rewrite !hDz, (proj2 (Z.ltb_ge _ _)); [| lia].
          rewrite hz; reflexivity.
        + unfold defeat; rewrite !hDz, (proj2 (Z.ltb_lt _ _)); [| lia].
          rewrite heq; reflexivity.
      - split; [| split].
        (* p ≥ d *)
        + intros i j; cbv beta; lia.
        (* 5. one-step closed *)
        + intros i j k.
          pose proof (proj1 (hkd i j)); pose proof (proj1 (hkd i k)); pose proof (proj1 (hkd k j)).
          pose proof (proj1 (hkl i j)); pose proof (proj1 (hkl i k)); pose proof (proj1 (hkl k j)).
          destruct (upper_sound n n' x g h enc_p k i j _ _ hh (ha5 k i j) (hc5 k i j) 
            (hpair _ (h5 k) i j) (hpair _ (h5' k) i j)) as (t & ht & [hu | hu]); 
          rewrite !hkp in hu.
          * pose proof (diff_decode _ g hinj hchar (kl i j + kd i j) (kl i k + kd i k) t 
              ltac:(lia) ltac:(lia) hu).
            destruct (Z.min_spec (Z.of_nat (kl i k + kd i k)) (Z.of_nat (kl k j + kd k j))) 
              as [[? ?] | [? ?]]; lia.
          * pose proof (diff_decode _ g hinj hchar (kl i j + kd i j) (kl k j + kd k j) t 
              ltac:(lia) ltac:(lia) hu).
            destruct (Z.min_spec (Z.of_nat (kl i k + kd i k)) (Z.of_nat (kl k j + kd k j))) 
              as [[? ?] | [? ?]]; lia.
        (* 6. witness paths *)
        + intros i j; cbv beta.
          destruct (verify_path_sound n n' g h enc_d enc_p i j _ _ (h6 i j)) as (hpb & hedges).
          destruct (verify_path_sound n n' g h enc_d enc_p i j _ _ (h6' i j)) as (_ & hedges').
          split; [apply path_from_to_b_sound; exact hpb |].
          destruct (mget (tp_paths pf) i j) as [| u l'] eqn:hl; [contradiction |].
          cbn [path_strength].
          apply path_from_to_b_sound in hpb; destruct hpb as (-> & hne & _).
          apply edges_ge_strength; [exact hne |].
          pose proof (proj1 (hkd i j)); pose proof (proj1 (hkl i j)).
          apply (edges_dec_ge n (S n') x g enc_d (mget enc_p i j) kd (kl i j + kd i j) 
            (2 * S n' * S n' + 3 * S n')%nat hinj hchar 
            (fun u v => ltac:(pose proof (proj1 (hkd u v)); lia)) ltac:(lia) 
            (fun u v => proj2 (hkd u v)) (hkp i j)).
          exact (verify_edges_sound n n' x g h enc_d _ l' _ _ i hh (ha6 i j) (hc6 i j) 
            hedges hedges').
      (* 7. winner *)
      - intros j; cbv beta.
        destruct (range_sound n' x g h _ _ _ hh (ha7 j) (hc7 j) (h7 j) (h7' j)) as (t & ht & hw).
        rewrite cdec_cmul, cdec_cinv, !hkp in hw.
        pose proof (proj1 (hkd w j)); pose proof (proj1 (hkd j w)); 
        pose proof (proj1 (hkl w j)); pose proof (proj1 (hkl j w)).
        pose proof (diff_decode _ g hinj hchar (kl w j + kd w j) (kl j w + kd j w) t 
          ltac:(lia) ltac:(lia) hw); lia.
    Qed.



    (* ---------------------------------------------------------------- *)
    (* Fiat-Shamir for the tally: announcements of the OR and decryption 
       provers do not depend on the witness or the challenge               *)

    Local Notation or_real := (generalised_construct_or_conversations_schnorr (F := F) 
      (zero := zero) (add := add) (mul := mul) (sub := sub) (opp := opp) (G := G2) 
      (gop := gop2) (gpow := gpow2)).

    Lemma or_real_announcement : ∀ (k : nat) (rindex : Fin.t (2 + k)) (x x' : F) 
      (gs hs : Vector.t G2 (2 + k)) (uscs : Vector.t F ((2 + k) + (1 + k))) (c c' : F),
      Sigma.announcement (or_real rindex x gs hs uscs c) = 
      Sigma.announcement (or_real rindex x' gs hs uscs c').
    Proof.
      intros; unfold generalised_construct_or_conversations_schnorr.
      destruct (splitat (2 + k) uscs) as (us & cs).
      destruct (vector_fin_app_pred (1 + k) rindex us cs) as 
        (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & _).
      destruct pfaa as [pfa]; destruct pfbb as [pfb].
      assert (hrew : ∀ (A B : nat) (e : A = B) (P : @sigma_proto F G2 B (S B) B), 
        Sigma.announcement (@eq_rect_r nat B (fun k => @sigma_proto F G2 k (S k) k) P A e) = 
        @eq_rect_r nat B (fun k => Vector.t G2 k) (Sigma.announcement P) A e) 
        by (intros A B e P; destruct e; reflexivity).
      rewrite !hrew; f_equal.
      unfold OrSigmaGen.construct_or_conversations_schnorr.
      destruct (splitat _ _) as (us' & cs').
      destruct (splitat m₁ us') as (usl & usrh).
      destruct (vector_inv_S usrh) as (u & usr & _).
      destruct (splitat m₁ cs') as (csl & csr).
      reflexivity.
    Qed.

    Lemma or_real_challenge : ∀ (k : nat) (rindex : Fin.t (2 + k)) (x : F) 
      (gs hs : Vector.t G2 (2 + k)) (uscs : Vector.t F ((2 + k) + (1 + k))) (c : F),
      Vector.hd (Sigma.challenge (or_real rindex x gs hs uscs c)) = c.
    Proof.
      intros; unfold generalised_construct_or_conversations_schnorr.
      destruct (splitat (2 + k) uscs) as (us & cs).
      destruct (vector_fin_app_pred (1 + k) rindex us cs) as 
        (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & _).
      destruct pfaa as [pfa]; destruct pfbb as [pfb].
      assert (hrew : ∀ (A B : nat) (e : A = B) (P : @sigma_proto F G2 B (S B) B), 
        Vector.hd (Sigma.challenge (@eq_rect_r nat B (fun k => @sigma_proto F G2 k (S k) k) P A e)) = 
        Vector.hd (Sigma.challenge P)) 
        by (intros A B e P; destruct e; reflexivity).
      rewrite hrew.
      unfold OrSigmaGen.construct_or_conversations_schnorr.
      destruct (splitat _ _) as (us' & cs').
      destruct (splitat m₁ us') as (usl & usrh).
      destruct (vector_inv_S usrh) as (u & usr & _).
      destruct (splitat m₁ cs') as (csl & csr).
      reflexivity.
    Qed.

    Local Notation dec_real := (construct_decryption_proof_elgamal_real (F := F) (add := add) 
      (mul := mul) (G := G) (gpow := gpow)).

    Lemma dec_real_announcement : ∀ (x x' : F) (g : G) (cp : G2) (u c c' : F),
      Sigma.announcement (dec_real x g cp u c) = Sigma.announcement (dec_real x' g cp u c').
    Proof. intros; reflexivity. Qed.

    Lemma dec_real_challenge : ∀ (x : F) (g : G) (cp : G2) (u c : F),
      Vector.hd (Sigma.challenge (dec_real x g cp u c)) = c.
    Proof. intros; reflexivity. Qed.

    (* ---------------------------------------------------------------- *)
    (* end to end: accepting ballots and an accepting certificate make w a 
       Schulze winner of the plaintext margins of the ballots' positions   *)

    Local Notation verify_ballot := (Schulze.verify_ballot (zero := zero) (one := one) 
      (add := add) (Fdec := Fdec) (ginv := ginv) (gop := gop) (gpow := gpow) (Gdec := Gdec)).

    Lemma natF_injective_mono : ∀ (B B' : nat), B' <= B -> 
      natF_injective B -> natF_injective B'.
    Proof. intros B B' hle hB a b ha hb he; apply hB; [lia | lia | exact he]. Qed.

    Theorem schulze_end_to_end : ∀ (n n' k : nat) (x : F) (g h : G) 
      (bs bs' : Vector.t (@ballot F G (S n)) k) (w : Fin.t (S n)) 
      (pf pf' : @tally_proof (S n) (S n')),
      h = g ^ x -> exp_injective g -> 
      natF_injective (4 * S n + 2 + (2 * S n' * S n' + 3 * S n'))%nat ->
      (* at most N ballots, the range of the certificate *)
      k <= S n' ->
      (* every ballot comes with a second accepting transcript on the same 
         announcements and different challenges *)
      (∀ k, same_announcements bs[@k] bs'[@k] ∧ different_challenges bs[@k] bs'[@k] ∧
        verify_ballot g h bs[@k] = true ∧ verify_ballot g h bs'[@k] = true) ->
      (* and so does the certificate, on the aggregate of the ballots *)
      same_tally_announcements pf pf' -> different_tally_challenges pf pf' ->
      verify_tally (N := S n') g h (aggregate_margins (gid := gid) (gop := gop) bs) w pf = true -> 
      verify_tally (N := S n') g h (aggregate_margins (gid := gid) (gop := gop) bs) w pf' = true ->
      ∃ (ss : Vector.t (Vector.t nat (S n)) k),
        (∀ k i, ss[@k][@i] <= S n) ∧
        let D := fun i j => Z.of_nat (margin_count ss i j) in
        ∃ (d p : Fin.t (S n) -> Fin.t (S n) -> Z) 
          (paths : Fin.t (S n) -> Fin.t (S n) -> list (Fin.t (S n))),
          (∀ i j, d i j = defeat D i j) ∧ cert_ok d p paths ∧ schulze_winner p w ∧
          (∀ p', is_closure d p' -> schulze_winner p' w).
    Proof.
      intros * hh hinj hchar hk hbal hsa hdc hv hv'.
      (* the positions of every ballot *)
      destruct (fin_choice k (Vector.t nat (S n)) (fun k' s => 
        (∀ i, s[@i] <= S n) ∧ 
        (∀ i j, plaintext_bit (ginv := ginv) (gop := gop) (gpow := gpow) x bs[@k'] i j = 
          g ^ (if Nat.ltb s[@i] s[@j] then one else zero)))) as (sf & hsf).
      { intro k'; destruct (hbal k') as (h1 & h2 & h3 & h4).
        exact (ballot_sound (Hvec := Hvec) n x g h bs[@k'] bs'[@k'] hh hinj 
          (natF_injective_mono (4 * S n + 2 + (2 * S n' * S n' + 3 * S n'))%nat 
            (4 * S n + 2)%nat ltac:(lia) hchar) h1 h2 h3 h4). }
      exists (Vector.map sf (fin_enum k)).
      split; [intros k' i; rewrite (Vector.nth_map _ _ k' k' eq_refl), fin_enum_nth; apply hsf |].
      cbv zeta.
      set (D := fun i j => Z.of_nat (margin_count (Vector.map sf (fin_enum k)) i j)).
      assert (he : encrypts x g (aggregate_margins (gid := gid) (gop := gop) bs) D).
      { intros i j; unfold D, encrypts, mget; rewrite Nat2Z.id.
        apply (cdec_aggregate (Hvec := Hvec) x g bs); intro k'.
        rewrite (Vector.nth_map _ _ k' k' eq_refl), fin_enum_nth; apply hsf. }
      assert (hb : ∀ i j, (0 <= D i j <= Z.of_nat (S n'))%Z).
      { intros i j; unfold D; pose proof (margin_count_le (Vector.map sf (fin_enum k)) i j); lia. }
      destruct (verify_tally_sound n n' x g h _ D w pf pf' hh hinj 
        (natF_injective_mono (4 * S n + 2 + (2 * S n' * S n' + 3 * S n'))%nat 
          (2 * S n' * S n' + 3 * S n')%nat ltac:(lia) hchar) he hb hsa hdc hv hv') 
        as (d & p & paths & hd & hc & hw).
      exists d, p, paths; split; [exact hd | split; [exact hc | split; [exact hw |]]].
      intros p' hp'.
      apply (cert_winner d p paths w); [| exact hc | exact hw | exact hp'].
      intros i j; rewrite hd; pose proof (defeat_le D i j (proj1 (hb i j))); lia.
    Qed.

    Lemma of_list_nth_In : ∀ (A : Type) (l : list A) (k : Fin.t (List.length l)), 
      List.In (Vector.of_list l)[@k] l.
    Proof.
      intros A l; induction l as [| a l ih]; intro k; [inversion k |].
      apply (Fin.caseS' k); [left; reflexivity | intro k'; right; apply ih].
    Qed.

    Lemma aggregate_list_of_list : ∀ (n k : nat) (bs : Vector.t (@ballot F G (S n)) k),
      aggregate_list (n := n) (Vector.to_list bs) = aggregate_margins (gid := gid) (gop := gop) bs.
    Proof.
      intros n k; induction k as [| k ih]; intro bs.
      + rewrite (vector_inv_0 bs); reflexivity.
      + destruct (vector_inv_S bs) as (b & bs' & ->).
        change (Vector.to_list (b :: bs')) with (List.cons b (Vector.to_list bs')).
        unfold aggregate_list; cbn [List.fold_right]; fold (aggregate_list (n := n) (Vector.to_list bs')).
        rewrite ih; reflexivity.
    Qed.

    (* a successful count, with rewinding transcripts for the valid ballots 
       and for the certificate, certifies the winner of the plaintext 
       margins of the valid ballots *)
    Corollary count_sound : ∀ (n n' : nat) (x : F) (g h : G) 
      (Hb : list (G * G) -> F) (Ht : list tr_item -> F)
      (us vbs inbs : list (@ballot F G (S n))) (w : Fin.t (S n)) (pf pf' : @tally_proof (S n) (S n')),
      h = g ^ x -> exp_injective g -> 
      natF_injective (4 * S n + 2 + (2 * S n' * S n' + 3 * S n'))%nat ->
      count (n' := n') g h Hb Ht (finished us vbs inbs w pf true) ->
      (∃ bs' : Vector.t (@ballot F G (S n)) (List.length vbs), ∀ k, 
        same_announcements (Vector.of_list vbs)[@k] bs'[@k] ∧ 
        different_challenges (Vector.of_list vbs)[@k] bs'[@k] ∧
        verify_ballot g h bs'[@k] = true) ->
      same_tally_announcements pf pf' -> different_tally_challenges pf pf' ->
      verify_tally (N := S n') g h (aggregate_list (n := n) vbs) w pf' = true ->
      ∃ (ss : Vector.t (Vector.t nat (S n)) (List.length vbs)),
        (∀ k i, ss[@k][@i] <= S n) ∧
        let D := fun i j => Z.of_nat (margin_count ss i j) in
        ∃ (d p : Fin.t (S n) -> Fin.t (S n) -> Z) 
          (paths : Fin.t (S n) -> Fin.t (S n) -> list (Fin.t (S n))),
          (∀ i j, d i j = defeat D i j) ∧ cert_ok d p paths ∧ schulze_winner p w ∧
          (∀ p', is_closure d p' -> schulze_winner p' w).
    Proof.
      intros * hh hinj hchar hc (bs' & hbs') hsa hdc hv'.
      destruct (count_finished_true _ _ _ _ _ _ _ _ _ hc) as (hvb & hlen & hpf).
      apply andb_prop in hpf; destruct hpf as (_ & hpf).
      rewrite <- (Vector.to_list_of_list_opp vbs) in hpf, hv'.
      rewrite aggregate_list_of_list in hpf, hv'.
      apply (schulze_end_to_end n n' (List.length vbs) x g h (Vector.of_list vbs) bs' w pf pf' 
        hh hinj hchar hlen); try assumption.
      intro k; destruct (hbs' k) as (h1 & h2 & h3).
      pose proof (hvb _ (of_list_nth_In _ vbs k)) as hb.
      unfold Schulze.nizk_verify_ballot in hb; apply andb_prop in hb; destruct hb as (_ & hb).
      split; [exact h1 | split; [exact h2 | split; [exact hb | exact h3]]].
    Qed.

    (* ---------------------------------------------------------------- *)
    (* completeness of the non-interactive tally                          *)

    Lemma tr_mat_pf_ext : ∀ {n : nat} {A : Type} (M M' : Vector.t (Vector.t A (S n)) (S n)) 
      (f : A -> list tr_item),
      (∀ i j, f (mget M i j) = f (mget M' i j)) -> tr_mat_pf M f = tr_mat_pf M' f.
    Proof.
      intros; unfold tr_mat_pf; f_equal; f_equal; apply VectorSpec.map_ext; intro i.
      f_equal; f_equal; apply VectorSpec.map_ext; intro j; auto.
    Qed.

    Lemma edge_proofs_ann : ∀ (n n' : nat) (g h : G) 
      (d p : Fin.t (S n) -> Fin.t (S n) -> Z) (enc_d enc_p : Vector.t (Vector.t G2 (S n)) (S n))
      (rd rp : Fin.t (S n) -> Fin.t (S n) -> F) (rnd : nat -> F) (c c' : F) (i j : Fin.t (S n))
      (l : list (Fin.t (S n))) (u : Fin.t (S n)) (e : nat),
      List.map tr_ann2 (edge_proofs (n' := n') g h d p enc_d enc_p rd rp rnd c i j u l e) = 
      List.map tr_ann2 (edge_proofs (n' := n') g h d p enc_d enc_p rd rp rnd c' i j u l e).
    Proof.
      intros * ; revert u e; induction l as [| v l' ih]; intros u e; cbn [edge_proofs List.map].
      + reflexivity.
      + f_equal; [| apply ih].
        unfold tr_ann2, prove_range; f_equal; f_equal; apply prove_membership_announcement.
    Qed.

    Lemma edge_proofs_chal : ∀ (n n' : nat) (g h : G) 
      (d p : Fin.t (S n) -> Fin.t (S n) -> Z) (enc_d enc_p : Vector.t (Vector.t G2 (S n)) (S n))
      (rd rp : Fin.t (S n) -> Fin.t (S n) -> F) (rnd : nat -> F) (c : F) (i j : Fin.t (S n))
      (l : list (Fin.t (S n))) (u : Fin.t (S n)) (e : nat),
      List.forallb (is_chal2 c) 
        (edge_proofs (n' := n') g h d p enc_d enc_p rd rp rnd c i j u l e) = true.
    Proof.
      intros *; revert u e; induction l as [| v l' ih]; intros u e; cbn [edge_proofs List.forallb].
      + reflexivity.
      + rewrite ih, Bool.andb_true_r.
        unfold is_chal2, prove_range; rewrite (prove_membership_challenge n').
        destruct (Fdec c c) as [_ | hne]; [reflexivity | contradiction].
    Qed.

    (* the transcript of the honest tally does not depend on the challenge *)
    Lemma tally_transcript_chal : ∀ (n n' : nat) (x : F) (g h : G) 
      (encD : Vector.t (Vector.t G2 (S n)) (S n)) (D p : Fin.t (S n) -> Fin.t (S n) -> Z) 
      (paths : Fin.t (S n) -> Fin.t (S n) -> list (Fin.t (S n))) (w : Fin.t (S n)) 
      (rnd : nat -> F) (c c' : F),
      tally_transcript (n' := n') encD w (generate_tally_with (n' := n') x g h encD D p paths w rnd c) = 
      tally_transcript (n' := n') encD w (generate_tally_with (n' := n') x g h encD D p paths w rnd c').
    Proof.
      intros; unfold tally_transcript, generate_tally_with; 
      cbn [tp_encD' tp_enc_d tp_enc_p tp_dec tp_d_range tp_defeat tp_lower tp_upper tp_paths 
        tp_edges tp_winner].
      f_equal; f_equal; f_equal; f_equal; f_equal; f_equal.
      (* decryption proofs *)
      f_equal.
      { apply tr_mat_pf_ext; intros i j; rewrite !mget_mat_of.
        unfold tr_ann1; f_equal; f_equal; apply dec_real_announcement. }
      (* d ranges *)
      f_equal.
      { apply tr_mat_pf_ext; intros i j; rewrite !mget_mat_of.
        unfold tr_ann2, prove_range; f_equal; f_equal; apply prove_membership_announcement. }
      (* defeats *)
      f_equal.
      { apply tr_mat_pf_ext; intros i j; rewrite !mget_mat_of; cbv zeta.
        destruct (Z.ltb 0 (D i j - D j i)); 
        unfold tr_ann2, prove_or; f_equal; f_equal; apply or_real_announcement. }
      (* lower *)
      f_equal.
      { apply tr_mat_pf_ext; intros i j; rewrite !mget_mat_of.
        unfold tr_ann2, prove_range; f_equal; f_equal; apply prove_membership_announcement. }
      (* upper *)
      f_equal.
      { f_equal; f_equal; apply VectorSpec.map_ext; intro k.
        rewrite !(Vector.nth_map _ _ k k eq_refl), !fin_enum_nth.
        apply tr_mat_pf_ext; intros i j; rewrite !mget_mat_of; cbv zeta.
        destruct (Z.leb (p i k) (p i j)); 
        unfold tr_ann2, prove_or; f_equal; f_equal; apply or_real_announcement. }
      (* edges *)
      f_equal.
      { apply tr_mat_pf_ext; intros i j; rewrite !mget_mat_of.
        destruct (paths i j) as [| u l]; [reflexivity |].
        f_equal; apply edge_proofs_ann. }
      (* winner *)
      f_equal; f_equal; apply VectorSpec.map_ext; intro j.
      rewrite !(Vector.nth_map _ _ j j eq_refl), !fin_enum_nth.
      unfold tr_ann2, prove_range; f_equal; f_equal; apply prove_membership_announcement.
    Qed.

    Theorem nizk_tally_complete : ∀ (n n' : nat) (x : F) (g h : G) (H : list tr_item -> F)
      (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) 
      (D p : Fin.t (S n) -> Fin.t (S n) -> Z) 
      (paths : Fin.t (S n) -> Fin.t (S n) -> list (Fin.t (S n)))
      (w : Fin.t (S n)) (rnd : nat -> F),
      h = g ^ x -> encrypts x g encD D -> 
      (∀ i j, (0 <= D i j <= Z.of_nat (S n'))%Z) ->
      cert_ok (defeat D) p paths -> schulze_winner p w ->
      nizk_verify_tally (n' := n') g h H encD w 
        (nizk_generate_tally_with (n' := n') x g h H encD D p paths w rnd) = true.
    Proof.
      intros * hh he hb hc hw.
      unfold nizk_verify_tally, nizk_generate_tally_with; cbv zeta.
      rewrite tally_transcript_chal with (c' := zero).
      apply Bool.andb_true_iff; split; [| apply verify_tally_complete; assumption].
      set (c := H (tally_transcript encD w (generate_tally_with x g h encD D p paths w rnd zero))).
      unfold tally_challenges_are, generate_tally_with; 
      cbn [tp_dec tp_d_range tp_defeat tp_lower tp_upper tp_edges tp_winner].
      rewrite !Bool.andb_true_iff; repeat split.
      + unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite mget_mat_of; unfold is_chal1; rewrite dec_real_challenge.
        destruct (Fdec c c) as [_ | hne]; [reflexivity | contradiction].
      + unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite mget_mat_of; unfold is_chal2, prove_range; rewrite (prove_membership_challenge n').
        destruct (Fdec c c) as [_ | hne]; [reflexivity | contradiction].
      + unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite mget_mat_of; cbv zeta; unfold is_chal2.
        destruct (Z.ltb 0 (D i j - D j i)); unfold prove_or; rewrite (or_real_challenge (n' + S n'));
        destruct (Fdec c c) as [_ | hne]; [reflexivity | contradiction | reflexivity | contradiction].
      + unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite mget_mat_of; unfold is_chal2, prove_range; rewrite (prove_membership_challenge n').
        destruct (Fdec c c) as [_ | hne]; [reflexivity | contradiction].
      + apply forall_fin_true; intro k; unfold forall_pairs; 
        apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite (Vector.nth_map _ _ k k eq_refl), fin_enum_nth, mget_mat_of; cbv zeta; unfold is_chal2.
        destruct (Z.leb (p i k) (p i j)); unfold prove_or; rewrite (or_real_challenge (n' + S (S n')));
        destruct (Fdec c c) as [_ | hne]; [reflexivity | contradiction | reflexivity | contradiction].
      + unfold forall_pairs; apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite mget_mat_of.
        destruct (paths i j) as [| u l]; [reflexivity | apply edge_proofs_chal].
      + apply forall_fin_true; intro j.
        rewrite (Vector.nth_map _ _ j j eq_refl), fin_enum_nth.
        unfold is_chal2, prove_range; rewrite (prove_membership_challenge n').
        destruct (Fdec c c) as [_ | hne]; [reflexivity | contradiction].
    Qed.

    (* ---------------------------------------------------------------- *)
    (* special honest-verifier zero knowledge of the tally                *)

    (* the relations of the honest sub-proofs, factored out of 
       verify_tally_complete *)
    Lemma reenc_relation : ∀ (x : F) (g h : G) (c : G2) (D : nat) (rD : F),
      h = g ^ x -> cdec x c = g ^ natF D ->
      let c' := cmul (enc g h (natF D) rD) (cinv c) in
      g ^ x = h ∧ (fst c') ^ x = gop (snd c') (ginv gid).
    Proof.
      intros * hh hd; destruct c as (c1, c2); cbn.
      split; [symmetry; exact hh |].
      unfold cdec in hd; cbn in hd.
      rewrite gop_pow, ginv_pow, <- pow_mul.
      rewrite ginv_gid, gop_gid_r.
      rewrite hh, <- pow_mul.
      assert (hc2 : c2 = gop (g ^ natF D) (c1 ^ x)).
      { rewrite <- hd, <- gop_assoc, gop_ginv_l, gop_gid_r; reflexivity. }
      rewrite hc2, ginv_gop.
      rewrite gop_rearrange, gop_ginv_r, gop_gid_l.
      f_equal; f_equal; field.
    Qed.

    Lemma range_index : ∀ (n' : nat) (g : G) (v : Z), (0 <= v <= Z.of_nat (S n'))%Z ->
      (msgs_range (N := S n') g)[@fin_of_nat_default (nat_of_Z v) (S n')] = g ^ natF (Z.to_nat v).
    Proof.
      intros; unfold msgs_range; rewrite (nth_enum _ _ (fun k => g ^ natF k)).
      unfold nat_of_Z; fin_idx_default; reflexivity.
    Qed.

    Lemma defeat_relation : ∀ (n n' : nat) (g h : G) (D : Fin.t (S n) -> Fin.t (S n) -> Z) 
      (rD rd : Fin.t (S n) -> Fin.t (S n) -> F) (i j : Fin.t (S n)),
      (∀ i j, (0 <= D i j <= Z.of_nat (S n'))%Z) ->
      let encD' := mat_of (n := n) (fun i j => enc g h (natF (nat_of_Z (D i j))) (rD i j)) in
      let enc_d := mat_of (n := n) (fun i j => enc g h (natF (nat_of_Z (defeat D i j))) (rd i j)) in
      let K := natF (tally_shift (N := S n')) in
      let delta := (D i j - D j i)%Z in
      let rdelta := sub (rD i j) (rD j i) in
      (if Z.ltb 0 delta 
       then (defeat_statements (N := S n') g encD' enc_d i j)
              [@fin_of_nat_default (S n' + nat_of_Z delta) (S n' + S n')] = 
            gpow2 (g, h) ((K * sub (rd i j) (rD i j)) + rdelta)
       else (defeat_statements (N := S n') g encD' enc_d i j)
              [@fin_of_nat_default (nat_of_Z (- delta)) (S n' + S n')] = 
            gpow2 (g, h) ((K * rd i j) + rdelta)).
    Proof.
      intros * hb; cbv zeta.
      pose proof (hb i j) as hbij; pose proof (hb j i) as hbji.
      destruct (Z.ltb 0 (D i j - D j i)) eqn:hlt.
      + apply Z.ltb_lt in hlt.
        assert (hd : defeat D i j = D i j) 
          by (unfold defeat; rewrite (proj2 (Z.ltb_lt _ _)); lia).
        pose proof (to_nat_le (D i j - D j i) (S n') ltac:(lia)) as hle.
        etransitivity; [exact (defeat_statements_nth _ _ _ _ _ _ _ _) |]; cbv zeta.
        unfold nat_of_Z in *; fin_idx_default.
        rewrite (proj2 (Nat.ltb_ge _ _)); [| lia].
        rewrite !mget_mat_of.
        repeat (rewrite enc_div || rewrite enc_pow || rewrite enc_mul).
        apply or_statement_enc_ext; [field |].
        replace (S (S n' + Z.to_nat (D i j - D j i) - S (S n'))) 
          with (Z.to_nat (D i j - D j i)) by lia.
        rewrite hd, natF_Z_sub; [| lia].
        f_equal; field.
      + apply Z.ltb_ge in hlt.
        assert (hd : defeat D i j = 0%Z) 
          by (unfold defeat; rewrite (proj2 (Z.ltb_ge _ _)); lia).
        pose proof (to_nat_le (- (D i j - D j i)) (S n') ltac:(lia)) as hle.
        etransitivity; [exact (defeat_statements_nth _ _ _ _ _ _ _ _) |]; cbv zeta.
        unfold nat_of_Z in *; fin_idx_default.
        rewrite (proj2 (Nat.ltb_lt _ _)); [| lia].
        rewrite !mget_mat_of.
        repeat (rewrite enc_div || rewrite enc_pow || rewrite enc_mul).
        apply or_statement_enc_ext; [field |].
        rewrite <- pow_opp; f_equal.
        rewrite hd; cbn [Z.to_nat].
        replace (- (D i j - D j i))%Z with (D j i - D i j)%Z by lia.
        rewrite natF_Z_sub; [| lia].
        cbn [nat_to_F]; field.
    Qed.

    Lemma upper_relation : ∀ (n n' : nat) (g h : G) (p : Fin.t (S n) -> Fin.t (S n) -> Z) 
      (rp : Fin.t (S n) -> Fin.t (S n) -> F) (k i j : Fin.t (S n)),
      (∀ i j, (0 <= p i j <= Z.of_nat (S n'))%Z) ->
      (Z.min (p i k) (p k j) <= p i j)%Z ->
      let enc_p := mat_of (n := n) (fun i j => enc g h (natF (nat_of_Z (p i j))) (rp i j)) in
      (if Z.leb (p i k) (p i j)
       then (upper_statements (N := S n') g enc_p k i j)
              [@fin_of_nat_default (nat_of_Z (p i j - p i k)) (S n' + S (S n'))] = 
            gpow2 (g, h) (sub (rp i j) (rp i k))
       else (upper_statements (N := S n') g enc_p k i j)
              [@fin_of_nat_default (S (S n') + nat_of_Z (p i j - p k j)) (S n' + S (S n'))] = 
            gpow2 (g, h) (sub (rp i j) (rp k j))).
    Proof.
      intros * hp hmin; cbv zeta.
      pose proof (hp i j); pose proof (hp i k); pose proof (hp k j).
      destruct (Z.leb (p i k) (p i j)) eqn:hle.
      + apply Z.leb_le in hle.
        pose proof (to_nat_le (p i j - p i k) (S n') ltac:(lia)) as hle'.
        etransitivity; [exact (upper_statements_nth _ _ _ _ _ _ _ _) |]; cbv zeta.
        unfold nat_of_Z in *; fin_idx_default.
        rewrite (proj2 (Nat.ltb_lt _ _)); [| lia].
        rewrite !mget_mat_of, enc_div.
        apply or_statement_enc_ext; [reflexivity |].
        rewrite natF_Z_sub; [reflexivity | lia].
      + apply Z.leb_gt in hle.
        destruct (Z.min_spec (p i k) (p k j)) as [[? ?] | [? ?]]; [lia |].
        pose proof (to_nat_le (p i j - p k j) (S n') ltac:(lia)) as hle'.
        etransitivity; [exact (upper_statements_nth _ _ _ _ _ _ _ _) |]; cbv zeta.
        unfold nat_of_Z in *; fin_idx_default.
        rewrite (proj2 (Nat.ltb_ge _ _)); [| lia].
        rewrite !mget_mat_of, enc_div.
        apply or_statement_enc_ext; [reflexivity |].
        replace (S (S n') + Z.to_nat (p i j - p k j) - S (S n')) 
          with (Z.to_nat (p i j - p k j)) by lia.
        rewrite natF_Z_sub; [reflexivity | lia].
    Qed.

    (* the edges of the walk u :: l with their counters *)
    Fixpoint edges_of {m : nat} (u : Fin.t m) (l : list (Fin.t m)) (e : nat) : 
      list (Fin.t m * Fin.t m * nat) :=
      match l with
      | List.nil => List.nil
      | List.cons v l' => List.cons (u, v, e) (edges_of v l' (S e))
      end.

    Lemma edges_of_ge : ∀ {m : nat} (d : Fin.t m -> Fin.t m -> Z) (s : Z) 
      (l : list (Fin.t m)) (u : Fin.t m) (e : nat) (a b : Fin.t m) (k : nat),
      edges_ge d s u l -> List.In (a, b, k) (edges_of u l e) -> (s <= d a b)%Z.
    Proof.
      intros m d s l; induction l as [| v l' ih]; intros u e a b k hl hin.
      + contradiction.
      + destruct hl as (hv & hl); destruct hin as [hin | hin].
        - injection hin as -> -> ->; exact hv.
        - exact (ih v (S e) a b k hl hin).
    Qed.

    (* the membership-proof distributions of Frontend/Schulze.v at this 
       section's operations *)
    Local Notation mem_real_dist := (Schulze.mem_real_dist (zero := zero) (add := add) 
      (mul := mul) (sub := sub) (opp := opp) (ginv := ginv) (gop := gop) (gpow := gpow)).
    Local Notation mem_sim_dist := (Schulze.mem_sim_dist (zero := zero) (add := add) 
      (sub := sub) (opp := opp) (ginv := ginv) (gop := gop) (gpow := gpow)).
    Local Notation mem_zk := (Schulze.mem_zk (Hvec := Hvec)).

    Lemma bind_perm : ∀ {A B : Type} (d d' : dist A) (f f' : A -> dist B),
      Permutation d d' -> (∀ a, Permutation (f a) (f' a)) -> 
      Permutation (Bind d f) (Bind d' f').
    Proof.
      intros * hd hf.
      eapply Permutation_trans; [apply bind_perm_left; exact hd |].
      apply bind_perm_right; intros a p _; exact (hf a).
    Qed.

    (* products of distributions *)
    Fixpoint dist_list {A : Type} (ds : list (dist A)) : dist (list A) :=
      match ds with
      | List.nil => Ret List.nil
      | List.cons d ds' => Bind d (fun a => Bind (dist_list ds') (fun l => Ret (List.cons a l)))
      end.

    Lemma dist_list_map_perm : ∀ {A B : Type} (f f' : B -> dist A) (l : list B),
      (∀ b, List.In b l -> Permutation (f b) (f' b)) -> 
      Permutation (dist_list (List.map f l)) (dist_list (List.map f' l)).
    Proof.
      intros A B f f' l; induction l as [| b l ih]; intro hp; cbn [List.map dist_list].
      + apply Permutation_refl.
      + eapply Permutation_trans; [apply bind_perm_left; apply hp; left; reflexivity |].
        apply bind_perm_right; intros a p _; apply bind_perm_left.
        apply ih; intros b' hin; apply hp; right; exact hin.
    Qed.

    Section TallyZK.
      Context (lf : list F) (Hlfn : lf <> List.nil) 
        (hnd : List.NoDup lf) (hall : ∀ y : F, List.In y lf).
      Context {n n' : nat} (x : F) (g h : G).
      Local Notation m := (S n).
      Local Notation N := (S n').
      Local Notation matrix A := (Vector.t (Vector.t A m) m).

      Definition dist_mat {A : Type} (f : Fin.t m -> Fin.t m -> dist A) : dist (matrix A) :=
        dist_vec (Vector.map (fun i => dist_vec (Vector.map (fun j => f i j) (fin_enum m))) 
          (fin_enum m)).

      Lemma dist_mat_perm : ∀ {A : Type} (f f' : Fin.t m -> Fin.t m -> dist A),
        (∀ i j, Permutation (f i j) (f' i j)) -> Permutation (dist_mat f) (dist_mat f').
      Proof.
        intros; unfold dist_mat; apply dist_vec_map_perm; intro i; 
        apply dist_vec_map_perm; intro j; auto.
      Qed.

      (* the re-encryption proofs *)
      Definition dec_real_dist (c1 : G) (c : F) : dist (@sigma_proto F G 2 1 1) :=
        construct_decryption_proof_elgamal_real_distribution (F := F) (add := add) 
          (mul := mul) (G := G) (gpow := gpow) lf Hlfn x g c1 c.
      Definition dec_sim_dist (c1 c2 : G) (c : F) : dist (@sigma_proto F G 2 1 1) :=
        construct_decryption_proof_elgama_simulator_distribution (F := F) (opp := opp) 
          (G := G) (ginv := ginv) (gop := gop) (gpow := gpow) lf Hlfn g h c1 c2 gid c.

      Lemma dec_zk : ∀ (cp : G2) (D : nat) (rD c : F), 
        h = g ^ x -> cdec x cp = g ^ natF D ->
        let c' := cmul (enc g h (natF D) rD) (cinv cp) in
        Permutation (dec_real_dist (fst c') c) (dec_sim_dist (fst c') (snd c') c).
      Proof.
        intros * hh hd; cbv zeta.
        apply (construct_decryption_proof_elgamal_special_honest_verifier_zkp_enum (Hvec := Hvec)); 
        [exact (reenc_relation x g h cp D rD hh hd) | exact hnd | exact hall].
      Qed.

      (* the range proofs *)
      Definition range_real_dist (v : Z) (r : F) (cp : G2) (c : F) : 
        dist (membership_proof (S N)) :=
        mem_real_dist lf Hlfn g h (msgs_range (N := N) g) (fin_of_nat_default (nat_of_Z v) N) r cp c.
      Definition range_sim_dist (cp : G2) (c : F) : dist (membership_proof (S N)) :=
        mem_sim_dist lf Hlfn g h (msgs_range (N := N) g) cp c.

      Lemma range_zk : ∀ (v : Z) (r : F) (cp : G2) (c : F), 
        (0 <= v <= Z.of_nat N)%Z -> cp = enc g h (natF (Z.to_nat v)) r ->
        Permutation (range_real_dist v r cp c) (range_sim_dist cp c).
      Proof.
        intros * hv hc.
        apply (mem_zk lf Hlfn hnd hall g h _ _ _ (natF (Z.to_nat v))); 
        [exact hc | apply range_index; exact hv].
      Qed.

      (* the disjunctions *)
      Definition or_real_dist {k : nat} (rindex : Fin.t (2 + k)) (r : F) 
        (hs : Vector.t G2 (2 + k)) (c : F) : dist (or_proof (2 + k)) :=
        generalised_or_schnorr_distribution (F := F) (zero := zero) (add := add) (mul := mul) 
          (sub := sub) (opp := opp) (G := G2) (gop := gop2) (gpow := gpow2) 
          lf Hlfn rindex r (Vector.const (g, h) (2 + k)) hs c.
      Definition or_sim_dist {k : nat} (hs : Vector.t G2 (2 + k)) (c : F) : dist (or_proof (2 + k)) :=
        generalised_or_simulator_distribution (F := F) (zero := zero) (add := add) 
          (sub := sub) (opp := opp) (G := G2) (gop := gop2) (gpow := gpow2) 
          lf Hlfn (Vector.const (g, h) (2 + k)) hs c.

      Lemma or_zk : ∀ (k : nat) (rindex : Fin.t (2 + k)) (r : F) (hs : Vector.t G2 (2 + k)) (c : F),
        hs[@rindex] = gpow2 (g, h) r -> Permutation (or_real_dist rindex r hs c) (or_sim_dist hs c).
      Proof.
        intros * hr.
        apply (generalised_or_special_honest_verifier_zkp_perm (Hvec := vspace2)); 
        [rewrite Vector.const_nth; exact hr | exact hnd | exact hall].
      Qed.

      (* the honest trustees' data: the aggregate encD, the plaintext 
         certificate, the randomness of their ciphertexts and the challenges *)
      Variables (encD : matrix G2) (D p : Fin.t m -> Fin.t m -> Z) 
        (paths : Fin.t m -> Fin.t m -> list (Fin.t m)) (w : Fin.t m)
        (rD rd rp : Fin.t m -> Fin.t m -> F)
        (c_dec c_rng c_def c_low : Fin.t m -> Fin.t m -> F) 
        (c_up : Fin.t m -> Fin.t m -> Fin.t m -> F) 
        (c_edge : Fin.t m -> Fin.t m -> nat -> F) (c_win : Fin.t m -> F).

      Let d := defeat D.
      Let encD' := mat_of (n := n) (fun i j => enc g h (natF (nat_of_Z (D i j))) (rD i j)).
      Let enc_d := mat_of (n := n) (fun i j => enc g h (natF (nat_of_Z (d i j))) (rd i j)).
      Let enc_p := mat_of (n := n) (fun i j => enc g h (natF (nat_of_Z (p i j))) (rp i j)).
      Let K := natF (tally_shift (N := N)).

      Definition path_edges (i j : Fin.t m) : list (Fin.t m * Fin.t m * nat) :=
        match paths i j with
        | List.nil => List.nil
        | List.cons u l => edges_of u l 0
        end.

      (* the distribution of the honest tally proof (generate_tally_with with 
         the proof randomness drawn uniformly) *)
      Definition tally_real_dist : dist (@tally_proof m N) :=
        Bind (dist_mat (fun i j => 
          dec_real_dist (fst (cmul (mget encD' i j) (cinv (mget encD i j)))) (c_dec i j))) (fun dec =>
        Bind (dist_mat (fun i j => 
          range_real_dist (d i j) (rd i j) (mget enc_d i j) (c_rng i j))) (fun d_range =>
        Bind (dist_mat (fun i j => 
          let delta := (D i j - D j i)%Z in
          let rdelta := sub (rD i j) (rD j i) in
          let hs := defeat_statements (N := N) g encD' enc_d i j in
          if Z.ltb 0 delta 
          then or_real_dist (k := n' + S n') 
            (fin_of_nat_default (N + nat_of_Z delta) (N + N)) 
            ((K * sub (rd i j) (rD i j)) + rdelta) hs (c_def i j)
          else or_real_dist (k := n' + S n') 
            (fin_of_nat_default (nat_of_Z (- delta)) (N + N)) 
            ((K * rd i j) + rdelta) hs (c_def i j))) (fun defeat_pf =>
        Bind (dist_mat (fun i j => 
          range_real_dist (p i j - d i j) (sub (rp i j) (rd i j)) 
            (cmul (mget enc_p i j) (cinv (mget enc_d i j))) (c_low i j))) (fun lower =>
        Bind (dist_vec (Vector.map (fun k => dist_mat (fun i j => 
          let hs := upper_statements (N := N) g enc_p k i j in
          if Z.leb (p i k) (p i j)
          then or_real_dist (k := n' + S (S n')) 
            (fin_of_nat_default (nat_of_Z (p i j - p i k)) (N + S N)) 
            (sub (rp i j) (rp i k)) hs (c_up k i j)
          else or_real_dist (k := n' + S (S n')) 
            (fin_of_nat_default (S N + nat_of_Z (p i j - p k j)) (N + S N)) 
            (sub (rp i j) (rp k j)) hs (c_up k i j))) (fin_enum m))) (fun upper =>
        Bind (dist_mat (fun i j => dist_list (List.map (fun '(u, v, e) => 
          range_real_dist (d u v - p i j) (sub (rd u v) (rp i j)) 
            (cmul (mget enc_d u v) (cinv (mget enc_p i j))) (c_edge i j e)) 
          (path_edges i j)))) (fun edges =>
        Bind (dist_vec (Vector.map (fun j => 
          range_real_dist (p w j - p j w) (sub (rp w j) (rp j w)) 
            (cmul (mget enc_p w j) (cinv (mget enc_p j w))) (c_win j)) (fin_enum m))) (fun winner =>
        Ret (mk_tally_proof encD' dec enc_d enc_p d_range defeat_pf lower upper 
          (mat_of paths) edges winner)))))))).

      (* the simulator: from the published ciphertexts, paths and challenges *)
      Definition tally_sim_dist : dist (@tally_proof m N) :=
        Bind (dist_mat (fun i j => 
          let c' := cmul (mget encD' i j) (cinv (mget encD i j)) in
          dec_sim_dist (fst c') (snd c') (c_dec i j))) (fun dec =>
        Bind (dist_mat (fun i j => range_sim_dist (mget enc_d i j) (c_rng i j))) (fun d_range =>
        Bind (dist_mat (fun i j => 
          or_sim_dist (k := n' + S n') (defeat_statements (N := N) g encD' enc_d i j) (c_def i j))) 
          (fun defeat_pf =>
        Bind (dist_mat (fun i j => 
          range_sim_dist (cmul (mget enc_p i j) (cinv (mget enc_d i j))) (c_low i j))) (fun lower =>
        Bind (dist_vec (Vector.map (fun k => dist_mat (fun i j => 
          or_sim_dist (k := n' + S (S n')) (upper_statements (N := N) g enc_p k i j) (c_up k i j))) 
          (fin_enum m))) (fun upper =>
        Bind (dist_mat (fun i j => dist_list (List.map (fun '(u, v, e) => 
          range_sim_dist (cmul (mget enc_d u v) (cinv (mget enc_p i j))) (c_edge i j e)) 
          (path_edges i j)))) (fun edges =>
        Bind (dist_vec (Vector.map (fun j => 
          range_sim_dist (cmul (mget enc_p w j) (cinv (mget enc_p j w))) (c_win j)) (fin_enum m))) 
          (fun winner =>
        Ret (mk_tally_proof encD' dec enc_d enc_p d_range defeat_pf lower upper 
          (mat_of paths) edges winner)))))))).

      (* SHVZK of the tally: for a correct plaintext certificate, the honest 
         proofs are distributed exactly as the simulated ones, which depend 
         only on the published ciphertexts and paths; so the tally reveals 
         nothing about the margins beyond the ciphertexts and the winner *)
      Theorem tally_zk : 
        h = g ^ x -> encrypts x g encD D -> 
        (∀ i j, (0 <= D i j <= Z.of_nat N)%Z) ->
        cert_ok d p paths -> schulze_winner p w ->
        Permutation tally_real_dist tally_sim_dist.
      Proof.
        intros hh he hb hc hw.
        assert (hdN : ∀ i j, (0 <= d i j <= Z.of_nat N)%Z) 
          by (intros i j; unfold d; pose proof (defeat_le D i j (proj1 (hb i j))); 
              specialize (hb i j); lia).
        pose proof (cert_ok_bound _ _ _ _ (fun i j => proj2 (hdN i j)) hc) as hpN.
        assert (hp0 : ∀ i j, (0 <= p i j)%Z) 
          by (intros i j; destruct hc as (h1 & _); specialize (h1 i j); specialize (hdN i j); lia).
        assert (hpb : ∀ i j, (0 <= p i j <= Z.of_nat N)%Z) by (intros; split; auto).
        destruct hc as (hc1 & hc2 & hc3).
        unfold tally_real_dist, tally_sim_dist.
        (* 1. re-encryption *)
        apply bind_perm; [apply dist_mat_perm; intros i j | intro dec].
        { unfold encD'; rewrite mget_mat_of.
          exact (dec_zk (mget encD i j) (nat_of_Z (D i j)) (rD i j) (c_dec i j) hh (he i j)). }
        (* 2. d in range *)
        apply bind_perm; [apply dist_mat_perm; intros i j | intro d_range].
        { apply range_zk; [apply hdN | unfold enc_d; rewrite mget_mat_of; reflexivity]. }
        (* 3. defeats *)
        apply bind_perm; [apply dist_mat_perm; intros i j | intro defeat_pf].
        { cbv zeta.
          pose proof (defeat_relation n n' g h D rD rd i j hb) as hr; cbv zeta in hr.
          destruct (Z.ltb 0 (D i j - D j i)) eqn:hlt; apply or_zk; exact hr. }
        (* 4. p ≥ d *)
        apply bind_perm; [apply dist_mat_perm; intros i j | intro lower].
        { pose proof (hc1 i j); pose proof (hdN i j); pose proof (hpN i j).
          apply range_zk; [lia |].
          unfold enc_p, enc_d; rewrite !mget_mat_of, enc_div.
          apply enc_ext; [| reflexivity].
          unfold nat_of_Z; rewrite natF_Z_sub; [reflexivity | lia]. }
        (* 5. closed *)
        apply bind_perm; [apply dist_vec_map_perm; intro k; apply dist_mat_perm; intros i j | intro upper].
        { cbv zeta.
          pose proof (upper_relation n n' g h p rp k i j hpb (hc2 i j k)) as hr; cbv zeta in hr.
          destruct (Z.leb (p i k) (p i j)) eqn:hle; apply or_zk; exact hr. }
        (* 6. witness paths *)
        apply bind_perm; [apply dist_mat_perm; intros i j | intro edges].
        { apply dist_list_map_perm; intros ((u, v), e) hin.
          destruct (hc3 i j) as (hpath & hstr).
          unfold path_edges in hin.
          destruct (paths i j) as [| u0 l] eqn:hl; [contradiction |].
          destruct hpath as (-> & hne & _); cbn in hstr.
          pose proof (edges_of_ge d (p i j) l i 0 u v e 
            (strength_edges_ge d (p i j) l i hne hstr) hin) as hge.
          pose proof (hdN u v); pose proof (hp0 i j).
          apply range_zk; [lia |].
          unfold enc_d, enc_p; rewrite !mget_mat_of, enc_div.
          apply enc_ext; [| reflexivity].
          unfold nat_of_Z; rewrite natF_Z_sub; [reflexivity | lia]. }
        (* 7. winner *)
        apply bind_perm; [apply dist_vec_map_perm; intro j | intro winner].
        { pose proof (hw j); pose proof (hpN w j); pose proof (hp0 j w).
          apply range_zk; [lia |].
          unfold enc_p; rewrite !mget_mat_of, enc_div.
          apply enc_ext; [| reflexivity].
          unfold nat_of_Z; rewrite natF_Z_sub; [reflexivity | lia]. }
        apply Permutation_refl.
      Qed.
    End TallyZK.

  End Proofs.
End SchulzeTally.
