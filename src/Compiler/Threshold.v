From Stdlib Require Import Setoid
  setoid_ring.Field Lia List Utf8
  Psatz Bool Arith.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Compiler Require Import
  Lagrange Composition.

Import ListNotations.

(*
  Shamir-style threshold composition (Milestone G).

  A t-of-n threshold proof shares the top-level challenge c among n
  child challenges c_1..c_n so that they lie on a polynomial of
  degree <= n - t passing through (0, c).  The prover freely chooses
  the n - t simulated branches' challenges (n - t points), which
  together with (0, c) fix the degree-(n-t) interpolant, and must
  answer the remaining t branches honestly.

  Soundness rests on uniqueness of low-degree interpolants
  (Lagrange.v): two accepting transcripts with the same
  announcements and different top challenges induce two distinct
  degree-(n-t) interpolants; these can agree on at most n - t nodes,
  so the child challenges differ on at least t branches, each of
  which yields an extractable witness.

  The proof size is linear in n (vs the C(n,t) of the monotone
  expansion in Dsl.v).
*)
Section Threshold.

  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hfield : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div Hfield).

  #[local] Notation lag_interpF :=
    (@lag_interp F zero one add mul sub inv).
  #[local] Notation lag_interp_uniqueF :=
    (@lag_interp_unique F zero one add mul sub div opp inv Fdec Hfield).

  Definition agreeb (cs cs' : list F) (i : nat) : bool :=
    match Fdec (nth i cs zero) (nth i cs' zero) with
    | left _ => true
    | right _ => false
    end.

  (* ---------- helper list lemmas ---------- *)

  Lemma filter_partition_length :
    ∀ (A : Type) (p : A -> bool) (l : list A),
    (length (filter p l) +
     length (filter (fun x => negb (p x)) l))%nat = length l.
  Proof.
    intros A p.
    induction l as [|a l ih]; cbn.
    reflexivity.
    destruct (p a); cbn; lia.
  Qed.

  Lemma nth_map_nodup :
    ∀ (xs : list F) (idxs : list nat),
    List.NoDup idxs ->
    (∀ i, List.In i idxs -> (i < length xs)%nat) ->
    List.NoDup xs ->
    List.NoDup (List.map (fun i => nth i xs zero) idxs).
  Proof.
    intros xs.
    induction idxs as [|a idxs ih]; intros hnd hlt hxs; cbn.
    +
      constructor.
    +
      inversion hnd as [| ? ? hnin hnd']; subst.
      constructor.
      ++
        intro hin.
        eapply List.in_map_iff in hin.
        destruct hin as (j & hj & hjin).
        assert (haj : a = j).
        eapply (proj1 (List.NoDup_nth xs zero) hxs).
        eapply hlt; left; reflexivity.
        eapply hlt; right; exact hjin.
        symmetry; exact hj.
        subst; contradiction.
      ++
        eapply ih.
        exact hnd'.
        intros i hi; eapply hlt; right; exact hi.
        exact hxs.
  Qed.

  Lemma filter_seq_lt :
    ∀ (p : nat -> bool) (n i : nat),
    List.In i (filter p (seq 0 n)) -> (i < n)%nat.
  Proof.
    intros * hi.
    eapply filter_In in hi.
    destruct hi as (hi & _).
    eapply in_seq in hi.
    lia.
  Qed.

  (* ---------- the Shamir soundness core ---------- *)

  Theorem threshold_extraction :
    ∀ (n thr : nat) (xs cs cs' : list F)
      (base base' : list (F * F)) (c c' : F),
    (thr <= n)%nat ->
    List.NoDup xs ->
    length xs = n ->
    (length base <= S (n - thr))%nat ->
    (length base' <= S (n - thr))%nat ->
    lag_interpF base zero = c ->
    lag_interpF base' zero = c' ->
    (∀ i, (i < n)%nat -> lag_interpF base (nth i xs zero) = nth i cs zero) ->
    (∀ i, (i < n)%nat -> lag_interpF base' (nth i xs zero) = nth i cs' zero) ->
    c <> c' ->
    (thr <=
      length (filter (fun i => negb (agreeb cs cs' i)) (seq 0 n)))%nat.
  Proof.
    intros * hthr hnd hlen hb hb' h0 h0' hcs hcs' hne.
    set (E := filter (agreeb cs cs') (seq 0 n)).
    set (D := filter (fun i => negb (agreeb cs cs' i)) (seq 0 n)).
    pose proof (filter_partition_length _ (agreeb cs cs') (seq 0 n))
      as hpart.
    rewrite seq_length in hpart.
    fold E D in hpart.
    (* the agreement set is small *)
    assert (hEsmall : (length E <= n - thr)%nat).
    {
      destruct (Nat.le_gt_cases (length E) (n - thr)) as [hle | hgt];
      [exact hle |].
      exfalso.
      set (nodes := List.map (fun i => nth i xs zero) E).
      assert (hndE : List.NoDup E).
      eapply NoDup_filter, seq_NoDup.
      assert (hnodes_nd : List.NoDup nodes).
      eapply nth_map_nodup.
      exact hndE.
      intros i hi; rewrite hlen; eapply filter_seq_lt; exact hi.
      exact hnd.
      assert (hnodes_len : length nodes = length E).
      unfold nodes; rewrite map_length; reflexivity.
      assert (hagree : ∀ a, List.In a nodes ->
        lag_interpF base a = lag_interpF base' a).
      {
        intros a ha.
        unfold nodes in ha.
        eapply in_map_iff in ha.
        destruct ha as (i & hia & hiin).
        subst a.
        assert (hilt : (i < n)%nat).
        eapply filter_seq_lt; exact hiin.
        rewrite (hcs i hilt), (hcs' i hilt).
        unfold E in hiin.
        eapply filter_In in hiin.
        destruct hiin as (_ & hag).
        unfold agreeb in hag.
        destruct (Fdec (nth i cs zero) (nth i cs' zero)) as [he | he];
        [exact he | discriminate].
      }
      pose proof (lag_interp_uniqueF base base' nodes hnodes_nd)
        as huniq.
      assert (hbn : (length base <= length nodes)%nat).
      rewrite hnodes_len; lia.
      assert (hbn' : (length base' <= length nodes)%nat).
      rewrite hnodes_len; lia.
      pose proof (huniq hbn hbn' hagree zero) as hz.
      rewrite h0, h0' in hz.
      contradiction.
    }
    lia.
  Qed.

  (* ---------- abstract threshold protocol ---------- *)

  (* Children are an indexed family sharing one transcript type T
     (for comp_rel children of the same shape, T = comp_transcript
     r0; a Leaf's transcript type depends only on its dimensions,
     not its public data, so a t-of-n threshold over instances of
     one protocol shape is homogeneous). *)
  Section Protocol.

    Context {T : Type}.
    Variable child_verify : nat -> F -> T -> bool.
    Variable child_holds : nat -> Prop.
    Variable child_same : nat -> T -> T -> Prop.
    Hypothesis child_special_sound :
      ∀ (i : nat) (c c' : F) (t t' : T),
      c <> c' -> child_same i t t' ->
      child_verify i c t = true -> child_verify i c' t' = true ->
      child_holds i.

    Variable xs : list F.
    Hypothesis xs_nodup : List.NoDup xs.

    Definition lag_okb (n : nat) (base : list (F * F))
      (c : F) (cs : list F) : bool :=
      (match Fdec (lag_interpF base zero) c with
       | left _ => true | right _ => false end) &&
      forallb (fun i =>
        match Fdec (lag_interpF base (nth i xs zero)) (nth i cs zero)
        with left _ => true | right _ => false end)
        (seq 0 n).

    Definition thresh_verify (thr n : nat) (default : T) (c : F)
      (cs : list F) (ts : list T) (base : list (F * F)) : bool :=
      (length xs =? n) &&
      (length cs =? n) &&
      (length base <=? S (n - thr)) &&
      lag_okb n base c cs &&
      forallb (fun i => child_verify i (nth i cs zero) (nth i ts default))
        (seq 0 n).

    (* the threshold relation: at least thr of the n children hold *)
    Definition thresh_holds (thr n : nat) : Prop :=
      ∃ idxs : list nat,
        List.NoDup idxs ∧
        (thr <= length idxs)%nat ∧
        (∀ i, List.In i idxs -> (i < n)%nat ∧ child_holds i).

    Lemma lag_okb_zero :
      ∀ (n : nat) (base : list (F * F)) (c : F) (cs : list F),
      lag_okb n base c cs = true -> lag_interpF base zero = c.
    Proof.
      intros * ha.
      unfold lag_okb in ha.
      eapply andb_true_iff in ha.
      destruct ha as (ha & _).
      destruct (Fdec (lag_interpF base zero) c); [assumption | discriminate].
    Qed.

    Lemma lag_okb_nodes :
      ∀ (n : nat) (base : list (F * F)) (c : F) (cs : list F),
      lag_okb n base c cs = true ->
      ∀ i, (i < n)%nat ->
      lag_interpF base (nth i xs zero) = nth i cs zero.
    Proof.
      intros * ha i hi.
      unfold lag_okb in ha.
      eapply andb_true_iff in ha.
      destruct ha as (_ & ha).
      rewrite forallb_forall in ha.
      assert (hin : List.In i (seq 0 n)).
      eapply in_seq; lia.
      pose proof (ha i hin) as hb.
      destruct (Fdec (lag_interpF base (nth i xs zero)) (nth i cs zero));
      [assumption | discriminate].
    Qed.

    (* Threshold special soundness: two accepting transcripts with
       the same per-child announcements and different top challenges
       imply the threshold relation holds. *)
    Theorem thresh_special_sound :
      ∀ (thr n : nat) (default : T) (c c' : F)
        (cs cs' : list F) (ts ts' : list T)
        (base base' : list (F * F)),
      (thr <= n)%nat ->
      c <> c' ->
      (∀ i, (i < n)%nat ->
        child_same i (nth i ts default) (nth i ts' default)) ->
      thresh_verify thr n default c cs ts base = true ->
      thresh_verify thr n default c' cs' ts' base' = true ->
      thresh_holds thr n.
    Proof.
      intros * hthr hne hsame hv hv'.
      unfold thresh_verify in hv, hv'.
      eapply andb_true_iff in hv; destruct hv as (hv & hchild).
      eapply andb_true_iff in hv; destruct hv as (hv & hlag).
      eapply andb_true_iff in hv; destruct hv as (hv & hbase).
      eapply andb_true_iff in hv; destruct hv as (hxsn & hcsn).
      eapply andb_true_iff in hv'; destruct hv' as (hv' & hchild').
      eapply andb_true_iff in hv'; destruct hv' as (hv' & hlag').
      eapply andb_true_iff in hv'; destruct hv' as (hv' & hbase').
      eapply andb_true_iff in hv'; destruct hv' as (hxsn' & hcsn').
      eapply Nat.eqb_eq in hxsn, hcsn, hcsn'.
      eapply Nat.leb_le in hbase, hbase'.
      (* apply the extraction core *)
      set (D := filter (fun i => negb (agreeb cs cs' i)) (seq 0 n)).
      assert (hD : (thr <= length D)%nat).
      {
        eapply (threshold_extraction n thr xs cs cs' base base' c c').
        exact hthr. exact xs_nodup. exact hxsn.
        exact hbase. exact hbase'.
        eapply lag_okb_zero; exact hlag.
        eapply lag_okb_zero; exact hlag'.
        intros i hi; eapply lag_okb_nodes; [exact hlag | exact hi].
        intros i hi; eapply lag_okb_nodes; [exact hlag' | exact hi].
        exact hne.
      }
      exists D.
      split; [| split].
      +
        eapply NoDup_filter, seq_NoDup.
      +
        exact hD.
      +
        intros i hiD.
        assert (hilt : (i < n)%nat).
        eapply filter_seq_lt; exact hiD.
        split; [exact hilt |].
        (* i is a differing index: extract *)
        assert (hdiff : nth i cs zero <> nth i cs' zero).
        {
          eapply filter_In in hiD.
          destruct hiD as (_ & hng).
          unfold agreeb in hng.
          destruct (Fdec (nth i cs zero) (nth i cs' zero)) as [he | he];
          [discriminate | exact he].
        }
        rewrite forallb_forall in hchild, hchild'.
        assert (hin : List.In i (seq 0 n)).
        eapply in_seq; lia.
        eapply (child_special_sound i (nth i cs zero) (nth i cs' zero)
          (nth i ts default) (nth i ts' default)).
        exact hdiff.
        eapply hsame; exact hilt.
        eapply hchild; exact hin.
        eapply hchild'; exact hin.
    Qed.

  End Protocol.

  (* ---------- concrete instantiation over comp_rel ---------- *)
  (* A t-of-n threshold over n instances of one protocol shape r
     (e.g. n independent provers of the same statement).  The
     child transcript type is comp_transcript r, uniform across the
     n branches, so the homogeneous Protocol section applies. *)
  Section CompRelThreshold.

    Context
      {G : Type}
      {gid : G}
      {ginv : G -> G}
      {gop : G -> G -> G}
      {gpow : G -> F -> G}
      {Gdec : forall x y : G, {x = y} + {x <> y}}
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.

    Variable r : @comp_rel G.
    Variable xs : list F.
    Hypothesis xs_nodup : List.NoDup xs.

    #[local] Notation cverify :=
      (@comp_verify F sub G gid gop gpow Gdec r).
    #[local] Notation csame :=
      (@comp_same_announcement F G r).

    Theorem comp_thresh_special_sound :
      ∀ (thr n : nat) (default : @comp_transcript F G r) (c c' : F)
        (cs cs' : list F)
        (ts ts' : list (@comp_transcript F G r))
        (base base' : list (F * F)),
      (thr <= n)%nat ->
      c <> c' ->
      (∀ i, (i < n)%nat -> csame (nth i ts default) (nth i ts' default)) ->
      thresh_verify (fun _ => cverify) xs thr n default c cs ts base = true ->
      thresh_verify (fun _ => cverify) xs thr n default c' cs' ts' base' = true ->
      thresh_holds (fun _ => ∃ w, @comp_rel_holds F G gid gop gpow r w) thr n.
    Proof.
      intros * hthr hne hsame hv hv'.
      eapply (thresh_special_sound
        (fun _ => cverify)
        (fun _ => ∃ w, @comp_rel_holds F G gid gop gpow r w)
        (fun _ => csame)
        _ xs xs_nodup thr n default c c' cs cs' ts ts' base base').
      exact hthr. exact hne. exact hsame. exact hv. exact hv'.
      Unshelve.
      intros i cc cc' tt tt' hcc hs hvv hvv'.
      destruct (@comp_special_soundness F zero one add mul sub div
        opp inv Fdec G gid ginv gop gpow Gdec Hvec r cc cc' tt tt'
        hcc hs hvv hvv') as (w & hw).
      exists w; exact hw.
    Qed.

  End CompRelThreshold.

End Threshold.
