Require Import Coq.Lists.List.
Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.
Require Import Shallow.lib.RTClosure.

Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Operators_Properties.
(* Require Import Coq.Arith.PeanoNat. *)

Import Assertion_S.
Import Cont.

Open Scope nat_scope.

Lemma safe_mstep_pre: forall c k st c' k' st',
  safe c k st ->
  mstep (c, k, st) (c', k', st') ->
  safe c' k' st'.
Proof.
  intros.
  remember (c, k, st) as prog.
  remember (c', k', st') as prog'.
  revert c k st Heqprog H.
  unfold mstep in H0.
  apply rt_rt1n_iff in H0.
  induction H0; intros; subst.
  - inversion Heqprog; subst; auto.
  (* - intros n.
    specialize (H0 (S n)).
    inversion H0; subst;
    [ inversion H |
      inversion H |
      inversion H |].
    apply (H3 _ _ _ H). *)
  - destruct y as [[c'' k''] st''].
    apply (IHclos_refl_trans_1n eq_refl _ _ _ eq_refl).
    intros n.
    specialize (H1 (S n)).
    inversion H1; subst;
    [ inversion H |
      inversion H |
      inversion H |].
    apply (H4 _ _ _ H).
Qed.

(* guard = triple + dead *)

Definition simulation (sim : (com * continuation) -> (com * continuation) -> Prop) : Prop := forall c1 k1 c2 k2,
sim (c1, k1) (c2, k2) ->  (* c2 simulates c1 *)
(Halt c1 k1 -> (c1, k1) = (c2, k2) \/
               forall st, exists c' k', cstep (c2, k2, st) (c', k', st) /\
                                        sim (c1, k1) (c', k')) /\
(forall st, irreducible c1 k1 st -> irreducible c2 k2 st) /\
(forall c1' k1' st st',
  cstep (c1, k1, st) (c1', k1', st') ->
  exists c2' k2',
  mstep (c2, k2, st) (c2', k2', st') /\ sim (c1', k1') (c2', k2')).

Lemma safe_sim_term : forall n c1 c2 k1 k2 st sim,
  Halt c2 k2 \/ irreducible c2 k2 st ->
  simulation sim ->
  sim (c2, k2) (c1, k1) ->
  safe_n n c1 k1 st ->
  safe_n n c2 k2 st.
Proof.
  intros.

  pose proof halt_choice c2 k2 st as [? | [? | ?]].
  - clear H.
    pose proof (H0 _ _ _ _ H1) as [? _].
    specialize (H H3).
    destruct H3 as [? | [? | ?]]; destruct H3; subst; constructor.
  - exfalso. destruct H;
    [ apply (halt_reducible_ex c2 k2 st); auto |
      apply (reducible_irreducible_ex c2 k2 st); auto].
  - pose proof H0 _ _ _ _ H1 as [_ [? _]].
    specialize (H4 _ H3).
    inversion H2; [constructor; solve_wp_0 | | | |]; exfalso;
    [ apply (halt_irreducible_ex c1 k1 st); auto; subst; auto_halt |
      apply (halt_irreducible_ex c1 k1 st); auto; subst; auto_halt |
      apply (halt_irreducible_ex c1 k1 st); auto; subst; auto_halt |]; subst.
    apply (reducible_irreducible_ex c1 k1 st); auto.
Qed.

Lemma safe_sim : forall c1 c2 k1 k2 st sim,
  simulation sim ->
  sim (c2, k2) (c1, k1) ->
  safe c1 k1 st ->
  safe c2 k2 st.
Proof.
  intros.

  pose proof halt_choice c2 k2 st.
  destruct H2 as [? | [? | ?]].
  - intros n; specialize (H1 n).
    assert (Halt c2 k2 \/ irreducible c2 k2 st); [auto |].
    apply (safe_sim_term _ _ _ _ _ _ _ H3 H H0 H1).
  - intros n.
    revert c1 k1 c2 k2 st H0 H1 H2.
    induction n; intros; [constructor |].

    pose proof H _ _ _ _ H0 as [_ [_ ?]].
    apply safe_Pre; auto; intros.
    apply H3 in H4.
    destruct H4 as (c1' & k1' & ? & ?).

    pose proof safe_mstep_pre _ _ _ _ _ _ H1 H4.
    pose proof halt_choice c' k' st' as [? | [? | ?]].
    + specialize (H6 n).
      assert (Halt c' k' \/ irreducible c' k' st'); [auto |].
      apply (safe_sim_term _ _ _ _ _ _ _ H8 H H5 H6).
    + apply (IHn _ _ _ _ _ H5 H6 H7).
    + specialize (H6 n).
      assert (Halt c' k' \/ irreducible c' k' st'); [auto |].
      apply (safe_sim_term _ _ _ _ _ _ _ H8 H H5 H6).
  - intros n; specialize (H1 n).
    assert (Halt c2 k2 \/ irreducible c2 k2 st); [auto |].
    apply (safe_sim_term _ _ _ _ _ _ _ H3 H H0 H1).
Qed.

Lemma guard_sim : forall c1 c2 k1 k2 P sim,
  simulation sim ->
  sim (c2, k2) (c1, k1) ->
  guard P c1 k1 ->
  guard P c2 k2.
Proof.
  intros.
  intros st ?.
  specialize (H1 _ H2).
  clear H2.
  apply (safe_sim _ _ _ _ _ _ H H0 H1).
Qed.

Definition dead : com := CFor CSkip CSkip.

Lemma dead_reducible : forall k st, reducible dead k st.
Proof.
  intros.
  unfold dead.
  exists (CSeq CSkip CCont), (KLoop1 CSkip CSkip :: k), st.
  constructor.
Qed.

Lemma dead_safe : forall k st, safe dead k st.
Proof.
  intros.
  intros n.

  destruct n; [constructor |].
  apply safe_Pre; [apply dead_reducible | intros].
  inversion_clear H.

  assert (n <= n); [lia |].
  remember n as m.
  rewrite Heqm in H at 1.
  rewrite Heqm.
  clear Heqm.
  revert n k st' H.

  induction m; intros.
  - inversion H; subst. constructor.
  - destruct n; [constructor |].
    apply safe_Pre;
    [exists CSkip, (KSeq CCont :: KLoop1 CSkip CSkip :: k), st'; constructor | intros].
    inversion_clear H0.
    destruct n; [constructor |].
    apply safe_Pre;
    [exists CCont, (KLoop1 CSkip CSkip :: k), st'0; constructor | intros].
    inversion_clear H0.
    destruct n; [constructor |].
    apply safe_Pre;
    [exists CSkip, (KLoop2 CSkip CSkip :: k), st'1; constructor | intros].
    inversion_clear H0.
    destruct n; [constructor |].
    apply safe_Pre;
    [exists (CSeq CSkip CCont), (KLoop1 CSkip CSkip :: k), st'2; constructor | intros].
    inversion_clear H0.
    apply IHm; omega.
Qed.

Definition start_with_KLoop2 k : Prop :=
  match k with
  | KLoop2 _ _ :: k => True
  | _ => False
  end.

Inductive seq_inv_sim : (com * continuation) -> (com * continuation) -> Prop:=
| SI_sim_id : forall c k, seq_inv_sim (c, k) (c, k)
| SI_sim_bd : forall k, seq_inv_sim (CBreak, KSeq dead :: k) (CBreak, k)
| SI_sim_cd : forall k, (*~ start_with_KLoop2 k ->*) seq_inv_sim (CCont, KSeq dead :: k) (CCont, k)
.

Lemma seq_inv_sim_is_simulation : simulation seq_inv_sim.
Proof.
  unfold simulation; intros.
  split; [| split]; intros.
  {
    destruct H0 as [? | [? | ?]]; inversion H0; subst;
    inversion H; subst; auto; right; intros.
    (* - exists CBreak, nil; split; constructor.
    - exists CCont, nil; split; constructor. *)
  }
  {
    inversion H0; subst; inversion H; subst; try constructor.
    (* exfalso; apply H3; simpl; auto. *)
  }
  {
    inversion H; subst.
    - exists c1', k1'; split; constructor; auto.
    - inversion H0; subst.
      exists CBreak, k1'; split; [apply rt_refl | constructor].
      (* apply (rt_trans _ _ (CBreak, k1, st)); constructor; auto; constructor. *)
    - inversion H0; subst.
      exists CCont, k1'; split; [apply rt_refl | constructor].
      (* apply (rt_trans _ _ (CCont, k1, st)); constructor; auto; constructor. *)
  }
Qed.

Inductive seq_sim : (com * continuation) -> (com * continuation) -> Prop :=
| S_sim_id : forall c k, seq_sim (c, k) (c, k)
| S_sim_seq : forall c1 c2 k, seq_sim (c1, KSeq c2 :: k) (CSeq c1 c2, k)
.

Lemma seq_sim_is_simulation : simulation seq_sim.
Proof.
  unfold simulation; intros.
  split; [| split]; intros.
  {
    destruct H0 as [? | [? | ?]]; inversion H0; subst;
    inversion H; subst; auto.
  }
  {
    inversion H0; subst; inversion H; subst; try constructor.
  }
  {
    inversion H; subst.
    - exists c1', k1'; split; constructor; auto.
    - exists c1', k1'; split; [eapply rt_trans | constructor]; constructor;
      [apply CS_Seq | auto].
  }
Qed.

(* Definition WP c Q R1 R2 (st : state) : Prop :=
forall k, guard Q CSkip k ->
        guard R1 CBreak k ->
        guard R2 CCont k -> safe c k st. *)

Theorem seq_inv_valid_continuation : forall P c1 c2 Q R1 R2,
valid_continuation P (CSeq c1 c2) Q R1 R2 ->
  (exists Q', (valid_continuation P c1 Q' R1 R2) /\
    (valid_continuation Q' c2 Q R1 R2)).
Proof.
  intros.

  (* strongest post *)
  exists (fun st => exists st0, Assertion_Shallow.Assertion_denote st0 P /\ mstep (c1, nil, st0) (CSkip, nil, st)).
  split.
  {
    unfold valid_continuation.
    intros.
    pose proof guard_sim _ _ _ _ _ _ seq_inv_sim_is_simulation (SI_sim_bd k) H1.
    pose proof guard_sim _ _ _ _ _ _ seq_inv_sim_is_simulation (SI_sim_cd k) H2.
    assert (guard Q CSkip (KSeq dead :: k)).
    {
      clear. intros st ? n.
      destruct n; [constructor |].
      apply safe_Pre.
      + exists dead, k, st; constructor.
      + intros. inversion H0; subst.
        apply dead_safe.
    }
    specialize (H _ H5 H3 H4).

    revert H H0; clear.
    unfold guard, Assertion_Shallow.Assertion_denote; intros.
    
    specialize (H _ H1).
    assert (forall st0, mstep (c1, nil, st) (CSkip, nil, st0) -> safe CSkip k st0); [| clear H0 H1].
    { intros. apply H0. exists st; split; auto. }

    apply (safe_sim _ _ _ _ _ _ seq_sim_is_simulation (S_sim_seq _ _ _)) in H.
    replace k with (nil ++ k); auto.
    replace (KSeq c2 :: KSeq dead :: k) with (nil ++ KSeq c2 :: KSeq dead :: k) in H; auto.
    remember (@nil KElements) as k'.
    rewrite Heqk' in *. rewrite <- Heqk'. rewrite <- Heqk' in H.
    replace (c1, nil, st) with (c1, k', st) in H2; [| subst; auto].
    clear Heqk'.

    intros n.
    revert dependent st.
    (* revert c1 k. *)
    revert c1 k'.
    induction n; [constructor | intros].

    pose proof halt_choice c1 k' st as [? | [? | ?]];
    [destruct H0 as [? | [? | ?]]; destruct H0; subst | |
      inversion H0; subst].
    - apply H2; apply rt_refl.
    - (* by H after 2 step *)
      simpl in *.
      specialize (H (S (S (S n)))).
      inversion H; subst; specialize (H3 _ _ _ (CS_SeqBreak _ _ _)).
      inversion H3; subst; specialize (H5 _ _ _ (CS_SeqBreak _ _ _)).
      auto.
    - (* by H after 2 step *)
      simpl in *.
      specialize (H (S (S (S n)))).
      inversion H; subst; specialize (H3 _ _ _ (CS_SeqCont _ _ _)).
      inversion H3; subst; specialize (H5 _ _ _ (CS_SeqCont _ _ _)).
      auto.
    - apply safe_Pre.
      { replace k with (nil ++ k); auto. apply reducible_ctx_step; auto. }
      intros.
      assert (~ Halt c1 k'); [solve_wp_0 |].
      pose proof fill_cstep_inv _ _ _ _ _ _ _ H3 H1 as (k'' & ? & ?); subst.
      apply IHn; clear n IHn.
      + intros n.
        specialize (H (S n)).
        inversion H; subst;
        [ apply nil_app_neq in H8; inversion H8 |
          apply nil_app_neq in H8; inversion H8 |
          apply nil_app_neq in H8; inversion H8 |].
        apply H7; apply cstep_ctx_step; auto.
      + intros.
        apply H2.
        apply (rt_trans cstep _ (c', k'', st')); auto; constructor; auto.
    - specialize (H (S O)).
      inversion H; subst.
      simpl in H3.
      assert (irreducible CSkip (KLoop1 c0 c3 :: k0 ++ KSeq c2 :: KSeq dead :: k) st); [constructor |].
      exfalso; apply (reducible_irreducible_ex CSkip (KLoop1 c0 c3 :: k0 ++ KSeq c2 :: KSeq dead :: k) st); auto.
    - specialize (H (S O)).
      inversion H; subst.
      simpl in H3.
      assert (irreducible CCont (KLoop2 c0 c3 :: k0 ++ KSeq c2 :: KSeq dead :: k) st); [constructor |].
      exfalso; apply (reducible_irreducible_ex CCont (KLoop2 c0 c3 :: k0 ++ KSeq c2 :: KSeq dead :: k) st); auto.
  }
  {
    unfold valid_continuation.
    intros.
    specialize (H _ H0 H1 H2); clear H0 H1 H2.
    unfold guard, Assertion_Shallow.Assertion_denote; intros ? [st1 [? ?]].
    specialize (H _ H0); clear H0.

    apply (safe_sim _ _ _ _ _ _ seq_sim_is_simulation (S_sim_seq _ _ _)) in H.
    replace (KSeq c2 :: k) with (nil ++ KSeq c2 :: k) in H; auto.
    remember (@nil KElements) as k1.
    rewrite Heqk1 in H1 at 2; clear Heqk1.

    unfold mstep in H1.
    rewrite rt_rt1n_iff in H1.
    remember (c1, k1, st1) as prog.
    remember (CSkip, nil, st) as term.
    revert dependent st1. revert c1 k1.
    induction H1; intros; subst.
    - inversion Heqprog; subst.
      intros n.
      specialize (H (S n)).
      simpl in H.
      inversion H; subst.
      apply H2; constructor.
    - destruct y as [[c1' k1'] st1'].
      apply (IHclos_refl_trans_1n eq_refl c1' k1' st1'); auto.
      intros n.
      specialize (H0 (S n)).
      inversion H0; subst;
      [apply nil_app_neq in H5; inversion H5 |
       apply nil_app_neq in H5; inversion H5 |
       apply nil_app_neq in H5; inversion H5 |].
      apply H4.
      apply cstep_ctx_step; auto.
  }
Qed.

Theorem if_seq_valid_continuation : forall P b c1 c2 c3 Q R1 R2,
  valid_continuation P (CSeq (CIf b c1 c2) c3) Q R1 R2 ->
  valid_continuation P (CIf b (CSeq c1 c3) (CSeq c2 c3)) Q R1 R2.
Proof.
Admitted.

(* Already proved in Iris-CF, leave to the last *)
Theorem nocontinue_valid_continuation : forall P c Q R1 R2 R2',
  nocontinue c ->
  valid_continuation P c Q R1 R2 ->
  valid_continuation P c Q R1 R2'.
Proof.
Admitted.

Theorem loop_nocontinue_valid_continuation : forall P c1 c2 Q R1 R2,
  nocontinue c1 ->
  nocontinue c2 ->
  valid_continuation P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  valid_continuation P (CFor c1 c2) Q R1 R2.
Proof.
  unfold valid_continuation.
  intros.
Admitted. 
