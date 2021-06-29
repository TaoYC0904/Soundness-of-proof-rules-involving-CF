Require Import Coq.Lists.List.
Require Import Shallow.lib.RTClosure.
Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.

Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Operators_Properties.

Import Assertion_S.
Import SmallS.

Lemma WP_mstep_pre: forall c k st c' k' st' Q Rb Rc,
  WP c k Q Rb Rc st ->
  mstep (c, k, st) (c', k', st') ->
  WP c' k' Q Rb Rc st'.
Proof.
  intros.
  remember (c, k, st) as prog.
  remember (c', k', st') as prog'.
  revert c k st Heqprog H.
  unfold mstep in H0.
  rewrite rt_rt1n_iff in H0.
  induction H0; intros; subst.
  - inversion Heqprog; subst; auto.
    (* intros n.
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

Lemma wp_sim_term : forall n c1 c2 k1 k2 Q Rb Rc st sim,
  Halt c2 k2 \/ irreducible c2 k2 st ->
  simulation sim ->
  sim (c2, k2) (c1, k1) ->
  WP_n n c1 k1 Q Rb Rc st ->
  WP_n n c2 k2 Q Rb Rc st.
Proof.
  intros.
  unfold simulation in H0.
  pose proof halt_choice c2 k2 st as [? | [? | ?]].
  - pose proof H0 _ _ _ _ H1 as [? _].
    specialize (H4 H3).
    inversion H4; subst; auto.
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

Lemma wp_sim : forall c1 c2 k1 k2 Q Rb Rc st sim,
  simulation sim ->
  sim (c2, k2) (c1, k1) ->
  WP c1 k1 Q Rb Rc st ->
  WP c2 k2 Q Rb Rc st.
Proof.
  intros.

  pose proof H as Hsim.
  unfold simulation in H.
  pose proof halt_choice c2 k2 st.
  destruct H2 as [? | [? | ?]].
  - pose proof H _ _ _ _ H0 as [? _].
    specialize (H3 H2).
    inversion H3; subst; auto.
  - intros n.
    revert c1 k1 c2 k2 st H0 H1 H2.
    induction n; intros; [constructor; solve_wp_0 |].

    pose proof H _ _ _ _ H0 as [_ [_ ?]].
    apply WP_Pre; auto; intros.
    apply H3 in H4.
    destruct H4 as (c1' & k1' & ? & ?).

    pose proof WP_mstep_pre _ _ _ _ _ _ _ _ _ H1 H4.
    pose proof halt_choice c' k' st' as [? | [? | ?]].
    + specialize (H6 n).
      assert (Halt c' k' \/ irreducible c' k' st'); [auto |].
      apply (wp_sim_term _ _ _ _ _ _ _ _ _ _ H8 Hsim H5 H6).
    + apply (IHn _ _ _ _ _ H5 H6 H7).
    + specialize (H6 n).
      assert (Halt c' k' \/ irreducible c' k' st'); [auto |].
      apply (wp_sim_term _ _ _ _ _ _ _ _ _ _ H8 Hsim H5 H6).

  - intros n. specialize (H1 n).
    assert (Halt c2 k2 \/ irreducible c2 k2 st); [auto |].
    apply (wp_sim_term _ _ _ _ _ _ _ _ _ _ H3 Hsim H0 H1).
Qed.

Lemma wp_bind_inv: forall c1 c2 Q R1 R2 st,
WP c1 (KSeq c2 :: nil) Q R1 R2 st ->
WP c1 nil (WP c2 nil Q R1 R2) R1 R2 st.
Proof.
  intros.

  replace (KSeq c2 :: nil) with (nil ++ KSeq c2 :: nil) in H; auto.
  remember (@nil KElements) as k.
  rewrite Heqk in *.
  rewrite <- Heqk in H at 1.
  rewrite <- Heqk at 1. clear Heqk.

  intros n.
  revert c1 k st H.
  induction n; intros.
  - constructor.
  - pose proof halt_choice c1 k st as [? | [? | ?]].
    + destruct H0 as [? | [? | ?]]; destruct H0; subst.
      * apply WP_Ter1; clear n IHn.
        unfold Assertion_Shallow.Assertion_denote.
        intros n.
        specialize (H (S n)).
        simpl in H.
        inversion H; subst.
        apply H2; constructor.
      * apply WP_Ter2; clear n IHn.
        specialize (H (S (S O))).
        simpl in H.
        inversion H; subst.
        assert (cstep (CBreak, KSeq c2 :: nil, st) (CBreak, nil, st)); [constructor |].
        specialize (H2 _ _ _ H0).
        inversion H2; subst; auto.
        destruct H4 as (? & ? & ? & ?).
        inversion H3.
      * apply WP_Ter3; clear n IHn.
        unfold Assertion_Shallow.Assertion_denote.
        specialize (H (S (S O))).
        simpl in H.
        inversion H; subst.
        assert (cstep (CCont, KSeq c2 :: nil, st) (CCont, nil, st)); [constructor |].
        specialize (H2 _ _ _ H0).
        inversion H2; subst; auto.
        destruct H4 as (? & ? & ? & ?).
        inversion H3.
    + apply WP_Pre; auto; intros.
      apply IHn. clear n IHn.
      intros n.
      specialize (H (S n)).
      inversion H; subst;
      [ apply nil_app_neq in H2; inversion H2 |
        apply nil_app_neq in H2; inversion H2 | 
        apply nil_app_neq in H2; inversion H2 |].
      apply H4.
      apply cstep_ctx_step; auto.
    + inversion H0; subst;
      specialize (H (S n));
      inversion H; subst; exfalso;
      [ apply (reducible_irreducible_ex CSkip ((KLoop1 c0 c3 :: k0) ++ KSeq c2 :: nil) st); auto; apply IR_ForSkip |
        apply (reducible_irreducible_ex CCont ((KLoop2 c0 c3 :: k0) ++ KSeq c2 :: nil) st); auto; apply IR_ForCont ].
Qed.

(* TODO: need (c1, (KSeq c2 :: nil)) ~ (c1 ;; c2, nil) *)

Import Assertion_Shallow.

Inductive seq_inv_sim : (com * continuation) -> (com * continuation) -> Prop :=
  | SI_sim_id : forall c k, seq_inv_sim (c, k) (c, k)
  | SI_sim_seqinv : forall c1 c2 k, 
      seq_inv_sim (c1, KSeq c2 :: k) (CSeq c1 c2, k).

Lemma seq_inv_sim_is_simulation : simulation seq_inv_sim.
Proof.
  unfold simulation.
  intros.
  split; try split.
  { intros. 
    destruct H0 as [? | [? | ?]]; inversion H0; subst; 
      inversion H; subst; tauto. }
  { intros.
    inversion H0; subst; inversion H; subst; constructor. }
  intros.
  inversion H; subst.
  + exists c1', k1'.
    split; constructor; tauto.
  + rename c3 into c2; rename k2 into k.
    inversion H0; subst.
    - exists (CAss X a'), (KSeq c2 :: k).
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - exists CSkip, (KSeq c2 :: k).
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - rename c1' into c11; rename c3 into c12.
      exists c11, (KSeq c12 :: KSeq c2 :: k).
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - exists c1', k1'.
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - exists CCont, k1'.
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - exists CBreak, k1'.
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - rename c0 into c11; rename c3 into c12.
      exists (CIf b' c11 c12), (KSeq c2 :: k).
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - exists c1', (KSeq c2 :: k).
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - exists c1', (KSeq c2 :: k).
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - exists (CSeq c0 CCont), (KLoop1 c0 c3 :: KSeq c2 :: k).
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
Qed.    

Theorem seq_inv_valid_smallstep : forall P c1 c2 Q R1 R2,
  valid_smallstep P (CSeq c1 c2) Q R1 R2 ->
  (exists Q', (valid_smallstep P c1 Q' R1 R2) /\
    (valid_smallstep Q' c2 Q R1 R2)).
Proof.
  intros.
  exists (WP c2 nil Q R1 R2).
  split.
  { unfold valid_smallstep in H.
    unfold valid_smallstep.
    intros.
    specialize (H st H0).
    pose proof wp_sim.
    pose proof wp_bind_inv.
    specialize (H1 (CSeq c1 c2) c1 nil (KSeq c2 :: nil) Q R1 R2 st seq_inv_sim).
    apply H2. apply H1.
    + apply seq_inv_sim_is_simulation.
    + constructor.
    + tauto.
  }
  unfold valid_smallstep.
  intros.
  unfold Assertion_denote, WP in H0.
  unfold WP; tauto.
Qed.

Inductive if_seq_sim : (com * continuation) -> (com * continuation) -> Prop :=
  | IS_sim_id : forall c k, if_seq_sim (c, k) (c, k)
  | IS_sim_ifseq : forall b c1 c2 c3 k,
  if_seq_sim (CSeq (CIf b c1 c2) c3, k) (CIf b (CSeq c1 c3) (CSeq c2 c3), k)
  | IS_sim_seq : forall b c1 c2 c3 k,
  if_seq_sim (CIf b c1 c2, KSeq c3 :: k) (CIf b (CSeq c1 c3) (CSeq c2 c3), k)
  (* | IS_sim_bfalse : forall c1 c2 c3 k,
      if_seq_sim (CIf BFalse c1 c2, KSeq c3 :: k) (CSeq c1 c3, k)
  | IS_sim_btrue : forall c1 c2 c3 k,
      if_seq_sim (CIf BTrue c1 c2, KSeq c3 :: k) (CSeq c2 c3, k) *)
  .

Lemma if_seq_sim_is_simulation :
  simulation if_seq_sim.
Proof.
  unfold simulation.
  intros. split; [| split].
  {
    intros.
    destruct H0 as [? | [? | ?]]; inversion H0; subst; inversion H; subst; auto.
  }
  {
    intros.
    inversion H0; subst; inversion H; subst; auto.
  }
  {
    intros.
    inversion H; subst.
    - exists c1', k1'; split; constructor; auto.
    - inversion H0; subst.
      exists (CIf b (CSeq c0 c4) (CSeq c3 c4)), k2;
      split; [apply rt_refl | constructor].
    - inversion H0; subst.
      + exists (CIf b' (CSeq c0 c4) (CSeq c3 c4)), k2; split; constructor.
        constructor; auto.
      + exists c1', (KSeq c4 :: k2); split; [| constructor].
        apply (rt_trans _ _ (CSeq c1' c4, k2, st')); constructor; constructor.
      + exists c1', (KSeq c4 :: k2); split; [| constructor].
        apply (rt_trans _ _ (CSeq c1' c4, k2, st')); constructor; constructor.
  }
Qed.

Theorem if_seq_valid_smallstep : forall P b c1 c2 c3 Q R1 R2,
  valid_smallstep P (CIf b (CSeq c1 c3) (CSeq c2 c3)) Q R1 R2 ->
  valid_smallstep P (CSeq (CIf b c1 c2) c3) Q R1 R2.
Proof.
  unfold valid_smallstep.
  intros.
  apply (wp_sim _ _ _ _ _ _ _ _ _ if_seq_sim_is_simulation (IS_sim_ifseq b c1 c2 c3 nil)).
  apply H; auto.
Qed.

(* Already proved in Iris-CF, leave to the last *)
Theorem nocontinue_valid_smallstep : forall P c Q R1 R2 R2',
  nocontinue_c c ->
  valid_smallstep P c Q R1 R2 ->
  valid_smallstep P c Q R1 R2'.
Admitted.

Inductive loop_noc_sim : (com * continuation) -> (com * continuation) -> Prop :=
  | LN_sim_id : forall c k, loop_noc_sim (c, k) (c, k)
  | LN_sim_loopnoc : forall c1 c2 k,
      nocontinue_c c1 -> nocontinue_c c2 ->
      loop_noc_sim (CFor c1 c2, k) (CFor (CSeq c1 c2) CSkip, k)
  | LN_sim_1 : forall c1 c2 k,
      nocontinue_c c1 -> nocontinue_c c2 ->
      loop_noc_sim (CSeq c1 CCont, KLoop1 c1 c2 :: k) 
        (CSeq c1 c2, KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k)
  | LN_sim_2 : forall c0 c1 c2 k k0,
      nocontinue c0 k0 -> nocontinue_c c1 -> nocontinue_c c2 ->
      loop_noc_sim (c0, k0 ++ KSeq CCont :: KLoop1 c1 c2 :: k)
        (c0, k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k)
  | LN_sim_3 : forall c1 c2 k,
      nocontinue_c c1 -> nocontinue_c c2 ->
      loop_noc_sim (CCont, KLoop1 c1 c2 :: k) 
        (c2, KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k)
  | LN_sim_4 : forall c0 c1 c2 k k0,
      nocontinue c0 k0 -> nocontinue_c c1 -> nocontinue_c c2 ->
      loop_noc_sim (c0, k0 ++ KLoop2 c1 c2 :: k)
        (c0, k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k)
  | LN_sim_5 : forall c1 c2 k,
      nocontinue_c c1 -> nocontinue_c c2 ->
      loop_noc_sim (CSkip, KLoop2 c1 c2 :: k)
        (CSkip, KLoop2 (CSeq c1 c2) CSkip :: k)
  | LN_sim_6 : forall c1 c2 k,
      nocontinue_c c1 -> nocontinue_c c2 ->
      loop_noc_sim (CBreak, KLoop1 c1 c2 :: k)
        (CBreak, KLoop1 (CSeq c1 c2) CSkip :: k).


Lemma loop_noc_sim_is_simulation : simulation loop_noc_sim.
Proof.
  unfold simulation.
  intros.
  split; [ | split].
  { intros; destruct H0 as [? | [? | ?]];
      inversion H0; subst; inversion H; subst;
      try auto; exfalso; eapply nil_app_neq; rewrite H2; auto. }
  { intros.
    inversion H0; subst. inversion H; subst; try tauto.
    + destruct k1; inversion H2; subst; constructor.
    + destruct k1; inversion H2; subst; constructor.
    + inversion H; subst; try tauto.
      - destruct k1; inversion H2; subst; constructor.
      - destruct k1; [inversion H5; subst; destruct H1; inversion H1 |
          inversion H2; subst; constructor]. }
  intros.
  inversion H; subst. 
  + exists c1', k1'.
    split; [ constructor; auto | constructor].
  + rename c0 into c1; rename c3 into c2; rename k2 into k.
    inversion H0; subst.
    exists (CSeq c1 c2), (KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
    split; [ | constructor; auto].
    eapply rt_trans_1n; [constructor | repeat constructor].
  + rename c0 into c1; rename c3 into c2.
    inversion H0; subst c1'; subst.
    exists c1, (KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
    split; [| apply (LN_sim_2 c1 _ _ _ nil); auto].
    apply rt_step; constructor.
    unfold nocontinue; constructor; [left; tauto | constructor].
  + rename c2 into c0; rename c3 into c1; rename c4 into c2.
    inversion H0; subst.
    - exists (CAss X a'), 
        (k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
    - exists CSkip, 
        (k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
    - rename c1' into c01; rename c4 into c02.
      exists c01,
        (KSeq c02 :: k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_2 c01 _ _ _ (KSeq c02 :: k0)); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0.
      { inversion H3; subst.
        exists c2, (KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
        split; [repeat constructor; auto | constructor; auto]. }
      inversion H3; subst. 
      exists c1',
        (k1 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0.
      { unfold nocontinue in H5; simpl in H5; tauto. }
      inversion H3; subst.
      exists CCont, 
        (k1 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0.
      { inversion H3; subst.
        exists CBreak,
          (KLoop1 (CSeq c1 c2) CSkip :: k).
        split; [| constructor; auto].
        eapply rt_trans_1n; [constructor |].
        repeat constructor. }
      inversion H3; subst.
      exists CBreak,  
        (k1 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
      unfold nocontinue in *; simpl in *; tauto.
    - rename c3 into c01; rename c4 into c02.
      exists (CIf b' c01 c02),
        (k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
    - rename c1' into c01; rename c4 into c02.
      exists c01,
        (k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
      unfold nocontinue in *; simpl in *; tauto.
    - rename c3 into c01; rename c1' into c02.
      exists c02,
        (k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
      unfold nocontinue in *; simpl in *; tauto.
    - rename c3 into c01; rename c4 into c02.
      exists (CSeq c01 CCont),
        (KLoop1 c01 c02 :: k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_2 _ _ _ _ (KLoop1 c01 c02 :: k0)); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0.
      { inversion H3; subst. }
      inversion H3; subst.
      exists (CSeq c3 CCont),
        (KLoop1 c3 c4 :: k2 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_2 _ _ _ _ (KLoop1 c3 c4 :: k2)); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0; inversion H3; subst.
      rename c3 into c01; rename c1' into c02.
      exists c02,
        (KLoop2 c01 c02 :: k2 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
        split; [repeat constructor; auto |].
        apply (LN_sim_2 _ _ _ _ (KLoop2 c01 c02 :: k2)); auto.
        unfold nocontinue in *; simpl in *; tauto.
    - destruct k0; inversion H3; subst.
      rename c3 into c01; rename c4 into c02.
      exists CSkip,
        (k1 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_2 _ _ _ _ k1); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0; inversion H3; subst.
      exists CSkip,
        (k1 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_2 _ _ _ _ k1); auto.
      unfold nocontinue in *; simpl in *; tauto.
  + inversion H0; subst.
    rename c0 into c1; rename c1' into c2. 
    exists c2, (KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
    split;[| apply (LN_sim_4 _ _ _ _ nil); auto].
    apply rt_refl.
    unfold nocontinue in *; simpl in *; tauto.
  + rename c2 into c0; rename c3 into c1; rename c4 into c2.
    inversion H0; subst.
    - exists (CAss X a'),
        (k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; tauto | constructor; tauto].
    - exists CSkip,
        (k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; tauto | constructor; tauto].
    - rename c1' into c01; rename c4 into c02.
      exists c01,
        (KSeq c02 :: k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; tauto | ].
      apply (LN_sim_4 _ _ _ _ (KSeq c02 :: k0)); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0; inversion H3; subst.
      exists c1', 
        (k1 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0; inversion H3; subst.
      exists CCont, (k1 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; tauto | constructor; auto].
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0; inversion H3; subst.
      exists CBreak, (k1 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
      unfold nocontinue in *; simpl in *; tauto.
    - exists (CIf b' c3 c4),
        (k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
    - exists (c1'),
        (k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto | constructor; auto].
      unfold nocontinue in *; simpl in *; tauto.
    - exists (c1'),
        (k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
       split; [repeat constructor; auto | constructor; auto].
       unfold nocontinue in *; simpl in *; tauto.
    - rename c3 into c01; rename c4 into c02.
      exists (CSeq c01 CCont),
        (KLoop1 c01 c02 :: k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_4 _ _ _ _ (KLoop1 c01 c02 :: k0)); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0.
      { inversion H3; subst; simpl in *.
        exists (CSeq c1 c2),
          (KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
        split; [| constructor; auto].
        eapply rt_trans_1n; [constructor |].
        eapply rt_trans_1n; [constructor |].
        eapply rt_trans_1n; [constructor |].
        repeat constructor. }
      rename c3 into c01; rename c4 into c02.
      inversion H3; subst.
      exists (CSeq c01 CCont),
        (KLoop1 c01 c02 :: k2 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_4 _ _ _ _ (KLoop1 c01 c02 :: k2)); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0.
      { inversion H3; subst. }
      rename c3 into c01; rename c1' into c02.
      inversion H3; subst.
      exists c02,
        (KLoop2 c01 c02 :: k2 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_4 _ _ _ _ (KLoop2 c01 c02 :: k2)); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0.
      { inversion H3; subst. }
      rename c3 into c01; rename c4 into c02.
      inversion H3; subst.
      exists CSkip,
        (k1 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_4 _ _ _ _ k1); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - destruct k0.
      { inversion H3; subst.
        simpl in *.
        exists CSkip, k; split; [| constructor].
        eapply rt_trans_1n; [constructor |].
        eapply rt_trans_1n; [constructor |].
        apply rt_refl. }
      rename c3 into c01; rename c4 into c02.
      inversion H3; subst.
      exists CSkip,
        (k1 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_4 _ _ _ _ k1); auto.
      unfold nocontinue in *; simpl in *; tauto.
  + rename c0 into c1; rename c3 into c2.
    inversion H0; subst.
    exists (CSeq c1 c2),
      (KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
    split; [| constructor; auto].
    eapply rt_trans_1n; [constructor; auto|].
    eapply rt_trans_1n; [constructor; auto|].
    apply rt_refl.
  + inversion H0; subst.
    rename c0 into c1; rename c3 into c2.
    exists CSkip, k1'.
    split; [repeat constructor | constructor].
Qed.    
    
Theorem loop_nocontinue_valid_smallstep : forall P c1 c2 Q R1 R2,
  nocontinue_c c1 ->
  nocontinue_c c2 ->
  valid_smallstep P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  valid_smallstep P (CFor c1 c2) Q R1 R2.
Proof.
  intros.
  unfold valid_smallstep in *.
  intros.
  specialize (H1 st H2).
  pose proof wp_sim.
  apply (wp_sim (CFor (CSeq c1 c2) CSkip) (CFor c1 c2) nil nil _ _ _ _ 
    loop_noc_sim).
  + apply loop_noc_sim_is_simulation.
  + constructor; tauto.
  + tauto.
Qed.  
