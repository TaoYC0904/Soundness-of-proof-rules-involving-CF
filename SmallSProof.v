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
    - exists c1', (KLoop1 c3 c4 :: KSeq c2 :: k).
      split; [| constructor].
      eapply rt_trans_1n; [constructor |].
      apply rt_step; constructor; tauto.
    - exists c1', (KLoop2 c3 c4 :: KSeq c2 :: k).
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
  if_seq_sim (CIf b c1 c2, KSeq c3 :: k) (CIf b (CSeq c1 c3) (CSeq c2 c3), k).

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

Lemma cstep_preserve_nocontinue : forall c1 c2 k1 k2 st1 st2,
  cstep (c1, k1, st1) (c2, k2, st2) ->
  nocontinue c1 k1 ->
  nocontinue c2 k2.
Proof.
  intros.
  inversion H; subst; auto;
  unfold nocontinue in *; simpl in *; tauto.
Qed.

Theorem nocontinue_valid_smallstep : forall P c Q R1 R2 R2',
  nocontinue_c c ->
  valid_smallstep P c Q R1 R2 ->
  valid_smallstep P c Q R1 R2'.
Proof.
  unfold valid_smallstep.
  intros.
  specialize (H0 st H1).
  unfold WP in *.
  intros.
  clear H1.
  assert (nocontinue c nil).
  { unfold nocontinue; simpl; auto. }
  clear H.
  remember nil as k; clear Heqk.
  revert c k st H0 H1.
  induction n; [constructor |].
  intros.
  pose proof (H0 1%nat).
  inversion H; subst.
  { constructor; auto. }
  { constructor; auto. }
  { inversion H1; simpl in *; tauto. }
  clear H.
  constructor; try tauto.
  intros.
  pose proof (cstep_preserve_nocontinue _ _ _ _ _ _ H H1).
  apply IHn; try tauto.
  intros.
  specialize (H0 (S n0)).
  inversion H0; subst.
  - inversion H.
  - inversion H.
  - inversion H.
  - specialize (H7 _ _ _ H); auto.
Qed.
 
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
    - rename c1' into c00; rename c4 into c01; rename c5 into c02.
      exists c00,
        (KLoop1 c01 c02 :: k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_2 _ _ _ _ (KLoop1 c01 c02 :: k0)); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - rename c1' into c00; rename c4 into c01; rename c5 into c02.
      exists c00,
        (KLoop2 c01 c02 :: k0 ++ KSeq c2 :: KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_2 _ _ _ _ (KLoop2 c01 c02 :: k0)); auto.
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
    - rename c1' into c00; rename c4 into c01; rename c5 into c02.
      exists c00,
        (KLoop1 c01 c02 :: k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_4 _ _ _ _ (KLoop1 c01 c02 :: k0)); auto.
      unfold nocontinue in *; simpl in *; tauto.
    - rename c1' into c00; rename c4 into c01; rename c5 into c02.
      exists c00,
        (KLoop2 c01 c02 :: k0 ++ KSeq CCont :: KLoop1 (CSeq c1 c2) CSkip :: k).
      split; [repeat constructor; auto |].
      apply (LN_sim_4 _ _ _ _ (KLoop2 c01 c02 :: k0)); auto.
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

(* Semantic Equivalence Approach *)
(* Aborted since it is no easier than the simulation approach. *)

Definition eval_like_mstep c1 k1 s1 c2 k2 s2 : Prop :=
  forall c k s, (Halt c k \/ irreducible c k s) ->
    mstep (c1, k1, s1) (c, k, s) -> mstep (c2, k2, s2) (c, k, s).

Lemma wp_eval_like: forall c1 k1 s1 c2 k2 s2 Q R1 R2,
  eval_like_mstep c2 k2 s2 c1 k1 s1 ->
  WP c1 k1 Q R1 R2 s1 ->
  WP c2 k2 Q R1 R2 s2.
Proof.
  intros. intros n.
  rename H into Hlike.
  rename H0 into H.
  revert c2 k2 s2 Hlike.
  induction n; intros; [constructor |].
  pose proof halt_choice c2 k2 s2 as [? | [? | ?]].
  - pose proof H0 as Hhalt;
    destruct H0 as [? | [? | ?]]; inversion H0; subst;
    specialize (Hlike _ _ _ (or_introl _ Hhalt) (rt_refl _ _)); clear Hhalt;
    eapply WP_mstep_pre; eauto.
  - constructor; auto; intros.
    apply IHn. intros ? ? ? ? ?.
    apply Hlike; auto.
    eapply rt_trans; eauto.
    apply rt_step; auto.
  - specialize (Hlike _ _ _ (or_intror _ H0) (rt_refl _ _)).
    eapply WP_mstep_pre; eauto.
Qed.

Ltac solve_nonhalt H :=
  let H0 := fresh in
  destruct H as [H0|[H0|H0]];
  let H1 := fresh in
  let H2 := fresh in
  destruct H0 as [H1 H2];
  try inversion H1;
  try (apply symmetry, app_cons_not_nil in H2; exfalso; tauto).

Ltac solve_nonterminal H :=
  destruct H; [solve_nonhalt H|inversion H].

Lemma if_path_spec: forall c k s,
  (Halt c k \/ irreducible c k s) ->
  forall b c1 c2 k1 s1,
  mstep ((CIf b c1 c2), k1, s1) (c, k, s) <->
  (multi_bstep s1 b BTrue /\
    mstep (c1, k1, s1) (c, k, s)) \/
  (multi_bstep s1 b BFalse /\
    mstep (c2, k1, s1) (c, k, s)).
Proof.
  intros.
  split; intros.
  {
    remember ((CIf b c1 c2), k1, s1) as cfg1.
    remember (c, k, s) as cfg.
    revert dependent s. revert c k.
    revert dependent s1. revert b c1 c2.
    induction_1n H0; intros; subst.
    + inversion Heqcfg; subst.
      solve_nonterminal H.
    + inversion H; subst.
      - specialize (IHrt _ _ _ _ ltac:(reflexivity) _ _ _ H1 ltac:(reflexivity)).
        destruct IHrt as [[? ?] | [? ?]].
        * assert (multi_bstep s1 b BTrue). { etransitivity_1n; eassumption. }
          tauto.
        * assert (multi_bstep s1 b BFalse). { etransitivity_1n; eassumption. }
          tauto.
      - assert (multi_bstep s1 BTrue BTrue). { reflexivity. }
        tauto.
      - assert (multi_bstep s1 BFalse BFalse). { reflexivity. }
        tauto.
  }
  {
    destruct H0 as [[? ?] | [? ?]].
    + induction_1n H0.
      - etransitivity_1n; [apply CS_IfTrue|auto].
      - etransitivity_1n; [constructor|]; eassumption.
    + induction_1n H0.
    - etransitivity_1n; [apply CS_IfFalse|auto].
    - etransitivity_1n; [constructor|]; eassumption.
  }
Qed.

(* Lemma CSeq_path_spec: forall c k s,
  (Halt c k \/ irreducible c k s) ->
  forall c1 c2 k1 s1,
  mstep (CSeq c1 c2, k1, s1) (c, k, s) <->
  (mstep (c1, k1, s1) (c, k, s) \/
  exists s2,
  mstep (c1, k1, s1) (CSkip, k1, s2) /\
  mstep (c2, k1, s2) (c, k, s)).
Proof.
  intros.
  split; intros.
  {
    remember (CSeq c1 c2, k1, s1) as (c, k, s)
  }
  remember (CSeq c1 c2) as c eqn:H0.
  remember CSkip as c' eqn:H1.
  revert c1 c2 H0 H1; induction_1n H; intros; subst.
  + inversion H1.
  + inversion H; subst.
    - specialize (IHrt _ _ ltac:(reflexivity) ltac:(reflexivity)).
      destruct IHrt as [st2 [? ?]].
      exists st2.
      assert (multi_cstep (c1, st1) (Skip%imp, st2)).
      { etransitivity_1n; eassumption. }
      tauto.
    - exists s.
      split; [reflexivity | tauto].
Qed. *)

Theorem if_seq_valid_smallstep' : forall P b c1 c2 c3 Q R1 R2,
  valid_smallstep P (CIf b (CSeq c1 c3) (CSeq c2 c3)) Q R1 R2 ->
  valid_smallstep P (CSeq (CIf b c1 c2) c3) Q R1 R2.
Proof.
  unfold valid_smallstep.
  intros.
  apply H in H0.
  eapply wp_eval_like; eauto.
  clear.
  intros ? ? ? ? ?.
  apply rt_rt1n in H0.
  inversion H0; subst; clear H0;
  [solve_nonterminal H|].
  inversion H1; subst; clear H1.
  apply rt1n_rt in H2.

  apply (if_path_spec _ _ _ H) in H2 as [[? ?]|[? ?]].
  - apply (if_path_spec _ _ _ H).
    left; split; auto.
    etransitivity_1n; [constructor|auto].
  - apply (if_path_spec _ _ _ H).
    right; split; auto.
    etransitivity_1n; [constructor|auto].
Qed.


Fixpoint CFor_path c1 c2 k1 s1 c k s (n: nat): Prop:=
  match n with
  | O =>
      (* c1 break *)
      (exists k2, mstep (c1, nil, s1) (CBreak, k2, s) /\
        (c, k, s) = (CSkip, k1, s)) \/
      (* c1 stuck middle *)
      (exists c1' k1', irreducible c1' k1' s /\
        mstep (c1, nil, s1) (c1', k1', s) /\
        (c, k, s) = (c1', k1' ++ KSeq CCont :: KLoop1 c1 c2 :: k1, s)) \/
      (
        exists s2, mstep (CSeq c1 CCont, nil, s1) (CCont, nil, s2) /\
        (
          (* c2 break *)
          (exists k2, mstep (c2, nil, s2) (CBreak, k2, s) /\
            (c, k, s) = (CSkip, k1, s)) \/
          (* c2 stuck middle *)
          (exists c2' k2', irreducible c2' (k2' ++ KLoop2 c1 c2 :: k1) s /\
            mstep (c2, nil, s2) (c2', k2', s) /\
            (c, k, s) = (c2', k2' ++ KLoop2 c1 c2 :: k1, s)) \/
          (* c2 continue: stuck *)
          exists k2, mstep (c2, nil, s2) (CCont, k2, s) /\
            (c, k, s) = (CCont, (KLoop2 c1 c2 :: k1), s)
        )
      )
  | S n' => 
      exists s2, mstep (CSeq c1 CCont, nil, s1) (CCont, nil, s2) /\
      exists s3, mstep (c2, nil, s2) (CSkip, nil, s3) /\
      CFor_path c1 c2 k1 s3 c k s n'
  end.

Definition CFor_path' c1' k1' c1 c2 k1 s1 c k s (n: nat): Prop:=
  match n with
  | O =>
      (* c1 break *)
      (exists k2, mstep (c1', k1', s1) (CBreak, k2, s) /\
        (c, k, s) = (CSkip, k1, s)) \/
      (* c1 stuck middle *)
      (exists c1'' k1'', irreducible c1'' k1'' s /\
        mstep (c1', k1', s1) (c1'', k1'', s) /\
        (c, k, s) = (c1'', k1'' ++ KSeq CCont :: KLoop1 c1 c2 :: k1, s)) \/
      (
        exists s2, mstep (c1', k1' ++ KSeq CCont :: nil, s1) (CCont, nil, s2) /\
        (
          (* c2 break *)
          (exists k2, mstep (c2, nil, s2) (CBreak, k2, s) /\
            (c, k, s) = (CSkip, k1, s)) \/
          (* c2 stuck middle *)
          (exists c2' k2', irreducible c2' (k2' ++ KLoop2 c1 c2 :: k1) s /\
            mstep (c2, nil, s2) (c2', k2', s) /\
            (c, k, s) = (c2', k2' ++ KLoop2 c1 c2 :: k1, s)) \/
          (* c2 continue: stuck *)
          exists k2, mstep (c2, nil, s2) (CCont, k2, s) /\
            (c, k, s) = (CCont, (KLoop2 c1 c2 :: k1), s)
        )
      )
  | S n' => 
      exists s2, mstep (c1', k1' ++ KSeq CCont :: nil, s1) (CCont, nil, s2) /\
      exists s3, mstep (c2, nil, s2) (CSkip, nil, s3) /\
      CFor_path c1 c2 k1 s3 c k s n'
  end.

Definition CFor_path'' c2' k2' c1 c2 k1 s1 c k s (n: nat): Prop:=
  match n with
  | O =>
      (* c2 break *)
      (exists k2, mstep (c2', k2', s1) (CBreak, k2, s) /\
        (c, k, s) = (CSkip, k1, s)) \/
      (* c2 stuck middle *)
      (exists c2'' k2'', irreducible c2'' (k2'' ++ KLoop2 c1 c2 :: k1) s /\
        mstep (c2', k2', s1) (c2'', k2'', s) /\
        (c, k, s) = (c2'', k2'' ++ KLoop2 c1 c2 :: k1, s)) \/
      (* c2 continue: stuck *)
      exists k2, mstep (c2', k2', s1) (CCont, k2, s) /\
        (c, k, s) = (CCont, (KLoop2 c1 c2 :: k1), s)
  | S n' => 
      exists s2, mstep (c2', k2', s1) (CSkip, nil, s2) /\
      CFor_path c1 c2 k1 s2 c k s n'
  end.

(* Lemma CFor_path_spec: forall c k s,
  (Halt c k \/ irreducible c k s) ->
  forall c1 c2 k1 s1,
  mstep (CFor c1 c2, k1, s1) (c, k, s) ->
  exists n, CFor_path c1 c2 k1 s1 c k s n.
Proof.
  intros.
  remember (CFor c1 c2, k1, s1) as cfg1.
  remember (c, k, s) as cfg2.
  revert dependent s. revert c k.
  assert 
  revert dependent s1. revert c1 c2 k1.
  induction_1n H0; intros; subst.
  + inversion Heqcfg2; subst.
    solve_nonterminal H.
  + inversion H; subst.
    pose proof CWhile_path_spec_aux st1 st2 c c'.
    tauto. *)

Lemma for_c1_step_inv: forall c1 c2 c1' k1' k1 s1 cfg1,
  cstep (c1', k1' ++ KSeq CCont :: KLoop1 c1 c2 :: k1, s1) cfg1 ->
  exists c1'' k1'' s1',
  cfg1 = (c1'', k1'' ++ KLoop1 c1 c2 :: k1, s1') /\
  (k1'' = nil \/ exists k1''', k1'' = k1''' ++ KSeq CCont :: nil).
Proof.
Abort.

Lemma CWhile_path_spec_aux:
  forall c k s, (Halt c k \/ irreducible c k s) ->
  forall cfg1, mstep cfg1 (c, k, s) ->
  (forall c1 c2 k1 s1,
    cfg1 = (CFor c1 c2, k1, s1) ->
    exists n, CFor_path c1 c2 k1 s1 c k s n) /\
  (forall s1 c1 c2 k1,
    cfg1 = (CSeq c1 CCont, KLoop1 c1 c2 :: k1, s1) ->
    exists n, CFor_path' c1 nil c1 c2 k1 s1 c k s n) /\
  (forall c1' k1' s1 c1 c2 k1,
    cfg1 = (c1', k1' ++ KSeq CCont :: KLoop1 c1 c2 :: k1, s1) -> 
    exists n, CFor_path' c1' k1' c1 c2 k1 s1 c k s n) /\
  (forall c2' k2' s1 c1 c2 k1,
    cfg1 = (c2', k2' ++ KLoop2 c1 c2 :: k1, s1) ->
    exists n, CFor_path'' c2' k2' c1 c2 k1 s1 c k s n).
Proof.
  intros.
  remember (c, k, s) as cfg2.
  revert dependent s. revert c k.
  induction_1n H0; intros; subst.
  + repeat split.
    - inversion 1; subst; solve_nonterminal H.
    - inversion 1; subst; solve_nonterminal H.
    - inversion 1; subst; destruct H; [solve_nonhalt H|].
      exists O; simpl.
      right; left. exists c1', k1'.
      split; [|split]; [|apply rt_refl|reflexivity].
      inversion H; subst;
      destruct k1'; inversion H3; subst; constructor.
    - inversion 1; subst.
      destruct H; [solve_nonhalt H|].
      exists O; simpl.
      right; left. exists c2', k2'.
      split; [|split]; [|apply rt_refl|reflexivity].
      inversion H; subst;
      destruct k2'; inversion H3; subst; constructor.
  + specialize (IHrt _ _ _ H1 ltac:(reflexivity)).
    repeat split; inversion 1; subst; clear H3.
    - inversion H; subst; clear H.
      destruct IHrt as [_ [? _]].
      specialize (H _ _ _ _ ltac:(reflexivity)).
      destruct H as [[| ?] ?].
      * exists 0%nat. simpl in *.
        destruct H as [? | [? | ?]]; try tauto.
        destruct H as [? [? ?]].
        destruct H2 as [? | [? | ?]];
        (right; right; eexists; split;
        [etransitivity_1n; [constructor|eauto]|tauto]).
      * exists (S n). simpl in *.
        destruct H as [? [? ?]].
        eexists; split; [etransitivity_1n; [constructor|eauto]|tauto].
    - inversion H; subst; clear H.
      destruct IHrt as [_ [_ [? _]]].
      specialize (H c1 nil). simpl in H.
      specialize (H _ _ _ _ ltac:(reflexivity)); auto.
    (* - apply for_c1_step_inv in H as [? [? [? [? [? | ?]]]]];
      inversion H; subst; clear H3.
      * 
      inversion H; subst; clear H2.
      destruct cfg1.
      destruct IHrt as [_ [_ [_ ?]]]. *)
Abort.

Theorem loop_nocontinue_valid_smallstep' : forall P c1 c2 Q R1 R2,
  nocontinue_c c1 ->
  nocontinue_c c2 ->
  valid_smallstep P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  valid_smallstep P (CFor c1 c2) Q R1 R2.
Proof.
  unfold valid_smallstep.
  intros.
  apply H1 in H2.
  eapply wp_eval_like; eauto.
  clear - H H0.
  intros ? ? ? ? ?.
  
  apply rt_rt1n in H2.
  
  remember (@pair (prod com continuation) state
  (@pair com continuation (CFor c1 c2) (@nil KElements)) st) as cfg1.
  remember (c, k, s) as cfg2.
  revert dependent s. revert c k.
  revert dependent st. revert c1 c2 H H0.
  induction H2; intros; subst;
  try inversion Heqcfg2; subst.
  {
    admit.
  }

  inversion H; subst; clear H.
  inversion H2; subst; clear H2.
  {
    admit.
  }
  inversion H; subst; clear H.
  eapply rt_trans; [eapply rt_step; constructor|].
  eapply rt_trans; [eapply rt_step; constructor|].
  eapply rt_trans; [eapply rt_step; constructor|].
Abort.

Print nocontinue_c.