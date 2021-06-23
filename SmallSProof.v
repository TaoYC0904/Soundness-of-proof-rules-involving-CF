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
  apply clos_trans_t1n_iff in H0.
  induction H0; intros; subst.
  - intros n.
    specialize (H0 (S n)).
    inversion H0; subst;
    [ inversion H |
      inversion H |
      inversion H |].
    apply (H3 _ _ _ H).
  - destruct y as [[c'' k''] st''].
    apply (IHclos_trans_1n eq_refl _ _ _ eq_refl).
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


Lemma nil_app_neq {A : Type} : forall (a : A) l,
  nil = l ++ a :: nil -> False.
Proof.
  intros.
  pose proof eq_refl (List.length (@nil A)).
  rewrite H in H0 at 1.
  rewrite List.app_length in H0.
  simpl in H0. lia.
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
Theorem seq_inv_valid_smallstep : forall P c1 c2 Q R1 R2,
  valid_smallstep P (CSeq c1 c2) Q R1 R2 ->
  (exists Q', (valid_smallstep P c1 Q' R1 R2) /\
    (valid_smallstep Q' c2 Q R1 R2)).
Admitted.

Theorem if_seq_valid_smallstep : forall P b c1 c2 c3 Q R1 R2,
  valid_smallstep P (CSeq (CIf b c1 c2) c3) Q R1 R2 ->
  valid_smallstep P (CIf b (CSeq c1 c3) (CSeq c2 c3)) Q R1 R2.
Admitted.

(* Already proved in Iris-CF, leave to the last *)
Theorem nocontinue_valid_smallstep : forall P c Q R1 R2 R2',
  nocontinue c ->
  valid_smallstep P c Q R1 R2 ->
  valid_smallstep P c Q R1 R2'.
Admitted.

Theorem loop_nocontinue_valid_smallstep : forall P c1 c2 Q R1 R2,
  nocontinue c1 ->
  nocontinue c2 ->
  valid_smallstep P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  valid_smallstep P (CFor c1 c2) Q R1 R2.
Admitted. 
