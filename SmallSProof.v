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
    inversion H2; [constructor | | | |]; exfalso;
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
    induction n; intros; [constructor |].

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

  (* pose proof H _ _ _ _ H0 as [_ [? _]].
    specialize (H3 _ H2).
    inversion H1; exfalso;
    [ apply (halt_irreducible_ex c1 k1 st); auto; subst; auto_halt |
      apply (halt_irreducible_ex c1 k1 st); auto; subst; auto_halt |
      apply (halt_irreducible_ex c1 k1 st); auto; subst; auto_halt |]; subst.
    apply (reducible_irreducible_ex c1 k1 st); auto.
    

(* ######################### *)


  revert c2 k2 H0.
  induction H1; intros.
  - unfold simulation in H.
    pose proof H1 as Hsim.
    apply H in H1.
    pose proof halt_choice c2 k2 st.
    destruct H2 as [? | [? | ?]].
    + destruct H1 as [? _].
      specialize (H1 H2).
      inversion H1; subst.
      apply WP_Ter1; auto.
    + destruct H1 as [_ [_ ?]].
      destruct H2 as (? & ? & ? & ?).
      apply H1 in H2.
      destruct H2 as (? & ? & ? & ?).
      unfold mstep in H2.
      apply clos_trans_t1n_iff in H2.
      inversion H2; inversion H4.
    + destruct H1 as [_ [? _]].
      specialize (H1 _ H2).
      inversion H1. 
  - admit.
  - admit.
  - unfold simulation in H.
    apply H in H3.
    pose proof halt_choice c2 k2 st.
    destruct H4 as [? | [? | ?]].
    + destruct H3 as [? _].
      specialize (H3 H4).
      inversion H3; subst.
      exfalso; apply (halt_reducible_ex c k st); auto.
    + destruct H3 as [_ [_ ?]].
      apply WP_Pre; auto.
      intros.
      pose proof H3 _ _ _ _ H5 as (c1' & k1' & ? & ?).
      

      revert H H2 H5 H6.
      clear.
      intros.

      remember (c, k, st) as prog.
      remember (c1', k1', st') as prog'.
      rewrite Heqprog in *. rewrite Heqprog' in *.
      rewrite <- Heqprog in H5. rewrite <- Heqprog' in H5.
      revert c k st Heqprog H2 H6.

      unfold mstep in H5.
      apply clos_trans_t1n_iff in H5.
      induction H5; intros; subst; [pose proof H2 _ _ _ H0 _ _ H6; auto |].
      destruct y as [[c'' k''] st''].
      specialize (IHclos_trans_1n eq_refl _ _ _ eq_refl).


      specialize (H2 _ _ _ H)
    + destruct H3 as [_ [? _]].
      apply H3 in H4.
      exfalso; apply (reducible_irreducible_ex c k st); auto.

    apply WP_Pre.
    + apply H in H3.
      destruct H3 as [_ [? _]].
    
    apply Hsym in H3.
      specialize (H _ _ _ _ H3) as [_ ?].
      destruct H0 as [c' [k' [st' ?]]].
      specialize (H _ _ _ _ H0) as (c2' & k2' & ? & ?).
      exists c2', k2', st'. auto.
    + intros.
      specialize (H _ _ _ _ H3) as [_ ?].
      specialize (H _ _ _ _ H4) as (c2' & k2' & ? & ?).
      specialize (H2 _ _ _ H _ _ H5). auto.
Admitted. *)



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
