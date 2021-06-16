Require Import Shallow.lib.RTClosure.
Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.

Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Classes.RelationClasses.

Import Assertion_S.
Import SmallS.

Lemma wp_sim : forall c1 c2 k1 k2 Q Rb Rc st sim,
  simulation sim ->
  (* sim (c1, k1) (c2, k2) -> *)
  Symmetric sim ->
  sim (c2, k2) (c1, k1) ->
  WP c1 k1 Q Rb Rc st ->
  WP c2 k2 Q Rb Rc st.
Proof.
  intros.
  rename H0 into Hsym.
  rename H1 into H0.
  rename H2 into H1.
  revert c2 k2 H0.
  induction H1; intros.
  - unfold simulation in H.
    apply H in H1.
    pose proof excluded_middle_informative (reducible c2 k2 st) as Hred.
    destruct Hred as [Hred | Hred].
    + destruct H1 as [_ ?].
      apply WP_Pre; auto.
      intros.
      apply H1 in H2.
      destruct H2 as (c1' & k1' & ? & _).
      inversion H2.
    + destruct H1 as [? _].
      apply H1 in Hred.
      unfold mstep in Hred.
      rewrite rt_rt1n_iff in Hred.
      inversion Hred; subst.
      * apply WP_Ter1; auto.
      * inversion H2. 

    (* destruct H1 as [? _].
    assert (~ reducible CSkip nil st).
    { unfold not; intros. destruct H2 as (? & ? & ? & ?). inversion H2. }
    specialize (H1 st H2).
    unfold mstep in H1.
    rewrite rt_rt1n_iff in H1.
    remember (c2, k2, st) as prog.
    remember (@pair (prod com continuation) state (@pair com continuation CSkip (@nil KElements)) st) as term.
    remember st as st0.
    rewrite Heqst0 in Heqprog; rewrite Heqst0; clear Heqst0.
    revert dependent st.
    revert dependent k2.
    revert c2 .
    induction H1; subst; intros.
    + inversion Heqprog; subst. apply WP_Ter1; auto.
    + destruct y as [[c2' k2'] st']; subst.
      specialize (IHclos_refl_trans_1n eq_refl).
       (* c2' k2' st' eq_refl). *)
      apply WP_Pre.
      * exists c2', k2', st'. auto.
      *  

    inversion H; subst.
    apply WP_Ter1. auto. *)
    
  - admit.
  - admit.
  - unfold simulation in H.
    unfold Symmetric in Hsym.  
    apply WP_Pre.
    + apply Hsym in H3.
      specialize (H _ _ _ _ H3) as [_ ?].
      destruct H0 as [c' [k' [st' ?]]].
      specialize (H _ _ _ _ H0) as (c2' & k2' & ? & ?).
      exists c2', k2', st'. auto.
    + intros.
      specialize (H _ _ _ _ H3) as [_ ?].
      specialize (H _ _ _ _ H4) as (c2' & k2' & ? & ?).
      specialize (H2 _ _ _ H _ _ H5). auto.
Admitted.



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
