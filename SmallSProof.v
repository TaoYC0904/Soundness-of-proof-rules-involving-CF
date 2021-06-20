Require Import Shallow.lib.RTClosure.
Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.

Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Operators_Properties.

Import Assertion_S.
Import SmallS.

Definition simulation (sim : (com * continuation) -> (com * continuation) -> Prop) : Prop := forall c1 k1 c2 k2,
  sim (c1, k1) (c2, k2) ->  (* c2 simulates c1 *)
  (Halt c1 k1 -> (c1, k1) = (c2, k2)) /\
  (~ Halt c1 k1 -> forall st, ~ reducible c1 k1 st -> ~ reducible c2 k2) /\
  (* (Error c1 k1 -> Error c2 k2) /\ *)
  (forall c1' k1' st st',
    cstep (c1, k1, st) (c1', k1', st') ->
    exists c2' k2',
    mstep (c2, k2, st) (c2', k2', st') /\ sim (c1', k1') (c2', k2')).


Lemma wp_sim : forall c1 c2 k1 k2 Q Rb Rc st sim,
  simulation sim ->
  sim (c2, k2) (c1, k1) ->
  WP c1 k1 Q Rb Rc st ->
  WP c2 k2 Q Rb Rc st.
Proof.
  intros.
  revert c2 k2 H0.
  induction H1; intros.
  - unfold simulation in H.
    pose proof H1 as Hsim.
    apply H in H1.
    pose proof halt_choice c2 k2.
    destruct H2 as [? | [? | ?]].
    + destruct H1 as [? _].
      specialize (H1 H2).
      inversion H1; subst.
      apply WP_Ter1; auto.
    + destruct H1 as [_ [? _]].
      specialize (H1 H2).
      inversion H1.
      exfalso; apply H3.
      unfold Halt.
      left. unfold NHalt. auto.
    + destruct H1 as [_ [_ ?]].
      destruct H2 as (? & ? & ? & ? & ?).
      apply H1 in H2.
      destruct H2 as (? & ? & ? & ?).
      unfold mstep in H2.
      apply clos_trans_t1n_iff in H2.
      inversion H2; inversion H4.
  - admit.
  - admit.
  - unfold simulation in H.
    apply WP_Pre.
    + apply H in H3.
      destruct H3 as [_ [? _]].
      unfold Error in H3.
    
    apply Hsym in H3.
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
