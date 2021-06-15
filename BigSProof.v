Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.

Import Assertion_Shallow.
Import BigS.

Definition SP (P : Assertion) (c : com) (st : state): Prop :=
  exists st0, Assertion_denote st0 P /\ ceval c st0 EK_Normal st.
  

Definition state_update (st: state) (X: var) (v: Z): state :=
  fun Y => if (Nat.eq_dec X Y) then v else st Y.

Lemma state_update_spec: forall st X v,
  (state_update st X v) X = v /\
  (forall Y, X <> Y -> st Y = (state_update st X v) Y).
Proof.
  intros.
  unfold state_update.
  split.
  + destruct (Nat.eq_dec X X).
    - reflexivity.
    - assert (X = X). { reflexivity. }
      tauto.
  + intros.
    destruct (Nat.eq_dec X Y).
    - tauto.
    - reflexivity.
Qed.

Lemma determination_when_Normal: forall c st1 st2 st3,
  ceval c st1 EK_Normal st2 ->
  ceval c st1 EK_Normal st3 ->
  st2 = st3.
Proof.
  intros.
  induction c; simpl in H; simpl in H0.
  + unfold skip_sem in H, H0.
    destruct H, H0.
    rewrite <-H, <-H0.
    tauto.
  + unfold asgn_sem in H, H0.
    destruct H, H0.
    destruct H1, H2.
    remember (aeval a st1) as v.
    assert (st2 = state_update st1 X v).
    

Admitted.

Theorem seq_inv_valid_bigstep : forall P c1 c2 Q R1 R2,
  total_valid_bigstep P (CSeq c1 c2) Q R1 R2 ->
  (exists Q', (total_valid_bigstep P c1 Q' R1 R2) /\ 
    (total_valid_bigstep Q' c2 Q R1 R2)).
Proof.
  unfold total_valid_bigstep.
  intros.
  exists (SP P c1).
  remember (SP P c1) as Q'.
  destruct H.
  split; intros.
  + (* semantics of c1 *)
    split; intros.
    - (* termination *)
      specialize (H st1 H1).
      destruct H as [ek [st2 ?]].
      simpl in H.
      unfold seq_sem in H.
      destruct H.
      * (* c1 normal exit *) 
        destruct H as [st3 [? ?]].
        exists EK_Normal, st3.
        tauto.
      * (* c1 break or cont *)
        destruct H.
        exists ek, st2.
        tauto.
    - (* partial validity *)
      unfold partial_valid_bigstep in H0.
      unfold partial_valid_bigstep.
      clear H.
      intros.
      destruct ek.
      ++ (* c1 normal exit *)
         split; try split; intros; try inversion H2.
         rewrite HeqQ'.
         unfold Assertion_denote, SP.
         exists st1.
         tauto.
      ++ (* c1 break exit *)
         split; try split; intros; try inversion H2.
         specialize (H0 st1 st2 EK_Break H).
         assert (ceval (CSeq c1 c2) st1 EK_Break st2).
         { simpl. unfold seq_sem.
           right.
           split; intros; try tauto.
           unfold not; intros; inversion H3. }
         specialize (H0 H3).
         destruct H0 as [? [? ?]].
         apply H4; tauto.
      ++ (* c1 cont exit *)
         split; try split; intros; try inversion H2.
         specialize (H0 st1 st2 EK_Cont H).
         assert (ceval (CSeq c1 c2) st1 EK_Cont st2).
         { simpl. unfold seq_sem.
           right.
           split; intros; try tauto.
           unfold not; intros; inversion H3. }
         specialize (H0 H3).
         destruct H0 as [? [? ?]].
         apply H5; tauto.
  + (* semantics of c2 *)
    split; intros.
    - (* termination *)
      subst Q'.
      unfold Assertion_denote, SP in H1.
      destruct H1 as [st0 [? ?]].
      specialize (H st0 H1).
      destruct H as [ek [st2 ?]].
      simpl in H.
      unfold seq_sem in H.
      destruct H.
      * (* c1 normal exit *)
Admitted.




Theorem if_seq_valid_bigstep : forall P b c1 c2 c3 Q R1 R2,
  total_valid_bigstep P (CSeq (CIf b c1 c2) c3) Q R1 R2 ->
  total_valid_bigstep P (CIf b (CSeq c1 c3) (CSeq c2 c3)) Q R1 R2.
Proof.
  unfold total_valid_bigstep.
  intros; destruct H; split.
  + (* Termination *)
    intros.
    specialize (H st1 H1).
    destruct H as [ek [st2 ?]].
    exists ek, st2.
    simpl in H; simpl.
    unfold seq_sem, if_sem in H.
    unfold if_sem.
    unfold union_sem.
    destruct H.
    - (* (If b Then c1 Else c2) Normal Exit *)
      destruct H as [st3 [? ?]].
      unfold union_sem in H.
      destruct H.
      * (* b = True *)
        left.
        unfold seq_sem in H.
        unfold seq_sem at 1.
        destruct H.
        ++ (* c1 Normal Exit *)
           left.
           destruct H as [st4 [? ?]].
           unfold test_sem in H.
           destruct H as [? [? ?]]; subst.
           unfold test_sem.
           exists st4.
           split; try tauto.
           unfold seq_sem; left.
           exists st3; tauto.
        ++ (* c1 Break or Cont *)
           tauto.
      * (* b = False *)
        right.
        unfold seq_sem in H.
        unfold seq_sem at 1.
        destruct H.
        ++ (* c2 Normal Exit *)
           left.
           destruct H as [st4 [? ?]].
           unfold test_sem in H.
           destruct H as [? [? ?]]; subst.
           unfold test_sem.
           exists st4.
           split; try tauto.
           unfold seq_sem; left.
           exists st3; tauto.
        ++ tauto.
    - (* (If b Then c1 Else c2) Break or Cont *)
      destruct H.
      unfold union_sem in H.
      destruct H.
      * (* b = True *)
        left.
        unfold seq_sem in H.
        unfold seq_sem.
        destruct H.
        ++ (* c1 Normal Exit *)
           left.
           destruct H as [st3 [? ?]].
           exists st3. tauto.
        ++ (* c1 Break or Cont *)
           right.
           tauto.
      * (* b = False *)
        right.
        unfold seq_sem in H.
        unfold seq_sem.
        destruct H.
        ++ (* c1 Normal Exit *)
           left.
           destruct H as [st3 [? ?]].
           exists st3. tauto.
        ++ (* c1 Break or Cont *)
           right.
           tauto.
  + (* partial validity *)
    unfold partial_valid_bigstep in H0.
    unfold partial_valid_bigstep.
    intros.
    specialize (H0 st1 st2 ek H1).
    apply H0.
    simpl in H2; simpl.
    unfold if_sem in H2.
    unfold union_sem in H2.
    unfold if_sem.
    unfold seq_sem at 1.
    destruct H2.
    - (* b = True *)
      unfold seq_sem at 1 in H2.
      destruct H2.
      * (* test Normal Exit *)
        destruct H2 as [st3 [? ?]].
        unfold test_sem in H2.
        destruct H2 as [? [? ?]]; subst.
        unfold seq_sem in H3.
        destruct H3.
        ++ (* c1 Normal Exit *)
           destruct H2 as [st4 [? ?]].
           left.
           exists st4.
           split; try tauto.
           unfold union_sem; left.
           unfold test_sem, seq_sem.
           left.
           exists st3.
           tauto.
        ++ (* c1 Break or Cont *)
           destruct H2.
           right.
           split; try tauto.
           unfold union_sem; left.
           unfold test_sem, seq_sem.
           left.
           exists st3.
           tauto.
      * (* test Break or Cont *)
        destruct H2.
        unfold test_sem in H2.
        tauto.
    - (* b = False *)
      unfold seq_sem at 1 in H2.
      destruct H2.
      * (* test Normal Exit *)
        destruct H2 as [st3 [? ?]].
        unfold test_sem in H2.
        destruct H2 as [? [? ?]]; subst.
        unfold seq_sem in H3.
        destruct H3.
        ++ (* c2 Normal Exit *)
           destruct H2 as [st4 [? ?]].
           left.
           exists st4.
           split; try tauto.
           unfold union_sem; right.
           unfold test_sem, seq_sem.
           left.
           exists st3.
           tauto.
        ++ (* c2 Break or Cont *)
           destruct H2.
           right.
           split; try tauto.
           unfold union_sem; right.
           unfold test_sem, seq_sem.
           left.
           exists st3.
           tauto.
        * (* test Break or Cont *)
          destruct H2.
          unfold test_sem in H2.
          tauto.
Qed.


Lemma nocontinue_nocontexit : forall c st1,
  nocontinue c ->
  ( (exists st2, ceval c st1 EK_Cont st2) -> False).
Proof.
  intros c.
  induction c; intros.
  + (* c = CSkip *)
    destruct H0 as [st2 ?].
    simpl in H0; unfold skip_sem in H0.
    destruct H0.
    inversion H1.
  + (* c = CAss X a *)
    destruct H0 as [st2 ?].
    simpl in H0; unfold asgn_sem in H0.
    destruct H0 as [? [? ?]].
    inversion H2.
  + (* c = CSeq c1 c2 *)
    destruct H0 as [st2 ?].
    simpl in H; destruct H.
    simpl in H0; unfold seq_sem in H0.
    destruct H0.
    - (* c1 Normal *)
      destruct H0 as [st3 [? ?]].
      specialize (IHc2 st3 H1).
      apply IHc2.
      exists st2; tauto.
    - (* c1 Break or Cont *)
      destruct H0.
      specialize (IHc1 st1 H).
      apply IHc1.
      exists st2; tauto.
  + (* c = CIf b c1 c2 *)
    destruct H0 as [st2 ?].
    simpl in H0; unfold if_sem in H0.
    unfold union_sem in H0.
    destruct H0.
    - (* b = True *)
      unfold seq_sem, test_sem in H0.
      destruct H0.
      * (* test Normal *)
        destruct H0 as [st3 [? ?]].
        destruct H0 as [? [? ?]]; subst.
        simpl in H; destruct H.
        specialize (IHc1 st3 H).
        apply IHc1.
        exists st2; tauto.
      * (* test Break or Cont *)
         destruct H0 as [[? [? ?]] ?].
         inversion H2.
     - (* b = False *)
        unfold seq_sem, test_sem in H0.
        destruct H0.
        * (* test Normal *)
          destruct H0 as [st3 [? ?]].
          destruct H0 as [? [? ?]]; subst.
          simpl in H; destruct H.
          specialize (IHc2 st3 H0).
          apply IHc2.
          exists st2; tauto.
        * (* test Break or Cont *)
          destruct H0 as [[? [? ?]] ?].
          inversion H2.
  + (* c = CFor c1 c2 *)
    destruct H0 as [st2 ?].
    simpl in H0.
    unfold for_sem in H0.
    destruct H0.
    inversion H0.
  + destruct H0 as [st2 ?].
    simpl in H0.
    unfold break_sem in H0.
    destruct H0.
    inversion H1.
  + simpl in H.
    tauto.
Qed.

Theorem nocontinue_valid_bigstep : forall P c Q R1 R2 R2',
  nocontinue c ->
  total_valid_bigstep P c Q R1 R2 ->
  total_valid_bigstep P c Q R1 R2'.
Proof.
  intros.
  unfold total_valid_bigstep in H0.
  unfold total_valid_bigstep.
  destruct H0.
  split.
  2:{ unfold partial_valid_bigstep in H1.
      unfold partial_valid_bigstep.
      intros.
      specialize (H1 st1 st2 ek H2 H3).
      destruct H1 as [? [? ?]].
      split; try split; try tauto.
      intros; subst ek.
      pose proof nocontinue_nocontexit.
      specialize (H6 c st1 H).
      exfalso.
      apply H6.
      exists st2; tauto. }
  intros.
  specialize (H0 st1 H2).
  destruct H0 as [ek [st2 ?]].
  exists ek, st2; tauto.
Qed.

Theorem loop_nocontinue_valid_bigstep : forall P c1 c2 Q R1 R2,
  nocontinue c1 ->
  nocontinue c2 ->
  total_valid_bigstep P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  total_valid_bigstep P (CFor c1 c2) Q R1 R2.
Admitted.

