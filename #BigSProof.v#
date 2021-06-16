Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.

Import Assertion_Shallow.
Import BigS.

Definition SP (P : Assertion) (c : com) (st : state): Prop :=
  exists st0, Assertion_denote st0 P /\ ceval c st0 EK_Normal st.

Lemma seq_c1_valid : forall P c1 c2 Q R1 R2 Q',
  total_valid_bigstep P (CSeq c1 c2) Q R1 R2 ->
  Q' = SP P c1 ->
  total_valid_bigstep P c1 Q' R1 R2.
Proof.
  intros.
  unfold total_valid_bigstep in H.
  unfold total_valid_bigstep.
  destruct H.
  split.
  + (* terminate *)
    intros.
    specialize (H st1 H2).
    destruct H as [ek [st2 ?]].
    simpl in H; unfold seq_sem in H.
    destruct H.
    - (* c1 Normal *)
      destruct H as [st3 [? ?]].
      exists EK_Normal, st3; tauto.
    - (* c1 Break or Cont *)
      destruct H.
      exists ek, st2; tauto.
  + (* partial validity *)
    unfold partial_valid_bigstep in H1.
    unfold partial_valid_bigstep.
    intros.
    destruct ek.
    - (* c1 Normal *)
      split; try split; intros; inversion H4.
      subst Q'.
      unfold Assertion_denote, SP.
      exists st1; tauto.
    - (* c1 Break *)
      split; try split; intros; inversion H4.
      assert (ceval (CSeq c1 c2) st1 EK_Break st2).
      { simpl; unfold seq_sem.
        right.
        split; [tauto | unfold not; intros; inversion H5]. }
      specialize (H1 st1 st2 EK_Break H2 H5).
      destruct H1 as [? [? ?]].
      apply H6; tauto.
    - (* c1 Cont *)
      split; try split; intros; inversion H4.
      assert (ceval (CSeq c1 c2) st1 EK_Cont st2).
      { simpl; unfold seq_sem.
        right.
        split; [tauto | unfold not; intros; inversion H5]. }
      specialize (H1 st1 st2 EK_Cont H2 H5).
      destruct H1 as [? [? ?]].
      apply H7; tauto.
Qed.

Theorem seq_inv_valid_bigstep : forall P c1 c2 Q R1 R2,
  total_valid_bigstep P (CSeq c1 c2) Q R1 R2 ->
  (exists Q', (total_valid_bigstep P c1 Q' R1 R2) /\ 
    (total_valid_bigstep Q' c2 Q R1 R2)).
Proof.
  intros.
  remember (SP P c1) as Q'.
  exists Q'.
  pose proof seq_c1_valid.
  specialize (H0 P c1 c2 Q R1 R2 Q' H HeqQ').
  split; try tauto.
  unfold total_valid_bigstep.
  unfold total_valid_bigstep in H, H0.
  destruct H, H0.
  split.
  + (* termination *)
    subst Q'.
    unfold Assertion_denote, SP.
    intros.
    destruct H3 as [st0 [? ?]].
    simpl in H.
    unfold seq_sem in H.
    specialize (H st0 H3).
    
    
Admitted.

(* Proof.
  unfold total_valid_bigstep.
  intros.
  exists (SP P c1).
  remember (SP P c1) as Q'.
  pose proof seq_c1_valid.
  specialize (H0 P c1 c2 Q R1 R2 Q' H HeqQ').
  rename H0  into HLemma.
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
    split.
    - (* termination *)
      rewrite HeqQ'.
      unfold Assertion_denote, SP.
      intros.
      destruct H1 as [st0 [? ?]].
      specialize (H st0 H1).
      destruct H as [ek [st2 ?]].
      simpl in H; unfold seq_sem in H.
      destruct H.
      * (* c1 Normal *)
        destruct H as [st3 [? ?]].
        pose proof determinism.
        specialize (H4 c1 st0 st1 st3 EK_Normal EK_Normal H2 H).
        destruct H4; subst.
        exists ek, st2; tauto.
      * (* c1 Break or Cont *)
        destruct H.
        pose proof determinism.
        specialize (H4 c1 st0 st2 st1 ek EK_Normal H H2).
        tauto.
    - (* partial validity *)
      clear H.
      unfold partial_valid_bigstep in H0.
      unfold partial_valid_bigstep.
      intros.
      subst Q'.
      unfold Assertion_denote, SP in H.
      destruct H as [st0 [? ?]].
      specialize (H0 st0 st2 ek H).
      apply H0.
      simpl; unfold seq_sem.
      left.
      exists st1.
      split; try tauto.
Qed. *)

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
  + (* c = CBreak *)
    destruct H0 as [st2 ?].
    simpl in H0.
    unfold break_sem in H0.
    destruct H0.
    inversion H1.
  + (* c = CCont *)
    simpl in H.
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
Proof.
  unfold total_valid_bigstep.
  intros.
  destruct H1.
  split; intros.
  + (* termination *)
    specialize (H1 st1 H3).
    destruct H1 as [ek [st2 ?]].
    exists ek, st2.
    simpl in H1. unfold for_sem in H1.
    destruct H1; subst.
    destruct H4 as [n ?].
    simpl; unfold for_sem.
    split; try tauto.
    exists n.
    induction n.
    - (* n = 0 *)
      apply ILB_0; try tauto.
      remember (seq_sem (ceval c1) (ceval c2)) as d1.
      remember (skip_sem) as d2.
      destruct H1.
      destruct H4.
      * (* d1 Break *)
        subst d1.
        unfold seq_sem in H4.
        destruct H4.
        ++ (* c1 Normal *)
           right; tauto.
        ++ (* c1 Break or Cont *)
           left; tauto.
      * (* d1 Normal; d2 Break *)
        destruct H4 as [st3 [? ?]].
        subst d2.
        unfold skip_sem in H5.
        destruct H5; inversion H6.
        
        
      
      
      
    
  
Admitted.

