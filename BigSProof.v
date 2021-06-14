Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.

Import Assertion_S.
Import BigS.

(* Definition inSP (st : state) (P : Assertion) (c : com) : Prop :=
  exists st0, Assertion_denote st0 P /\ ceval c st0 EK_Normal st.
  
Definition SP (P : Assertion) (c : com) : Assertion :=
   *)

Theorem seq_inv_valid_bigstep : forall P c1 c2 Q R1 R2,
  total_valid_bigstep P (CSeq c1 c2) Q R1 R2 ->
  (exists Q', (total_valid_bigstep P c1 Q' R1 R2) /\ 
    (total_valid_bigstep Q' c2 Q R1 R2)).
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

Lemma noncontinue_nocontext : forall P c Q R1 R2,
  nocontinue c ->
  total_valid_bigstep P c Q R1 R2 ->
  .


Theorem nocontinue_valid_bigstep : forall P c Q R1 R2 R2',
  nocontinue c ->
  total_valid_bigstep P c Q R1 R2 ->
  total_valid_bigstep P c Q R1 R2'.
Proof.
  intros.
  unfold total_valid_bigstep in H0.
  unfold total_valid_bigstep.
  destruct H0.
  destruct c.
  + 
  
  
  
    
  
Admitted.

Theorem loop_nocontinue_valid_bigstep : forall P c1 c2 Q R1 R2,
  nocontinue c1 ->
  nocontinue c2 ->
  total_valid_bigstep P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  total_valid_bigstep P (CFor c1 c2) Q R1 R2.
Admitted.

