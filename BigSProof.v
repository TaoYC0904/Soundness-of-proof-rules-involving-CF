Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.

Import Assertion_S.
Import BigS.


Theorem seq_inv_valid_bigstep : forall P c1 c2 Q R1 R2,
  total_valid_bigstep P (CSeq c1 c2) Q R1 R2 ->
  (exists Q', (total_valid_bigstep P c1 Q' R1 R2) /\ 
    (total_valid_bigstep Q' c2 Q R1 R2)).
Admitted.

Theorem if_seq_valid_bigstep : forall P b c1 c2 c3 Q R1 R2,
  total_valid_bigstep P (CSeq (CIf b c1 c2) c3) Q R1 R2 ->
  total_valid_bigstep P (CIf b (CSeq c1 c3) (CSeq c2 c3)) Q R1 R2.
Admitted.

Theorem nocontinue_valid_bigstep : forall P c Q R1 R2 R2',
  nocontinue c ->
  total_valid_bigstep P c Q R1 R2 ->
  total_valid_bigstep P c Q R1 R2'.
Admitted.

Theorem loop_nocontinue_valid_bigstep : forall P c1 c2 Q R1 R2,
  nocontinue c1 ->
  nocontinue c2 ->
  total_valid_bigstep P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  total_valid_bigstep P (CFor c1 c2) Q R1 R2.
Admitted.

