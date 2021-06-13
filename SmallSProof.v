Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.

Import Assertion_S.
Import SmallS.


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
