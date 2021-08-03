Require Import Coq.Lists.List.
Require Import Shallow.Imp Shallow.Embeddings.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

Module OptF.

Definition add {A : Type} (f g : A -> option Z) : A -> option Z :=
  fun st =>
    match f st, g st with
      | Some v1, Some v2 => Some (v1 + v2)
      | _, _ => None
    end.

Definition sub {A : Type} (f g : A -> option Z) : A -> option Z :=
  fun st =>
    match f st, g st with
      | Some v1, Some v2 => Some (v1 - v2)
      | _, _ => None
    end.

Definition mul {A : Type} (f g : A -> option Z) : A -> option Z :=
  fun st =>
    match f st, g st with
      | Some v1, Some v2 => Some (v1 * v2)
      | _, _ => None
    end.

Definition div {A : Type} (f g : A -> option Z) : A -> option Z :=
  fun st =>
    match f st, g st with
      | Some v1, Some v2 =>
          if Z.eq_dec v2 0 then None else Some (v1 / v2)
      | _, _ => None
    end.

End OptF.

Module Denote_Aexp.

Fixpoint aeval (a : aexp) : state -> option Z :=
  match a with
    | ANum n => fun _ => Some n
    | AId X => fun st => Some (st X)
    | APlus a1 a2 => OptF.add (aeval a1) (aeval a2)
    | AMinus a1 a2 => OptF.sub (aeval a1) (aeval a2)
    | AMult a1 a2 => OptF.mul (aeval a1) (aeval a2)
    | ADiv a1 a2 => OptF.div (aeval a1) (aeval a2)
  end.

End Denote_Aexp.

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Record bexp_denote : Type := {
  true_set : state -> Prop;
  false_set : state -> Prop;
  error_set : state -> Prop; }.

Definition opt_test (R: Z -> Z -> Prop) (X Y: state -> option Z): bexp_denote :=
  {|
    true_set := fun st =>
      match X st, Y st with
        | Some n1, Some n2 => R n1 n2
        | _, _ => False
      end;
    false_set := fun st =>
      match X st, Y st with
        | Some n1, Some n2 => ~R n1 n2
        | _, _ => False
      end;
    error_set := fun st =>
      match X st, Y st with
        | Some n1, Some n2 => False
        | _, _ => True
      end;
  |}.

Module Sets.

Definition union {A : Type} (X Y : A -> Prop) : A -> Prop :=
  fun a => X a \/ Y a.

Definition omega_union {A} (X : nat -> A -> Prop) : A -> Prop :=
  fun a => exists n, X n a.

End Sets.

Module Denote_Bexp.
Import Denote_Aexp.

Fixpoint beval (b : bexp) : bexp_denote :=
  match b with
  | BTrue =>
      {| true_set := Sets.full;
         false_set := Sets.empty;
         error_set := Sets.empty; |}
  | BFalse =>
      {| true_set := Sets.empty;
         false_set := Sets.full;
         error_set := Sets.empty; |}
  | BEq a1 a2 => 
      opt_test Z.eq (aeval a1) (aeval a2)
  | BLe a1 a2 =>
      opt_test Z.le (aeval a1) (aeval a2)
  | BNot b =>
      {| true_set := false_set (beval b);
         false_set := true_set (beval b);
         error_set := error_set (beval b); |}
  | BAnd b1 b2 =>
      {| true_set := Sets.intersect (true_set (beval b1)) (true_set (beval b2));
         false_set := Sets.union (false_set (beval b1))
                                 (Sets.intersect (true_set (beval b1))
                                                 (false_set (beval b2)));
         error_set := Sets.union (error_set (beval b1))
                                 (Sets.intersect (true_set (beval b1))
                                                 (error_set (beval b2))); |}
  end.

End Denote_Bexp.

Inductive com : Type :=
  | CSkip
  | CAss (X : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CFor (c1 c2 : com)
  | CBreak
  | CCont.

Record com_denote : Type := {
  com_normal : state -> state -> Prop;
  com_break : state -> state -> Prop;
  com_cont : state -> state -> Prop;
  com_error : state -> Prop }.

Module Denote_Com.
Import Denote_Aexp.
Import Denote_Bexp.

Definition skip_sem : com_denote := {|
  com_normal := fun st1 st2 => st1 = st2;
  com_break := fun st1 st2 => False;
  com_cont := fun st1 st2 => False;
  com_error := fun st => False; |}.

Definition asgn_sem (X : var) (DA : state -> option Z) : com_denote := {|
  com_normal := fun st1 st2 => (Some (st2 X) = DA st1) /\ (forall Y, Y <> X -> st2 Y = st1 Y);
  com_break := fun st1 st2 => False;
  com_cont := fun st1 st2 => False;
  com_error := fun st => DA st = None; |}.

Definition seq_sem (DC1 DC2 : com_denote) : com_denote := {|
  com_normal := fun st1 st2 =>
    exists st3, com_normal DC1 st1 st3 /\ com_normal DC2 st3 st2;
  com_break := fun st1 st2 =>
    (com_break DC1 st1 st2) \/
    (exists st3, com_normal DC1 st1 st3 /\ com_break DC2 st3 st2);
  com_cont := fun st1 st2 =>
    (com_cont DC1 st1 st2) \/
    (exists st3, com_normal DC1 st1 st3 /\ com_cont DC2 st3 st2);
  com_error := fun st =>
    (com_error DC1 st) \/ (exists st', com_normal DC1 st st' /\ com_error DC2 st'); |}.

Definition if_sem (DB : bexp_denote) (DC1 DC2 : com_denote) : com_denote := {|
  com_normal := fun st1 st2 =>
    (true_set DB st1 /\ com_normal DC1 st1 st2) \/
    (false_set DB st1 /\ com_normal DC2 st1 st2);
  com_break := fun st1 st2 =>
    (true_set DB st1 /\ com_break DC1 st1 st2) \/
    (false_set DB st1 /\ com_break DC2 st1 st2);
  com_cont := fun st1 st2 =>
    (true_set DB st1 /\ com_cont DC1 st1 st2) \/
    (false_set DB st1 /\ com_cont DC2 st1 st2);
  com_error := fun st =>
    (error_set DB st) \/
    (true_set DB st /\ com_error DC1 st) \/
    (false_set DB st /\ com_error DC2 st) |}.

Fixpoint iter_loop_body (DC1 DC2 : com_denote) (n : nat) : com_denote :=
  match n with
  | O => {|
      com_normal := fun st1 st2 =>
        (com_break DC1 st1 st2) \/
        (exists st3, com_normal DC1 st1 st3 /\ com_break DC2 st3 st2);
      com_break := fun st1 st2 => False;
      com_cont := fun st1 st2 => False;
      com_error := fun st =>
        (com_error DC1 st) \/
        (exists st', com_normal DC1 st st' /\ com_error DC2 st') |}
  | S n' => {|
      com_normal := fun st1 st2 => exists st3,
        ((com_normal (seq_sem DC1 DC2) st1 st3) \/ (com_cont (seq_sem DC1 DC2) st1 st3)) /\
        (com_normal (iter_loop_body DC1 DC2 n') st3 st2);
      com_break := fun st1 st2 => False;
      com_cont := fun st1 st2 => False;
      com_error := fun st => exists st',
        ((com_normal (seq_sem DC1 DC2) st st') \/ (com_cont (seq_sem DC1 DC2) st st')) /\
        (com_error (iter_loop_body DC1 DC2 n') st') |}
  end.

Definition for_sem (DC1 DC2 : com_denote) : com_denote := {|
  com_normal := fun st1 st2 =>
    exists n, com_normal (iter_loop_body DC1 DC2 n) st1 st2;
  com_break := fun st1 st2 => False;
  com_cont := fun st1 st2 => False;
  com_error := fun st =>
    exists n, com_error (iter_loop_body DC1 DC2 n) st |}.

Definition break_sem : com_denote := {|
  com_normal := fun st1 st2 => False;
  com_break := fun st1 st2 => st1 = st2;
  com_cont := fun st1 st2 => False;
  com_error := fun st => False |}.

Definition cont_sem : com_denote := {|
  com_normal := fun st1 st2 => False;
  com_break := fun st1 st2 => False;
  com_cont := fun st1 st2 => st1 = st2;
  com_error := fun st => False |}.

Fixpoint ceval (c : com) : com_denote :=
  match c with 
  | CSkip => skip_sem
  | CAss X a => asgn_sem X (aeval a)
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem (beval b) (ceval c1) (ceval c2)
  | CFor c1 c2 => for_sem (ceval c1) (ceval c2)
  | CBreak => break_sem
  | CCont => cont_sem
  end.

End Denote_Com.

Module Denote_Embeddings.
Import Denote_Com.

Definition Assertion : Type := state -> Prop.

Definition Assertion_denote : state -> Assertion -> Prop :=
  fun st P => P st.

Definition com_term : com_denote -> state -> state -> Prop :=
  fun DC st1 st2 =>
    (com_normal DC st1 st2) \/ (com_break DC st1 st2) \/ (com_cont DC st1 st2).

Definition partial_valid (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  forall st1 st2, Assertion_denote st1 P ->
    (~ com_error (ceval c) st1) /\
    ((com_normal (ceval c) st1 st2) -> Assertion_denote st2 Q) /\
    ((com_break (ceval c) st1 st2) -> Assertion_denote st2 R1) /\
    ((com_cont (ceval c) st1 st2) -> Assertion_denote st2 R2).

Definition total_valid (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  (forall st1, Assertion_denote st1 P -> exists st2, com_term (ceval c) st1 st2) /\
  (partial_valid P c Q R1 R2).

End Denote_Embeddings.

Module rules_sound.
Import Denote_Com.
Import Denote_Embeddings.

Definition WP (c : com) (Q R1 R2 : Assertion) : state -> Prop :=
  fun st =>
    (~ (com_error (ceval c) st)) /\
    (forall st',
      (com_normal (ceval c) st st' -> Assertion_denote st' Q) /\
      (com_break (ceval c) st st' -> Assertion_denote st' R1) /\
      (com_cont (ceval c) st st' -> Assertion_denote st' R2)).

Theorem seq_inv_sound_bigstep : forall P c1 c2 Q R1 R2,
  partial_valid P (CSeq c1 c2) Q R1 R2 ->
    (exists Q', partial_valid P c1 Q' R1 R2 /\ partial_valid Q' c2 Q R1 R2).
Proof.
  intros.
  exists (WP c2 Q R1 R2).
  remember (WP c2 Q R1 R2) as Q'.
  split.
  + (* partial_valid P c1 Q' R1 R2 *)
    unfold partial_valid in *.
    intros.
    split; try split; try split; intros.
    - specialize (H st1 st2 H0).
      destruct H as [HE [HN [HB HC]]].
      simpl in HE.
      unfold not in *; intros; apply HE; tauto.
    - subst Q'; unfold WP, Assertion_denote in *.
      split.
      { specialize (H st1 st2 H0).
        destruct H as [HE [HN [HB HC]]].
        unfold not in *.
        intros; apply HE. 
        simpl; right; exists st2; tauto. }
      intros st3.
      specialize (H st1 st3 H0).
      destruct H as [HE [HN [HB HC]]].
      split; try split; intros; 
        [apply HN | apply HB | apply HC]; simpl;
        [ | right | right]; exists st2; tauto.
    - specialize (H st1 st2 H0).
      destruct H as [HE [HN [HB HC]]].
      apply HB; simpl; tauto.
    - specialize (H st1 st2 H0).
      destruct H as [HE [HN [HB HC]]].
      apply HC; simpl; tauto.
  + unfold partial_valid; subst Q'; unfold WP, Assertion_denote.
    intros.
    destruct H0 as [HE ?].
    specialize (H0 st2); tauto.
Qed.

Theorem if_seq_sound_bigstep : forall P b c1 c2 c3 Q R1 R2,
  partial_valid P (CIf b (CSeq c1 c3) (CSeq c2 c3)) Q R1 R2 ->
  partial_valid P (CSeq (CIf b c1 c2) c3) Q R1 R2.
Proof.
  
      
(* Theorem if_seq_sound_bigstep : forall P b c1 c2 c3 Q R1 R2,
  total_valid P (CSeq (CIf b c1 c2) c3) Q R1 R2 ->
  total_valid P (CIf b (CSeq c1 c3) (CSeq c2 c3)) Q R1 R2.
Proof.
  intros.
  unfold total_valid in H.
  unfold total_valid.
  destruct H.
  split.
  + (* safety *)
    intros.
    unfold not; intros.
    simpl in H2.
    specialize (H st1 H1).
    apply H.
    destruct H2 as [? | [? | ?]].
    - (* beval b error *)
      simpl. tauto.
    - (* b true *)
      destruct H2.
      destruct H3.
      * (* c3 error *)
        destruct H3 as [st' [? ?]].
        simpl. left.
        exists st'. 
        split; tauto.
      * (* c1 error *)
        simpl. tauto.
    - (* b false *)
      destruct H2.
      destruct H3.
      * (* c3 error *) 
        destruct H3 as [st' [? ?]].
        simpl. left.
        exists st'. tauto.
      * (* c2 error *)
        simpl. tauto.
  + (* partial validity *)
    unfold partial_valid in H0.
    unfold partial_valid.
    intros.
    specialize (H0 st1 ek st2 H1).
    apply H0; clear H0.
    simpl in H2. simpl.
    destruct H2.
    - (* b true *)
      destruct H0.
      destruct H2.
      * (* c1 Normal *)
        destruct H2 as [st3 [? ?]].
        left. exists st3. tauto.
      * (* c1 Break or Cont *)
        tauto.
    - (* b false *)
      destruct H0.
      destruct H2.
      * (* c2 Normal *)
        destruct H2 as [st3 [? ?]].
        left. exists st3. tauto.
      * (* c2 Break or Cont *)  
        tauto.
Qed. *)

Fixpoint nocontinue (c : com) : Prop :=
  match c with
  | CSkip         => True
  | CAss _ _      => True
  | CSeq c1 c2    => (nocontinue c1) /\ (nocontinue c2)
  | CIf b c1 c2   => (nocontinue c1) /\ (nocontinue c2)
  | CFor c1 c2    => True
  | CBreak        => True 
  | CCont         => False
  end.

Lemma nocontinue_nocontexit : forall (c : com) st1,
  nocontinue c ->
  ~(exists st2, com_term (ceval c) st1 EK_Cont st2).
Proof.
  intros.
  revert st1; induction c; unfold not; intros.
  + destruct H0 as [st2 ?]. simpl in H0. destruct H0. inversion H1.
  + destruct H0 as [st2 ?]. simpl in H0. destruct H0 as [? [? ?]]. inversion H2.
  + simpl in H; destruct H.
    destruct H0 as [st2 ?].
    simpl in H0. destruct H0.
    - destruct H0 as [st3 [? ?]].
      specialize (IHc2 H1 st3).
      apply IHc2. exists st2. tauto.
    - destruct H0 as [st3 ?].
      specialize (IHc1 H st1).
      apply IHc1. exists st2. tauto.
  + simpl in H; destruct H.
    destruct H0 as [st2 ?].
    simpl in H0. destruct H0.
    - destruct H0.
      specialize (IHc1 H st1).
      apply IHc1. exists st2. tauto.
    - destruct H0.
      specialize (IHc2 H1 st1).
      apply IHc2. exists st2. tauto.
  + destruct H0 as [st2 ?].
    simpl in H0.
    destruct H0 as [n ?].
    destruct n; simpl in H0.
    - destruct H0. inversion H1.
    - destruct H0 as [st3 [? ?]]. inversion H1.
  + destruct H0 as [st2 ?].
    simpl in H0.
    destruct H0. inversion H1.
  + inversion H.
Qed.

Theorem nocontinue_sound_bigstep : forall P c Q R1 R2 R2',
  nocontinue c ->
  total_valid P c Q R1 R2 ->
  total_valid P c Q R1 R2'.
Proof.
  intros.
  unfold total_valid in H0.
  unfold total_valid.
  destruct H0.
  split.
  + intros.
    specialize (H0 st1 H2); tauto.
  + unfold partial_valid in H1.
    unfold partial_valid.
    intros.
    specialize (H1 st1 ek st2 H2 H3).
    destruct H1 as [? [? ?]].
    split; try split; try tauto.
    intros; subst.
    pose proof nocontinue_nocontexit.
    specialize (H6 c st1 H).
    exfalso; apply H6.
    exists st2; tauto.
Qed.

Lemma add_skip: forall c st1 ek st2,
  com_term (ceval c) st1 ek st2 <-> 
    com_term (ceval (CSeq c CSkip)) st1 ek st2.
Proof.
  intros.
  unfold iff; split; intros.
  + (* add skip *)
    simpl.
    destruct ek.
    - (* c Normal *)
      left; exists st2; tauto.
    - (* c Break *)
      right; split; try tauto.
      unfold not; intros; inversion H0.
    - (* c Cont *)
      right; split; try tauto.
      unfold not; intros; inversion H0.
  + (* sub skip *)
    simpl in H.
    destruct H.
    - (* c1 Normal *)
      destruct H as [st3 [? [? ?]]]; subst; tauto.
    - (* c1 Break or Cont *)
      tauto.
Qed.

Theorem loop_nocontinue_sound_bigstep : forall P c1 c2 Q R1 R2,
  nocontinue c1 ->
  nocontinue c2 ->
  total_valid P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  total_valid P (CFor c1 c2) Q R1 R2.
Proof.
  intros.
  unfold total_valid in H1.
  unfold total_valid.
  destruct H1; split.
  + (* safety *)
    intros.
    specialize (H1 st1 H3).
    unfold not; intros; apply H1.
    simpl in H4; simpl.
    destruct H4 as [n ?].
    exists n.
    clear H1 H2 H3.
    revert st1 H4.
    induction n.
    - (* n = O *)
      intros.
      simpl in H4; simpl.
      destruct H4.
      * (* c1 error *)
        tauto.
      * (* c2 error *)
        destruct H1 as [st2 [? ?]].
        left. left. exists st2; tauto.
    - (* n = S n'*) 
      intros.
      inversion H4; subst; clear H4.
      rename x into st2.
      destruct H1. destruct H1.
      2:{
        assert (nocontinue (CSeq c1 c2)).
        { simpl. tauto. }
        pose proof nocontinue_nocontexit.
        specialize (H4 (CSeq c1 c2) st1 H3).
        exfalso; apply H4; exists st2; tauto. }
      specialize (IHn st2 H2).
      clear H2.
      simpl in H1. destruct H1.
      * (* c1 Normal *)
        destruct H1 as [st3 [? ?]].
        simpl. 
        exists st2; split; try tauto.
        left. left. 
        exists st2. split; try split; try tauto.
        left. exists st3. tauto.
      * (* c1 Break or Cont *)
        destruct H1. contradiction.
  + (* partial validity *)  
    unfold partial_valid in H2.
    unfold partial_valid.
    intros.
    specialize (H2 st1 ek st2 H3).
    apply H2; clear H1 H2 H3.
    simpl in H4; simpl.
    destruct H4 as [n ?].
    exists n.
    revert st1 H1.
    induction n.
    - (* n = O *)
      intros.
      simpl in H1. 
      destruct H1; subst.
      destruct H1.
      * (* c1 Break *)
        simpl. split; try tauto.
        left. right. 
        split; try tauto.
        unfold not; intros; inversion H2.
      * (* c2 Break *)
        simpl. split; try tauto.
    - (* n = S n' *) 
      intros.
      simpl in H1.
      destruct H1 as [st3 [? ?]]; subst.
      destruct H1.
      specialize (IHn st3 H2); clear H2.
      destruct H1.
      2:{ (* first iteration Cont *)
        destruct H1.
        * destruct H1 as [st4 [? ?]].
          pose proof nocontinue_nocontexit.
          specialize (H3 c2 st4 H0).
          exfalso; apply H3.
          exists st3; tauto.
        * destruct H1.
          pose proof nocontinue_nocontexit.
          specialize (H3 c1 st1 H).
          exfalso; apply H3.
          exists st3; tauto. }
      (* first iteration Normal *)
      destruct H1.
      2:{ destruct H1. contradiction. }
      destruct H1 as [st4 [? ?]].
      simpl. exists st3.
      split; try split; try tauto.
      left. left. exists st3.
      split; try split; try tauto.
      left. exists st4. tauto.
Qed. 
End rules_sound.