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

Module Assertion_Shallow.
Import Denote_Aexp.
Import Denote_Bexp.
  
Definition Assertion : Type := state -> Prop.

Definition Assertion_denote : state -> Assertion -> Prop :=
  fun st P => P st.

Definition andp : Assertion -> Assertion -> Assertion :=
  fun P Q st => P st /\ Q st. 

Definition orp : Assertion -> Assertion -> Assertion :=
  fun P Q st => P st \/ Q st.

Definition negp : Assertion -> Assertion :=
  fun P st => ~ P st.

Definition falsep : Assertion :=
  fun st => False.

Definition inj : bexp -> Assertion :=
  fun b st => true_set (beval b) st.

Definition safea : aexp -> Assertion :=
  fun a st => ~ (aeval a) st = None.

Definition safeb : bexp -> Assertion :=
  fun b st => ~ error_set (beval b) st. 

Definition derives : Assertion -> Assertion -> Prop :=
  fun P Q => forall st, P st -> Q st.

Definition state_update (st : state) (X : var) (v : option Z) : state :=
  match v with
  | Some n => fun Y => if (Nat.eq_dec X Y) then n else st Y
  | None => fun Y => 0
  end.
  
Definition subst_assertion (P : Assertion) (X : var) (v : state -> option Z) : Assertion :=
  fun st => P (state_update st X (v st)).

End Assertion_Shallow.

Module Denote_Embeddings.
Import Denote_Com.
Import Assertion_Shallow.

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
Import Assertion_Shallow.

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
  intros.
  unfold partial_valid in *.
  intros.
  specialize (H st1 st2 H0).
  destruct H as [HE [HN [HB HC]]].
  split; [| split;[| split]].
  + unfold not in *; intros; apply HE.
    simpl in H; simpl.
    destruct H; try tauto.
    destruct H as [st3 [? ?]].
    right; destruct H; [left | right]; split; try tauto;
      right; exists st3; try tauto.
  + intros; apply HN.
    simpl in H; simpl.
    destruct H as [st3 [[? | ?] ?]]; [left | right];
      split; try tauto; exists st3; tauto.
  + intros; apply HB.
    simpl in H; simpl.
    destruct H; try tauto.
    destruct H as [st3 [[? | ?] ?]]; [left | right];
      split; try tauto; right; exists st3; tauto.
  + intros; apply HC.
    simpl in H; simpl.
    destruct H; try tauto.
    destruct H as [st3 [[? | ?] ?]]; [left | right];
      split; try tauto; right; exists st3; tauto.
Qed.

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
  ~(exists st2, com_cont (ceval c) st1 st2).
Proof.
  intros; revert st1.
  induction c; unfold not; intros; destruct H0 as [st2 ?].
  + inversion H0.
  + inversion H0.
  + simpl in H; destruct H as [Hc1 Hc2].
    unfold not in *.
    simpl in H0; destruct H0.
    - specialize (IHc1 Hc1 st1).
      apply IHc1; exists st2; tauto.
    - destruct H as [st3 ?].
      specialize (IHc2 Hc2 st3).
      apply IHc2; exists st2; tauto.
  + simpl in H0; simpl in H; destruct H as [Hc1 Hc2]; destruct H0.
    - specialize (IHc1 Hc1 st1).
      unfold not in IHc1; apply IHc1.
      exists st2; tauto.
    - specialize (IHc2 Hc2 st1).
      unfold not in IHc2; apply IHc2.
      exists st2; tauto.
  + simpl in H0; tauto.
  + simpl in H0; tauto.
  + simpl in H; tauto.
Qed.  

Theorem nocontinue_sound_bigstep : forall P c Q R1 R2 R2',
  nocontinue c ->
  partial_valid P c Q R1 R2 ->
  partial_valid P c Q R1 R2'.
Proof.
  intros.
  unfold partial_valid in *.
  intros.
  specialize (H0 st1 st2 H1).
  split; [tauto | split; [tauto | split; try tauto]].
  clear H0; intros.
  pose proof (nocontinue_nocontexit c st1 H).
  exfalso; unfold not in H2; apply H2.
  exists st2; tauto.
Qed.

Lemma loop_nocontinue_error : forall c1 c2 st1,
  com_error (ceval (CFor c1 c2)) st1 ->
  com_error (ceval (CFor (CSeq c1 c2) CSkip)) st1.
Proof.
  intros.
  simpl in *.
  destruct H as [n ?]; exists n.
  revert st1 H; induction n; intros.
  + simpl in *.
    destruct H; try tauto.
  + simpl in *.
    destruct H as [st2 [? ?]].
    exists st2; split.
    2:{ pose proof (IHn st2 H0); tauto. }
    destruct H.
    - destruct H as [st3 [? ?]].
      left. exists st2; split; try tauto.
      exists st3; tauto.
    - destruct H as [? | [st3 [? ?]]]; try tauto.
      right. left. right. exists st3; tauto.
Qed.

Lemma loop_nocontinue_normal : forall c1 c2 st1 st2,
  com_normal (ceval (CFor c1 c2)) st1 st2 ->
  com_normal (ceval (CFor (CSeq c1 c2) CSkip)) st1 st2.
Proof.
  intros.
  simpl in *.
  destruct H as [n ?]; exists n.
  revert st1 st2 H; induction n; intros.
  + simpl in *.
    destruct H; try tauto.
  + simpl in *.
    destruct H as [st3 [? ?]].
    exists st3; split.
    2:{ pose proof (IHn st3 st2 H0); tauto. }
    destruct H.
    - destruct H as [st4 ?].
      left. exists st3; split; try tauto; exists st4; tauto.
    - destruct H as [? | [st4 ?]]; try tauto.
      right. left. right. exists st4; tauto.
Qed.

Theorem loop_nocontinue_sound_bigstep : forall P c1 c2 Q R1 R2,
  nocontinue c1 ->
  nocontinue c2 ->
  partial_valid P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  partial_valid P (CFor c1 c2) Q R1 R2.
Proof.
  intros.
  unfold partial_valid in *.
  intros.
  specialize (H1 st1 st2 H2).
  destruct H1 as [HE [HN [HB HC]]].
  split; try split; try split.
  + unfold not in *; intros; apply HE.
    pose proof (loop_nocontinue_error c1 c2 st1); tauto.
  + intros; apply HN.
    pose proof (loop_nocontinue_normal c1 c2 st1 st2); tauto.
  + intros.
    simpl in H1. tauto.
  + intros.
    simpl in H1. tauto.
Qed.

End rules_sound.

Module basic_rules.
Import Denote_Aexp.
Import Denote_Bexp.
Import Denote_Com.
Import Denote_Embeddings.
Import Assertion_Shallow.

Theorem hoare_seq_sound : forall P Q R R1 R2 c1 c2,
  partial_valid P c1 Q R1 R2 ->
  partial_valid Q c2 R R1 R2 ->
  partial_valid P (CSeq c1 c2) R R1 R2.
Proof.
  intros.
  unfold partial_valid in *.
  intros.
  split; try split; try split.
  + unfold not; intros.
    simpl in H2.
    destruct H2.
    - specialize (H st1 st2 H1); tauto.
    - destruct H2 as  [st3 [? ?]].
      specialize (H st1 st3 H1).
      assert (Assertion_denote st3 Q). { tauto. }
      specialize (H0 st3 st2 H4); tauto.
  + intros.
    simpl in H2.
    destruct H2 as [st3 [? ?]].
    specialize (H st1 st3 H1).
    assert (Assertion_denote st3 Q). { tauto. }
    specialize (H0 st3 st2 H4). tauto.
  + intros.
    simpl in H2.
    destruct H2.
    - specialize (H st1 st2 H1); tauto.
    - destruct H2 as [st3 [? ?]].
      specialize (H st1 st3 H1).
      assert (Assertion_denote st3 Q). { tauto. }
      specialize (H0 st3 st2 H4). tauto.
  + intros.
    simpl in H2.
    destruct H2.
    - specialize (H st1 st2 H1); tauto.
    - destruct H2 as [st3 [? ?]].
      specialize (H st1 st3 H1).
      assert (Assertion_denote st3 Q). { tauto. }
      specialize (H0 st3 st2 H4). tauto.
Qed.

Theorem hoare_skip_sound : forall P, 
  partial_valid P CSkip P falsep falsep.
Proof.
  intros.
  unfold partial_valid.
  intros.
  split; try split; try split.
  + unfold not; intros. inversion H0.
  + intros. simpl in H0; subst; tauto.
  + intros. inversion H0.
  + intros. inversion H0.
Qed.

Lemma true_notfalse : forall b st,
  true_set (beval b) st ->
  false_set (beval b) st -> False.
Proof.
  induction b; intros.
  + inversion H0.
  + inversion H.
  + simpl in *.
    destruct (aeval a1 st), (aeval a2 st); tauto. 
  + simpl in *.
    destruct (aeval a1 st), (aeval a2 st); tauto.
  + simpl in *. apply (IHb st); tauto.
  + simpl in *. 
    unfold Sets.intersect, Sets.union in *.
    specialize (IHb1 st); specialize (IHb2 st); tauto.
Qed.

Theorem hoare_if_sound : forall P Q R1 R2 b c1 c2,
  partial_valid (andp P (inj b)) c1 Q R1 R2 ->
  partial_valid (andp P (negp (inj b))) c2 Q R1 R2 ->
  partial_valid (andp P (safeb b)) (CIf b c1 c2) Q R1 R2.
Proof.
  unfold partial_valid in *.
  intros.
  unfold safeb, andp, inj, negp, Assertion_denote in *.
  split; try split; try split.
  + simpl. unfold not; intros.
    destruct H2 as [? | [? | ?]].
    - tauto.
    - specialize (H st1 st2); tauto.
    - specialize (H0 st1 st2).
      destruct H2.
      assert (~ true_set (beval b) st1).
      { unfold not; intros. apply (true_notfalse b st1); tauto. }
      tauto.
  + simpl; intros.
    destruct H2.
    - specialize (H st1 st2). tauto.
    - specialize (H0 st1 st2).
      assert (~ true_set (beval b) st1).
      { unfold not; intros. apply (true_notfalse b st1); tauto. }
      tauto.
  + simpl; intros.
    destruct H2.
    - specialize (H st1 st2). tauto.
    - specialize (H0 st1 st2).
      assert (~ true_set (beval b) st1).
      { unfold not; intros. apply (true_notfalse b st1); tauto. }
      tauto.
    + simpl; intros.
    destruct H2.
    - specialize (H st1 st2). tauto.
    - specialize (H0 st1 st2).
      assert (~ true_set (beval b) st1).
      { unfold not; intros. apply (true_notfalse b st1); tauto. }
      tauto.
Qed.

Theorem hoare_break_sound : forall P,
  partial_valid P CBreak falsep P falsep.
Proof.
  unfold partial_valid.
  intros.
  split; try split; try split.
  + unfold not; intros. inversion H0.
  + intros. inversion H0.
  + intros. inversion H0. subst. tauto.
  + intros. inversion H0.
Qed.

Theorem hoare_cont_sound : forall P,
  partial_valid P CCont falsep falsep P.
Proof.
  unfold partial_valid.
  intros.
  split; try split; try split.
  + unfold not; intros. inversion H0.
  + intros. inversion H0.
  + intros. inversion H0.
  + intros. inversion H0. subst. tauto.
Qed.

Theorem hoare_consequence_sound : forall P P' Q Q' R1 R1' R2 R2' c,
  derives P P' ->
  partial_valid P' c Q' R1' R2' ->
  derives Q' Q ->
  derives R1' R1 ->
  derives R2' R2 ->
  partial_valid P c Q R1 R2.
Proof.
  unfold derives, partial_valid, Assertion_denote in *.
  intros.
  specialize (H st1).
  specialize (H0 st1 st2).
  specialize (H1 st2).
  specialize (H2 st2).
  specialize (H3 st2).
  split; try split; try split; tauto.
Qed.

Theorem hoare_for_sound : forall I P c1 c2,
  partial_valid I (CSeq c1 c2) I P I ->
  partial_valid I (CFor c1 c2) (orp I P) falsep falsep.
Proof.
  unfold partial_valid, orp, falsep, Assertion_denote.
  intros.
  split; try split; try split; try tauto.
  + unfold not; intros.
    simpl in H1.
    destruct H1 as [n ?].
    revert st1 H1 H0; induction n; intros.
    - simpl in H1.
      specialize (H st1 st2 H0); destruct H.
      simpl in H. tauto.
    - simpl in H1.
      destruct H1 as [st3 [? ?]].
      specialize (IHn st3); apply IHn; try tauto.
      clear IHn H2.
      destruct H1 as [? | [? | ?]].
      * destruct H1 as [st4 [? ?]].
        specialize (H st1 st3 H0).
        assert (com_normal (ceval (CSeq c1 c2)) st1 st3).
        { simpl. exists st4; tauto. }
        tauto.
      * specialize (H st1 st3 H0).
        assert (com_cont (ceval (CSeq c1 c2)) st1 st3).
        { simpl. tauto. }
        tauto.
      * specialize (H st1 st3 H0).
        destruct H1 as [st4 [? ?]].
        assert (com_cont (ceval (CSeq c1 c2)) st1 st3).
        { simpl. right. exists st4; tauto. }
        tauto.
  + intros.
    simpl in H1.
    destruct H1 as [n ?].
    revert st1 st2 H0 H1; induction n; intros.
    - simpl in H1.
      destruct H1.
      * specialize (H st1 st2).
        assert (com_break (ceval (CSeq c1 c2)) st1 st2).
        { simpl. tauto. }
        tauto.
      * specialize (H st1 st2).
        assert (com_break (ceval (CSeq c1 c2)) st1 st2).
        { simpl. tauto. }
        tauto.
    - simpl in H1.
      destruct H1 as [st3 [? ?]].
      specialize (IHn st3 st2); apply IHn; try tauto.
      clear IHn H2.
      destruct H1 as [? | [? | ?]].
      * specialize (H st1 st3); tauto.
      * specialize (H st1 st3).
        assert (com_cont (ceval (CSeq c1 c2)) st1 st3).
        { simpl. tauto. }
        tauto.
      * specialize (H st1 st3).
        assert (com_cont (ceval (CSeq c1 c2)) st1 st3).
        { simpl. tauto. }
        tauto.
Qed.

Theorem hoare_asgn_sound : forall P (X : var) (E : aexp),
  partial_valid (andp (safea E) (subst_assertion P X (aeval E))) (CAss X E) P falsep falsep.
Proof.
  unfold partial_valid.
  intros.
  unfold Assertion_denote, andp, safea, subst_assertion in *.
  split; try split; try split.
  + unfold not; intros.
    simpl in *; tauto.
  + intros; simpl in *.
    destruct H, H0.
    remember (state_update st1 X (aeval E st1)) as st2'.
    assert (forall X, st2 X = st2' X).
    { intros.
      subst st2'.
      destruct (aeval E st1); try tauto.
      unfold state_update.
      destruct (Nat.eq_dec X X0).
      - subst. inversion H0. tauto.
      - specialize (H2 X0); auto. }
    assert (st2 = state_update st1 X (aeval E st1)).
    { eapply FunctionalExtensionality.functional_extensionality_dep.
      subst. tauto. }
    subst; tauto.
  + intros; simpl in *; tauto.
  + intros; simpl in *; tauto.
Qed.

End basic_rules.