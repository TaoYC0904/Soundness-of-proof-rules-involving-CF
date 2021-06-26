Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
Require Import Shallow.Imp Shallow.ImpExt Shallow.lib.RTClosure.

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CFor (c1 (* body *) c2 (* incr *) : com)
  | CBreak
  | CCont
.

Inductive exit_kind: Type :=
  | EK_Normal
  | EK_Break
  | EK_Cont.

Definition skip_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Normal.

Definition asgn_sem (X: var) (E: aexp): state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 => 
    st2 X = aeval E st1 /\
    (forall Y, X <> Y -> st1 Y = st2 Y) /\
    ek = EK_Normal.

Definition break_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Break.

Definition cont_sem: state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ ek = EK_Cont.

Definition seq_sem (d1 d2: state -> exit_kind -> state -> Prop):
  state -> exit_kind -> state -> Prop:=
  fun st1 ek st3 =>
    (exists st2, d1 st1 EK_Normal st2 /\ d2 st2 ek st3) \/
    (d1 st1 ek st3 /\ ek <> EK_Normal).

Definition test_sem (X: state -> Prop): state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    st1 = st2 /\ X st1 /\ ek = EK_Normal.

Definition union_sem (d d': state -> exit_kind -> state -> Prop) :
  state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    d st1 ek st2 \/ d' st1 ek st2.

Definition if_sem (b: bexp) (d1 d2: state -> exit_kind -> state -> Prop):
  state -> exit_kind -> state -> Prop :=
  union_sem  
    (seq_sem (test_sem (beval b)) d1)
    (seq_sem (test_sem (beval (! b))) d2).

Inductive iter_loop_body:
  (state -> exit_kind -> state -> Prop) -> 
  (state -> exit_kind -> state -> Prop) ->
  nat -> state -> state -> Prop :=
  | ILB_0: forall d1 d2 st1 st2,
      (d1 st1 EK_Break st2) \/
      (exists st3, d1 st1 EK_Normal st3 /\ d2 st3 EK_Break st2) ->
      iter_loop_body d1 d2 0 st1 st2
  | ILB_n: forall d1 d2 n st1 st2 st3 n', 
      n = S n' ->
      ((seq_sem d1 d2 st1 EK_Normal st3) \/
      (seq_sem d1 d2 st1 EK_Cont st3)) ->
      iter_loop_body d1 d2 n' st3 st2 ->
      iter_loop_body d1 d2 n st1 st2.

Definition for_sem (d1 d2: state -> exit_kind -> state -> Prop):
  state -> exit_kind -> state -> Prop :=
  fun st1 ek st2 =>
    ek = EK_Normal /\
    exists n, iter_loop_body d1 d2 n st1 st2.

Fixpoint ceval (c: com): state -> exit_kind -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CFor c1 c2 => for_sem (ceval c1) (ceval c2)
  | CBreak => break_sem
  | CCont => cont_sem
  end.

Inductive KElements: Type :=
  | KSeq (c : com)
  | KLoop1 (c1 : com) (c2 : com)
  | KLoop2 (c1 : com) (c2 : com).

Definition continuation: Type := list KElements.

Lemma nil_app_neq {A : Type} : forall (a : A) l1 l2,
  nil = l1 ++ a :: l2 -> False.
Proof.
  intros.
  pose proof eq_refl (List.length (@nil A)).
  rewrite H in H0 at 1.
  rewrite List.app_length in H0.
  simpl in H0. lia.
Qed.

(* Inductive continuation': Type :=
  | Empty_Continuation
  | KSeq' (c : com) (k0 : continuation')
  | KLoop1' (c1 : com) (c2 : com) (k0 : continuation')
  | KLoop2' (c1 : com) (c2 : com) (k0 : continuation')
. *)

(* Inductive start_with_break: com -> Prop :=
  | SWB_Break: start_with_break CBreak
  | SWB_Seq: forall c1 c2,
      start_with_break c1 ->
      start_with_break (CSeq c1 c2).

Inductive start_with_cont: com -> Prop :=
  | SWC_Cont: start_with_cont CCont
  | SWC_Seq: forall c1 c2,
      start_with_cont c1 ->
      start_with_cont (CSeq c1 c2).

Inductive start_with_loop: com -> Prop :=
  | SWL_For : forall c1 c2, start_with_loop (CFor c1 c2)
  | SWL_Seq : forall c1 c2,
      start_with_loop c1 ->
      start_with_loop (CSeq c1 c2). *)

Inductive cstep: (com * continuation * state) -> (com * continuation * state) -> Prop :=
  | CS_AssStep : forall st X a a' k,
      astep st a a' ->
      cstep (CAss X a, k, st) (CAss X a', k, st)
  | CS_Ass : forall st1 st2 X n k,
      st2 X = n ->
      (forall Y, Y <> X -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), k, st1) (CSkip, k, st2)
  
  | CS_Seq : forall st c1 c2 k,
      cstep (CSeq c1 c2, k, st) (c1, KSeq c2 :: k, st)
  | CS_SeqSkip : forall c k st,
      cstep (CSkip, (KSeq c) :: k, st) (c, k, st)
  | CS_SeqCont : forall c k st,
      cstep (CCont, (KSeq c) :: k, st) (CCont, k, st)
  | CS_SeqBreak : forall c k st,
      cstep (CBreak, (KSeq c) :: k, st) (CBreak, k, st)
  
  | CS_IfStep: forall st b b' c1 c2 k,
      bstep st b b' ->
      cstep (CIf b c1 c2, k, st) (CIf b' c1 c2, k, st)
  | CS_IfTrue: forall c1 c2 k st,
      cstep (CIf BTrue c1 c2, k, st) (c1, k, st)
  | CS_IfFalse: forall c1 c2 k st,
      cstep (CIf BFalse c1 c2, k, st) (c2, k, st)
  
  | CS_For: forall c1 c2 k st,
      cstep (CFor c1 c2, k, st) 
            (CSeq c1 CCont, (KLoop1 c1 c2) :: k, st)
  | CS_ForSkip : forall c1 c2 k st,
      cstep (CSkip, (KLoop2 c1 c2) :: k, st)
            (CSeq c1 CCont, (KLoop1 c1 c2) :: k, st)
  | CS_ForCont : forall c1 c2 k st,
      cstep (CCont, (KLoop1 c1 c2) :: k, st)
            (c2, (KLoop2 c1 c2) :: k, st)
  | CS_ForBreak1 : forall c1 c2 k st,
      cstep (CBreak, (KLoop1 c1 c2) :: k, st)
            (CSkip, k, st)
  | CS_ForBreak2 : forall c1 c2 k st,
      cstep (CBreak, (KLoop2 c1 c2) :: k, st)
            (CSkip, k, st)
.

Lemma cstep_ctx_step: forall c k st c' k' st' k'',
  cstep (c, k, st) (c', k', st') ->
  cstep (c, k ++ k'', st) (c', k' ++ k'', st').
Proof.
  inversion 1; subst; constructor; auto.
Qed.

Inductive irreducible : com -> continuation -> state -> Prop :=
| IR_ForSkip : forall c1 c2 k st,
    irreducible CSkip (KLoop1 c1 c2 :: k) st
| IR_ForCont : forall c1 c2 k st,
    irreducible CCont (KLoop2 c1 c2 :: k) st
.

Definition NHalt c k : Prop := c = CSkip /\ k = @nil KElements.

Definition BHalt c k : Prop := c = CBreak /\ k = @nil KElements.

Definition CHalt c k : Prop := c = CCont /\ k = @nil KElements.

Definition Halt c k : Prop := NHalt c k \/ BHalt c k \/ CHalt c k.

Ltac auto_halt :=
  match goal with | |- Halt ?c _ =>
    unfold Halt; unfold NHalt; unfold BHalt; unfold CHalt;
    match c with
    | CSkip => left; auto
    | CBreak => right; left; auto
    | CCont => right; right; auto
    | _ => idtac
    end
  end
.

Lemma fill_cstep_inv: forall c c' k k0 k'' st st',
  ~ Halt c k -> cstep (c, k ++ k0, st) (c', k'', st') ->
  exists k', k'' = k' ++ k0 /\ cstep (c, k, st) (c', k', st').
Proof.
  intros.
  revert k'' H0.
  induction k; intros; simpl in *.
  - inversion H0; subst;
    match goal with
    | H: ~ Halt ?c _ |- _ =>
      match c with
      | CSkip => exfalso; apply H; auto_halt
      | CBreak => exfalso; apply H; auto_halt
      | CCont => exfalso; apply H; auto_halt
      | _ => idtac
      end
    | _ => idtac
    end.
    + exists nil; split; auto; constructor; auto.
    + exists nil; split; auto; constructor; auto.
    + exists (KSeq c2 :: nil); split; auto; constructor; auto.
    + exists nil; split; auto; constructor; auto.
    + exists nil; split; auto; constructor; auto.
    + exists nil; split; auto; constructor; auto.
    + exists (KLoop1 c1 c2 :: nil); split; auto; constructor; auto.
  - inversion H0; subst;
    match goal with
    | H0: cstep (_, ?a :: ?k ++ _, _) (_, ?a :: ?k ++ _, _) |- _ =>
        exists (a :: k); split; auto; constructor; auto
    | _ => idtac
    end.
    + exists (KSeq c2 :: a :: k); split; auto; constructor.
    + exists k; split; auto; constructor.
    + exists k; split; auto; constructor.
    + exists k; split; auto; constructor.
    + exists (KLoop1 c1 c2 :: a :: k); split; auto; constructor.
    + exists (KLoop1 c1 c2 :: k); split; auto; constructor.
    + exists (KLoop2 c1 c' :: k); split; auto; constructor.
    + exists k; split; auto; constructor.
    + exists k; split; auto; constructor.
Qed.


Definition reducible c k st : Prop := (exists c' k' st', cstep (c, k, st) (c', k', st')).

Lemma reducible_ctx_step : forall c k k' st,
  reducible c k st -> reducible c (k ++ k') st.
Proof.
  intros.
  destruct H as (c1 & k1 & st1 & ?).
  exists c1, (k1 ++ k'), st1.
  apply cstep_ctx_step; auto.
Qed.


(* Definition Error c k st : Prop := ~ Halt c k /\ irreducible c k st. *)

Definition mstep : (com * continuation * state) -> (com * continuation * state) -> Prop := clos_refl_trans cstep.

Import Assertion_D.

Lemma halt_choice : forall c k st,
  Halt c k \/ reducible c k st \/ irreducible c k st.
Proof.
  intros.
  destruct c.
  - destruct k as [| c' k]; [left; auto_halt |].
    right; destruct c'.
    + left. exists c, k, st. constructor.
    + right. constructor.
    + left. exists (CSeq c1 CCont), ((KLoop1 c1 c2) :: k), st. constructor.
  - right. left.
    pose proof aexp_halt_choice a st.
    destruct H.
    + inversion H; subst.
      exists CSkip, k, (state_update st X n).
      pose proof state_update_spec st X n as [? ?].
      constructor; auto. 
    + destruct H. exists (CAss X x), k, st. constructor; auto.
  - right; left.
    exists c1, (KSeq c2 :: k), st.
    constructor.
  - right; left.
    pose proof bexp_halt_choice b st.
    destruct H.
    + inversion H; subst;
      [
        exists c1, k, st |
        exists c2, k, st
      ]; constructor.
    + destruct H. exists (CIf x c1 c2), k, st; constructor; auto.
  - right; left.
    exists (CSeq c1 CCont), ((KLoop1 c1 c2) :: k), st.
    constructor.
  - destruct k as [| c' k]; [left; auto_halt |].
    right; destruct c'.
    + left. exists CBreak, k, st. constructor.
    + left. exists CSkip, k, st. constructor.
    + left. exists CSkip, k, st. constructor.
  - destruct k as [| c' k]; [left; auto_halt |].
    right; destruct c'.
    + left. exists CCont, k, st. constructor.
    + left. exists c2, ((KLoop2 c1 c2) :: k), st. constructor.
    + right; constructor.
Qed.

Lemma halt_reducible_ex : forall c k st,
  Halt c k -> reducible c k st -> False.
Proof.
  intros.
  destruct H as [? | [? | ?]]; inversion H; subst;
  destruct H0 as (? & ? & ? & ?); inversion H0.
Qed.

Lemma halt_irreducible_ex : forall c k st,
  Halt c k -> irreducible c k st -> False.
Proof.
  intros.
  destruct H as [? | [? | ?]]; inversion H; subst;
  inversion H0.
Qed.

Lemma reducible_irreducible_ex : forall c k st,
  reducible c k st -> irreducible c k st -> False.
Proof.
  intros.
  destruct H0;
  destruct H as (? & ? & ? & ?); inversion H.
Qed.

Ltac solve_wp_0 :=
  match goal with
  | |- ~ Halt ?c ?k => unfold not; intros;
    match goal with
    | _: reducible c k ?st |- _ =>
      apply (halt_reducible_ex c k st); auto
    | _: irreducible c k ?st |- _ =>
      apply (halt_irreducible_ex c k st); auto
    end
  end.

Lemma halt_em: forall c k (st : state),
  Halt c k \/ ~ Halt c k.
Proof.
  intros.
  pose proof halt_choice c k st as [? | [? | ?]].
  - left; auto.
  - right; solve_wp_0.
  - right; solve_wp_0.
Qed.

Lemma determinism : forall c st1 st2 st3 ek1 ek2,
  ceval c st1 ek1 st2 ->
  ceval c st1 ek2 st3 ->
  (ek1 = ek2 /\ st2 = st3).
Abort.
  

(* Ltac induction_cstep H :=
  match type of H with
  | ?cstep ?a ?b =>
    revert_dependent_component a H;
    revert_dependent_component b H;
    let a0 := fresh "cst" in
    let b0 := fresh "cst" in
    let EQa := fresh "EQ" in
    let EQb := fresh "EQ" in
    remember a as a0 eqn:EQa in H;
    remember b as b0 eqn:EQb in H;
    revert EQa EQb;
    revert_component a;
    revert_component b;
    match goal with
    | |- ?Q =>
      let Pab := eval pattern a0, b0 in Q in
      match Pab with
      | ?P a0 b0 =>
        change (P a0 b0); induction H
      end
    end;
    intros ? ? ? ?;
    match goal with
    | IH: forall _ _ _ _, _ = _ -> _ = _ -> _ |- _ =>         
      specialize_until_EQ IH;
      specialize (IH eq_refl)
    | _ => idtac
    end;
    intros_until_EQ EQa; intros EQb;
        match goal with
          | |- ?Base =>
            let Base0 := fresh in
            remember Base as Base0 in |- *;
            first [ injection EQa; clear EQa; intros_and_subst Base0
                  | revert EQa; intros_and_subst Base0
                  | idtac ];
            subst Base0
          end;
          match goal with
          | |- ?Base =>
            let Base0 := fresh in
            remember Base as Base0 in |- *;
            first [ injection EQb; clear EQb; intros_and_subst Base0
                  | revert EQb; intros_and_subst Base0
                  | idtac ];
            subst Base0
          end
  end. *)

(* 2021-05-08 18:58 *)

