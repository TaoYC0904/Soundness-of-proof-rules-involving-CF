Require Import Coq.Lists.List.
Require Import Shallow.Imp Shallow.ImpExt Shallow.lib.RTClosure.

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CFor (c1 c2 : com)
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
    forall Y, X <> Y -> st1 Y = st2 Y /\
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
  | ILB_0: forall d1 d2 n st1 st2,
      n = Z.to_nat 0 ->
      (d1 st1 EK_Break st2) \/
      (exists st3, d1 st1 EK_Normal st3 /\ d2 st3 EK_Break st2) ->
      iter_loop_body d1 d2 n st1 st2
  | ILB_n: forall d1 d2 n st1 st2 st3 n', 
      n = S n' ->
      seq_sem d1 d2 st1 EK_Normal st3 ->
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

Definition cstack: Type := list (bexp * com * com).

Inductive start_with_break: com -> Prop :=
| SWB_Break: start_with_break CBreak
| SWB_Seq: forall c1 c2,
             start_with_break c1 ->
             start_with_break (CSeq c1 c2).

Inductive start_with_cont: com -> Prop :=
| SWC_Cont: start_with_cont CCont
| SWC_Seq: forall c1 c2,
             start_with_cont c1 ->
             start_with_cont (CSeq c1 c2).

Inductive start_with_loop: com -> bexp -> com -> com -> Prop :=
| SWL_While: forall b c, start_with_loop (CWhile b c) b c CSkip
| SWL_Seq: forall c1 b c11 c12 c2,
             start_with_loop c1 b c11 c12 ->
             start_with_loop (CSeq c1 c2) b c11 (CSeq c12 c2).

Inductive cstep : (com * cstack * state) -> (com * cstack * state) -> Prop :=
  | CS_AssStep : forall st s X a a',
      astep st a a' ->
      cstep
        (CAss X a, s, st)
        (CAss X a', s, st)
  | CS_Ass : forall st1 st2 s X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep
        (CAss X (ANum n), s, st1)
        (CSkip, s, st2)
  | CS_SeqStep : forall st s c1 c1' st' c2,
      cstep
        (c1, s, st)
        (c1', s, st') ->
      cstep
        (CSeq c1 c2, s, st)
        (CSeq c1' c2, s, st')
  | CS_Seq : forall st s c2,
      cstep
        (CSeq CSkip c2, s, st)
        (c2, s, st)
  | CS_IfStep : forall st s b b' c1 c2,
      bstep st b b' ->
      cstep
        (CIf b c1 c2, s, st)
        (CIf b' c1 c2, s, st)
  | CS_IfTrue : forall st s c1 c2,
      cstep
        (CIf BTrue c1 c2, s, st)
        (c1, s, st)
  | CS_IfFalse : forall st s c1 c2,
      cstep
        (CIf BFalse c1 c2, s, st)
        (c2, s, st)
  | CS_While : forall st s c b c1 c2,
      start_with_loop c b c1 c2 ->
      cstep
        (c, s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
  | CS_Skip : forall st s b c1 c2,
      cstep
        (CSkip, (b, c1, c2) :: s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
  | CS_Break : forall st s b c1 c2 c,
      start_with_break c ->
      cstep
        (c, (b, c1, c2) :: s, st)
        (c2, s, st)
  | CS_Cont : forall st s b c1 c2 c,
      start_with_cont c ->
      cstep
        (c, (b, c1, c2) :: s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
.

Ltac induction_cstep H :=
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
  end.

(* 2021-05-08 18:58 *)
