Require Import Coq.Lists.List.
Require Import Shallow.Imp Shallow.ImpExt Shallow.lib.RTClosure.

Inductive com : Type :=
  | CSkip
  | CAss (X: var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  (* FIXME: change while loop to for loop below *)
  (* CFor (c1 c2 : com) (* c2 is incremental step, c1 is loop body, i.e., for(;;c2) { c1 } *) *)
  | CBreak
  | CCont
  .

Record denote: Type := {
  NormalExit: state -> state -> Prop;
  BreakExit: state -> state -> Prop;
  ContExit: state -> state -> Prop;
}.

Definition skip_sem: denote := {|
  NormalExit := BinRel.id;
  BreakExit := BinRel.empty;
  ContExit := BinRel.empty
|}.

Definition break_sem: denote := {|
  NormalExit := BinRel.empty;
  BreakExit := BinRel.id;
  ContExit := BinRel.empty
|}.

Definition cont_sem: denote := {|
  NormalExit := BinRel.empty;
  BreakExit := BinRel.empty;
  ContExit := BinRel.id
|}.

Definition asgn_sem (X: var) (E: aexp): denote := {|
  NormalExit :=
    fun st1 st2 =>
      st2 X = aeval E st1 /\
      (forall Y, X <> Y -> st1 Y = st2 Y);
  BreakExit := BinRel.empty;
  ContExit := BinRel.empty
|}.

Definition seq_sem (d1 d2: denote): denote := {|
  NormalExit := BinRel.concat (NormalExit d1) (NormalExit d2);
  BreakExit := BinRel.union
                 (BreakExit d1)
                 (BinRel.concat (NormalExit d1) (BreakExit d2));
  ContExit := BinRel.union
                (ContExit d1)
                (BinRel.concat (NormalExit d1) (ContExit d2));
|}.

Definition if_sem (b: bexp) (d1 d2: denote): denote := {|
  NormalExit := BinRel.union
                  (BinRel.concat
                     (BinRel.test_rel (beval b))
                     (NormalExit d1))
                  (BinRel.concat
                     (BinRel.test_rel (beval (BNot b)))
                     (NormalExit d2));
  BreakExit := BinRel.union
                 (BinRel.concat
                    (BinRel.test_rel (beval b))
                    (BreakExit d1))
                 (BinRel.concat
                    (BinRel.test_rel (beval (BNot b)))
                    (BreakExit d2));
  ContExit := BinRel.union
                (BinRel.concat
                   (BinRel.test_rel (beval b))
                   (ContExit d1))
                (BinRel.concat
                   (BinRel.test_rel (beval (BNot b)))
                   (ContExit d2))
|}.

Fixpoint iter_loop_body (b: bexp) (d: denote) (n: nat): state -> state -> Prop :=
  match n with
  | O    => BinRel.union
              (BinRel.test_rel (beval (! b)))
              (BinRel.concat (BinRel.test_rel (beval b)) (BreakExit d))
  | S n' => BinRel.concat
              (BinRel.test_rel (beval b))
              (BinRel.concat
                 (BinRel.union (NormalExit d) (ContExit d))
                 (iter_loop_body b d n'))
  end.

Definition loop_sem (b: bexp) (d: denote): denote := {|
  NormalExit := BinRel.omega_union (iter_loop_body b d);
  BreakExit := BinRel.empty;
  ContExit := BinRel.empty
|}.


Fixpoint ceval (c: com): denote :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
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
