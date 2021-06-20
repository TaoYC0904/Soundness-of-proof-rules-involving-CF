Require Import Coq.Lists.List.
Require Import Shallow.Imp Shallow.lib.RTClosure.

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

Inductive exit_kind : Type :=
  | EK_Normal
  | EK_Break
  | EK_Cont.

Record com_denote : Type := {
  com_term : state -> exit_kind -> state -> Prop;
  com_error : state -> Prop }.

Module Denote_Com.
Import Denote_Aexp.
Import Denote_Bexp.

Definition skip_sem : com_denote := {| 
  com_term := 
    fun st1 ek st2 => st1 = st2 /\ ek = EK_Normal;
  com_error :=
    fun st => False; |}.

Definition asgn_sem (X : var) (DA : state -> option Z): com_denote := {|
  com_term :=
    fun st1 ek st2 => (Some (st2 X) = DA st1) /\
      (forall Y, Y <> X -> st2 Y = st1 Y) /\
      (ek = EK_Normal);
  com_error := 
    fun st => DA st = None; |}.

Definition seq_sem (DC1 DC2 : com_denote) : com_denote := {|
  com_term :=
    fun st1 ek st2 =>
      (exists st3, com_term DC1 st1 EK_Normal st3 /\ com_term DC2 st3 ek st2) \/
      (com_term DC1 st1 ek st2 /\ ek <> EK_Normal);
  com_error :=
    fun st =>
      (exists st', com_term DC1 st EK_Normal st' /\ com_error DC2 st') \/
      com_error DC2 st |}.

Definition if_sem (DB : bexp_denote) (DC1 DC2 : com_denote) : com_denote := {|
  com_term :=
    fun st1 ek st2 =>
      (true_set DB st1 /\ com_term DC1 st1 ek st2) \/
      (false_set DB st1 /\ com_term DC2 st1 ek st2);
  com_error :=
    fun st =>
      (error_set DB st) \/
      (true_set DB st /\ com_error DC1 st) \/
      (false_set DB st /\ com_error DC2 st) |}.

Fixpoint iter_loop_body (DC1 DC2 : com_denote) (n : nat) : com_denote :=
  match n with
  | O => {|
      com_term := 
        fun st1 ek st2 =>
          (com_term DC1 st1 EK_Break st2) \/
          (exists st3, com_term DC1 st1 EK_Normal st3 /\ com_term DC2 st3 EK_Break st2);
      com_error := 
        fun st =>
          (com_error DC1 st) \/
          (exists st', com_term DC1 st EK_Normal st' /\ com_error DC2 st') |}
  | S n' => {|
      com_term :=
        fun st1 ek st2 => exists st3,
          (com_term (seq_sem DC1 DC2) st1 EK_Normal st3 \/
           com_term (seq_sem DC1 DC2) st1 EK_Cont st3) /\
          com_term (iter_loop_body DC1 DC2 n') st3 ek st2;
      com_error :=
        fun st => exists st',
          (com_term (seq_sem DC1 DC2) st EK_Normal st' \/
           com_term (seq_sem DC1 DC2) st EK_Cont st') /\
          com_error (iter_loop_body DC1 DC2 n') st' |}
  end.

Definition for_sem (DC1 DC2 : com_denote) : com_denote := {|
  com_term :=
    fun st1 ek st2 => 
      exists n, com_term (iter_loop_body DC1 DC2 n) st1 ek st2;
  com_error :=
    fun st =>
      exists n, com_error (iter_loop_body DC1 DC2 n) st |}.

Definition break_sem : com_denote := {|
  com_term :=
    fun st1 ek st2 => st1 = st2 /\ ek = EK_Break;
  com_error :=
    fun st => False |}.

Definition cont_sem : com_denote := {|
  com_term :=
    fun st1 ek st2 => st1 = st2 /\ ek = EK_Cont;
  com_error :=
    fun st => False |}.

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





























Inductive com : Type :=
  | CSkip
  | CAss (X : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CFor (c1 c2 : com) 
  | CBreak
  | CCont.
  

Inductive exit_kind: Type :=
  | EK_Normal
  | EK_Break
  | EK_Cont.

Record com_denote : Type := {
  com_term : state -> exit_kind -> state -> Prop;
  com_error : state -> Prop }.

Definition skip_sem : com_denote :=
  {| com_term := fun st1 ek st2 => st1 = st2 /\ ek = EK_Normal;
     com_error := fun st => False |}.

Definition asgn_sem (X : var) (DA : state -> option Z): com_denote :=
  {| com_term := 
      fun st1 ek st2 => Some (st2 X) = DA st1 /\
        (forall Y, X <> Y -> st1 Y = st2 Y) /\ ek = EK_Normal;
     com_error := 
      fun st => None = DA st |}.

  Definition seq_sem (DC1 DC2 : com_denote) : com_denote :=
  {| com_term := 
      fun st1 ek st2 => 
        (exists st3, com_term DC1 st1 EK_Normal st3 /\ com_term DC2 st3 ek st2) \/
        (com_term DC1 st1 ek st2 /\ ek <> EK_Normal);
     com_error :=
      fun st =>
        (com_error DC1 st) \/
        (exists st', com_term DC1 st EK_Normal st' /\ com_error DC2 st') |}.

Check true_set DB.

Definition if_sem (DB : state -> option Prop) (DC1 DC2 : com_denote) : com_denote :=
  {| com_term :=
      fun st1 ek st2 =>
        () /\ (com_term DC1 st1 ek st2)) \/
        (~(Some (DB st1)) /\ (com_term DC2 st1 ek st2));
     com_error :=
      fun st =>
        (None DB st) \/
        ((Some (DB st)) /\ (com_error DC1 st)) \/
        ((Some (DB st)) /\ (com_error DC2 st)) |}.



Definition break_sem : com_denote :=
  {| com_term := fun st1 ek st2 => 

















