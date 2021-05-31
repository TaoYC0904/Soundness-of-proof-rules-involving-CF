Require Import PL.Imp.
Require Import PL.ImpCF.
Import Assertion_S.

Print state. 
(* state = nat -> Z : Type *)

Print com. 
(* Inductive com : Type :=
    CSkip : com
  | CAss : var -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CBreak : com
  | CCont : com *)
  
Print Assertion.
(* Inductive Assertion : Type :=
    DLe : term -> term -> Assertion
  | DLt : term -> term -> Assertion
  | DEq : term -> term -> Assertion
  | DInj : bexp -> Assertion
  | DProp : Prop -> Assertion
  | DOr : Assertion -> Assertion -> Assertion
  | DAnd : Assertion -> Assertion -> Assertion
  | DNot : Assertion -> Assertion
  | DExists : (Z -> Assertion) -> Assertion
  | DForall : (Z -> Assertion) -> Assertion *)
  
Print Assertion_denote.
(* Assertion_denote = 
fix Assertion_denote (st : state) (d : Assertion) {struct d} : Prop :=
  match d with
  | (t1 <= t2)%assert => term_denote st t1 <= term_denote st t2
  | (t1 < t2)%assert => term_denote st t1 < term_denote st t2
  | (t1 = t2)%assert => term_denote st t1 = term_denote st t2
  | ({[b]})%assert => bexp_denote st b
  | DProp P => P
  | (d1 OR d2)%assert => Assertion_denote st d1 \/ Assertion_denote st d2
  | (d1 AND d2)%assert => Assertion_denote st d1 /\ Assertion_denote st d2
  | (NOT d0)%assert => ~ Assertion_denote st d0
  | DExists d0 => exists k : Z, Assertion_denote st (d0 k)
  | DForall d0 => forall k : Z, Assertion_denote st (d0 k)
  end
     : state -> Assertion -> Prop *)
     
Print ceval.
(* ceval = 
fix ceval (c : com) : denote :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c0 => loop_sem b (ceval c0)
  | CBreak => break_sem
  | CCont => cont_sem
  end
     : com -> denote *)

Print denote.
(* Record denote : Type := Build_denote
  { NormalExit : state -> state -> Prop;
    BreakExit : state -> state -> Prop;
    ContExit : state -> state -> Prop } *)

Definition partial_valid_CF (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  forall (st1 st2 : state) (d : denote),
    Assertion_denote st1 P ->
    d = ceval c ->
    ((NormalExit d st1 st2) -> (Assertion_denote st2 Q)) /\
    ((BreakExit d st1 st2) -> (Assertion_denote st2 R1)) /\
    ((ContExit d st1 st2) -> (Assertion_denote st2 R2)).

Definition total_valid_CF (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  (forall (st1 : state),
    Assertion_denote st1 P ->
    exists (d : denote), d = ceval c ->
    exists (st2 : state), 
      (NormalExit d st1 st2) \/ (BreakExit d st1 st2) \/ (ContExit d st1 st2)) /\
  (forall (st1 st2 : state) (d : denote),
    Assertion_denote st1 P ->
    d = ceval c ->
    ((NormalExit d st1 st2) -> (Assertion_denote st2 Q)) /\
    ((BreakExit d st1 st2) -> (Assertion_denote st2 R1)) /\
    ((ContExit d st1 st2) -> (Assertion_denote st2 R2))).





(* definition small step semantics, weakest precondition, validity *)
