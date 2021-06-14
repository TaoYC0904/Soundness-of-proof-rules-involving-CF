Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
(* Import Assertion_S. *)

(* Print state. 
Print com. 
Print Assertion.
Print Assertion_denote.    
Print ceval. *)

Module Assertion_Shallow.

Definition Assertion : Type := state -> Prop.

Definition Assertion_denote (st : state) (P : Assertion) : Prop := P st.

End Assertion_Shallow.

Import Assertion_Shallow.

Module BigS.

Definition partial_valid_bigstep (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  forall st1 st2 ek,
    Assertion_denote st1 P ->
    ceval c st1 ek st2 ->
    ((ek = EK_Normal) -> (Assertion_denote st2 Q)) /\
    ((ek = EK_Break)  -> (Assertion_denote st2 R1)) /\
    ((ek = EK_Cont)   -> (Assertion_denote st2 R2)).

Definition total_valid_bigstep (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  (forall st1, Assertion_denote st1 P -> (exists ek st2, ceval c st1 ek st2)) /\
  partial_valid_bigstep P c Q R1 R2.

End BigS.


Definition reducible c k st : Prop := (exists c' k' st', cstep (c, k, st) (c', k', st')).

Module SmallS.

Inductive WP : com -> continuation -> Assertion -> Assertion -> Assertion
  -> state -> Prop :=
  | WP_Ter1: forall Q R1 R2 st,
      Assertion_denote st Q -> WP CSkip nil Q R1 R2 st
  | WP_Ter2: forall Q R1 R2 st,
      Assertion_denote st R1 -> WP CBreak nil Q R1 R2 st 
  | WP_Ter3: forall Q R1 R2 st,
      Assertion_denote st R2 -> WP CCont nil Q R1 R2 st 
  | WP_Pre: forall c k st Q R1 R2,
      reducible c k st ->
      (* (exists c' k' st', cstep (c, k, st) (c', k', st')) -> *)
      (forall c' k' st', 
        cstep (c, k, st) (c', k', st') -> WP c' k' Q R1 R2 st') ->
      WP c k Q R1 R2 st.      

Definition valid_smallstep (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  forall st, Assertion_denote st P -> WP c nil Q R1 R2 st.

End SmallS.

Module Cont.

Inductive safe : com -> continuation -> state -> Prop :=
  | safe_Ter1: forall st, safe CSkip nil st 
  | safe_Ter2: forall st, safe CBreak nil st
  | safe_Ter3: forall st, safe CCont nil st    
  | safe_Pre: forall c k st c' k' st',
      cstep (c, k, st) (c', k', st') ->
      safe c' k' st' ->
      safe c k st.

Definition guard (P : Assertion) (k : continuation) : Prop :=
  forall st, Assertion_denote st P -> safe CSkip k st.

(* Lemma all_guard_nil : forall P, guard P nil.
Proof.
  intros.
  unfold guard.
  intros.
  apply safe_Ter1.
Qed.

Lemma false_guard_all : forall k, guard (DInj BFalse) k.
Proof.
  intros.
  unfold guard.
  intros.
  inversion H; subst.
Qed.  *)

Open Scope list_scope.

Definition valid_continuaion (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  forall k, (guard Q k /\ guard R1 ((KSeq CBreak) :: k) /\ guard R2 ((KSeq CCont) :: k)) ->
    guard P ((KSeq c) :: k).

End Cont.

Fixpoint nocontinue (c : com) : Prop :=
  match c with
  | CSkip         => True
  | CAss _ _      => True
  | CSeq c1 c2    => (nocontinue c1) /\ (nocontinue c2)
  | CIf b c1 c2   => (nocontinue c1) /\ (nocontinue c2)
  | CFor c1 c2    => (nocontinue c1) /\ (nocontinue c2)
  | CBreak        => True 
  | CCont         => False
  end.


Definition simulation (sim : (com * continuation) -> (com * continuation) -> Prop) : Prop := 
  forall c1 k1 c2 k2,
    sim (c1, k1) (c2, k2) ->
  (* (forall st, reducible c1 k1 st -> reducible c2 k2 st) /\ *)
  ((c1, k1) = (CSkip, nil) -> (c2, k2) = (CSkip, nil)) /\
  ((c1, k1) = (CBreak, nil) -> (c2, k2) = (CBreak, nil)) /\
  ((c1, k1) = (CCont, nil) -> (c2, k2) = (CCont, nil)) /\
  (forall c1' k1' st st',
    cstep (c1, k1, st) (c1', k1', st') ->
    exists c2' k2',
    cstep (c2, k2, st) (c2', k2', st') /\ sim (c1', k1') (c2', k2')).

