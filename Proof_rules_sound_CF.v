Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Import Assertion_S.

Print state. 
Print com. 
Print Assertion.
Print Assertion_denote.    
Print ceval.

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

Inductive WP : com -> continuation -> Assertion -> Assertion -> Assertion
  -> state -> Prop :=
  | WP_Ter1: forall Q R1 R2 st,
      Assertion_denote st Q -> WP CSkip nil Q R1 R2 st
  | WP_Ter2: forall Q R1 R2 st,
      Assertion_denote st R1 -> WP CBreak nil Q R1 R2 st 
  | WP_Ter3: forall Q R1 R2 st,
      Assertion_denote st R2 -> WP CCont nil Q R1 R2 st 
  | WP_Pre: forall c k st Q R1 R2,
      (exists c' k' st', cstep (c, k, st) (c', k', st')) ->
      (forall c' k' st', 
        cstep (c, k, st) (c', k', st') -> WP c' k' Q R1 R2 st') ->
      WP c k Q R1 R2 st.      

Definition valid_smallstep (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  forall st, Assertion_denote st P -> WP c nil Q R1 R2 st.
  
Inductive safe : com -> continuation -> state -> Prop :=
  | safe_Ter1: forall st, safe CSkip nil st 
  | safe_Ter2: forall st, safe CBreak nil st
  | safe_Ter3: forall st, safe CCont nil st    
  | safe_Pre: forall c k st c' k' st',
      cstep (c, k, st) (c', k', st') ->
      safe c' k' st' ->
      safe c k st.

(* definition small step semantics, weakest precondition, validity *)
