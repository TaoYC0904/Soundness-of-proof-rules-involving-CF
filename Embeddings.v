Require Import Coq.Lists.List.
Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.lib.RTClosure.
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

Module SmallS.

Inductive WP_n : nat -> com -> continuation -> Assertion -> Assertion -> Assertion -> state -> Prop :=
  | WP_0 : forall c k Q R1 R2 st, WP_n 0 c k Q R1 R2 st
  (* | WP_0 : forall c k Q R1 R2 st, ~ Halt c k -> WP_n 0 c k Q R1 R2 st *)
  | WP_Ter1: forall n Q R1 R2 st,
      Assertion_denote st Q -> WP_n n CSkip nil Q R1 R2 st
  | WP_Ter2: forall n Q R1 R2 st,
      Assertion_denote st R1 -> WP_n n CBreak nil Q R1 R2 st 
  | WP_Ter3: forall n Q R1 R2 st,
      Assertion_denote st R2 -> WP_n n CCont nil Q R1 R2 st 
  | WP_Pre: forall n c k st Q R1 R2,
      reducible c k st ->
      (* (exists c' k' st', cstep (c, k, st) (c', k', st')) -> *)
      (forall c' k' st', 
        cstep (c, k, st) (c', k', st') -> WP_n n c' k' Q R1 R2 st') ->
      WP_n (S n) c k Q R1 R2 st.

Definition WP c k Q R1 R2 st : Prop :=
  forall n, WP_n n c k Q R1 R2 st.

Ltac iLob := intros n; induction n; [constructor |].

Definition valid_smallstep (P : Assertion) (c : com) (Q R1 R2 : Assertion) : Prop :=
  forall st, Assertion_denote st P -> WP c nil Q R1 R2 st.

End SmallS.

Module Cont.

Inductive safe_n : nat -> com -> continuation -> state -> Prop :=
  | safe_0: forall c k st, safe_n 0 c k st
  | safe_Ter1: forall n st, safe_n n CSkip nil st 
  | safe_Ter2: forall n st, safe_n n CBreak nil st
  | safe_Ter3: forall n st, safe_n n CCont nil st    
  | safe_Pre: forall n c k st,
      reducible c k st ->
      (forall c' k' st', 
        cstep (c, k, st) (c', k', st') -> safe_n n c' k' st') ->
      safe_n (S n) c k st.

Definition safe c k st : Prop :=
  forall n, safe_n n c k st.

Definition guard P c k : Prop :=
  forall st, Assertion_denote st P -> safe c k st.

Lemma all_guard_nil : forall P, guard P CSkip nil.
Proof.
  intros.
  intros st ? n.
  apply safe_Ter1.
Qed.

Lemma false_guard_all : forall c k, guard (fun _ => False) c k.
Proof.
  intros.
  intros st ?.
  inversion H; subst.
Qed.

Definition valid_continuation P c Q R1 R2 : Prop := forall k,
    guard Q CSkip k ->
    guard R1 CBreak k ->
    guard R2 CCont k ->
    guard P c k.

End Cont.

Fixpoint nocontinue_c (c : com) : Prop :=
  match c with
  | CSkip         => True
  | CAss _ _      => True
  | CSeq c1 c2    => (nocontinue_c c1) /\ (nocontinue_c c2)
  | CIf b c1 c2   => (nocontinue_c c1) /\ (nocontinue_c c2)
  | CFor c1 c2    => True
  | CBreak        => True 
  | CCont         => False
  | CFor1 _ _ _ | CFor2 _ _ _ => True
  end.

Fixpoint hasloop_k k : Prop :=
  match k with
  | nil => False
  | KLoop1 _ _ :: _ | KLoop2 _ _ :: _ => True
  | KSeq _ :: k => hasloop_k k
  end.

Fixpoint nocontinue_k (k : continuation) : Prop :=
  match k with 
  | KSeq c :: k' => (nocontinue_c c \/ hasloop_k k') /\ (nocontinue_k k')
  | KLoop1 c1 c2 :: k' => (nocontinue_k k')
  | KLoop2 c1 c2 :: k' => (nocontinue_k k')
  | nil => True
  end.

Definition nocontinue c k : Prop := nocontinue_k (KSeq c :: k).

Lemma cstep_preserve_nocontinue : forall c1 c2 k1 k2 st1 st2,
  cstep (c1, k1, st1) (c2, k2, st2) ->
  nocontinue c1 k1 ->
  nocontinue c2 k2.
Proof.
  intros.
  inversion H; subst; auto;
  unfold nocontinue in *; simpl in *; tauto.
Qed.

Lemma mstep_preserve_nocontinue : forall c1 c2 k1 k2 st1 st2,
  mstep (c1, k1, st1) (c2, k2, st2) ->
  nocontinue c1 k1 ->
  nocontinue c2 k2.
Proof.
  intros.
  remember (c1, k1, st1) as prog1.
  remember (c2, k2, st2) as prog2.
  revert c1 k1 st1 Heqprog1 H0.
  unfold mstep in H.
  rewrite rt_rt1n_iff in H.
  induction H; intros; subst.
  - inversion Heqprog1; subst; auto.
  - destruct y as [[c1' k1'] st1'].
    apply (IHclos_refl_trans_1n eq_refl _ _ _ eq_refl).
    apply (cstep_preserve_nocontinue _ _ _ _ _ _ H H1).
Qed.

Definition simulation (sim : (com * continuation) -> (com * continuation) -> Prop) : Prop := forall c1 k1 c2 k2,
  sim (c1, k1) (c2, k2) ->  (* c2 simulates c1 *)
  (Halt c1 k1 -> (c1, k1) = (c2, k2)) /\
  (forall st, irreducible c1 k1 st -> irreducible c2 k2 st) /\
  (forall c1' k1' st st',
    cstep (c1, k1, st) (c1', k1', st') ->
    exists c2' k2',
    mstep (c2, k2, st) (c2', k2', st') /\ sim (c1', k1') (c2', k2')).

