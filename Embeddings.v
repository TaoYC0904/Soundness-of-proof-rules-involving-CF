(* Require Import Coq.Arith.EqNat.


Definition var := nat.


Definition vars := var -> nat.
Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if beq_nat v v' then n else vs v'.

Inductive exp : Set :=
| Const : nat -> exp
| Var : var -> exp
| Plus : exp -> exp -> exp.

Fixpoint evalExp (vs : vars) (e : exp) : nat :=
  match e with
    | Const n => n
    | Var v => vs v
    | Plus e1 e2 => evalExp vs e1 + evalExp vs e2
  end.


Inductive cmd : Set :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| While : exp -> cmd -> cmd.

CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EvalAssign : forall vs v e, evalCmd vs (Assign v e) (set vs v (evalExp vs e))
| EvalSeq : forall vs1 vs2 vs3 c1 c2, evalCmd vs1 c1 vs2
  -> evalCmd vs2 c2 vs3
  -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c, evalExp vs e = 0
  -> evalCmd vs (While e c) vs
| EvalWhileTrue : forall vs1 vs2 vs3 e c, evalExp vs1 e <> 0
  -> evalCmd vs1 c vs2
  -> evalCmd vs2 (While e c) vs3
  -> evalCmd vs1 (While e c) vs3.
  
Section evalCmd_coind.
  Variable R : vars -> cmd -> vars -> Prop.

  Hypothesis AssignCase : forall vs1 vs2 v e, R vs1 (Assign v e) vs2
    -> vs2 = set vs1 v (evalExp vs1 e).

  Hypothesis SeqCase : forall vs1 vs3 c1 c2, R vs1 (Seq c1 c2) vs3
    -> exists vs2, R vs1 c1 vs2 /\ R vs2 c2 vs3.

  Hypothesis WhileCase : forall vs1 vs3 e c, R vs1 (While e c) vs3
    -> (evalExp vs1 e = 0 /\ vs3 = vs1)
    \/ exists vs2, evalExp vs1 e <> 0 /\ R vs1 c vs2 /\ R vs2 (While e c) vs3.

  Theorem evalCmd_coind : forall vs1 c vs2, R vs1 c vs2 -> evalCmd vs1 c vs2.
    cofix evalCmd_coind; intros; destruct c.
    rewrite (AssignCase _ _ _ _ H); constructor.
    destruct (SeqCase _ _ _ _ H) as [? [? ?]]; econstructor; eauto.
    destruct (WhileCase _ _ _ _ H) as [[? ?] | [? [? [? ?]]]]; subst; econstructor; eauto.
  Qed.
End evalCmd_coind. *)

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

Definition entails (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Lemma entails_refl: forall P, entails P P.
Proof.
  intros; unfold entails; auto.
Qed.

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

CoInductive coWP: com -> continuation -> Assertion -> Assertion -> Assertion -> state -> Prop :=
| coWP_Ter1: forall Q R1 R2 st,
    Assertion_denote st Q -> coWP CSkip nil Q R1 R2 st
| coWP_Ter2: forall Q R1 R2 st,
    Assertion_denote st R1 -> coWP CBreak nil Q R1 R2 st
| coWP_Ter3: forall Q R1 R2 st,
    Assertion_denote st R2 -> coWP CCont nil Q R1 R2 st
| coWP_Pre: forall c k st Q R1 R2,
    reducible c k st ->
    (forall c' k' st', 
      cstep (c, k, st) (c', k', st') -> coWP c' k' Q R1 R2 st') ->
    coWP c k Q R1 R2 st.

Section CoInductiveWP_coind.
  Variable R : com -> continuation -> Assertion -> Assertion -> Assertion -> state -> Prop.

  Hypothesis coWP_Ter1Case : forall Q R1 R2 st,
    R CSkip nil Q R1 R2 st -> Assertion_denote st Q.

  Hypothesis coWP_Ter2Case : forall Q R1 R2 st,
    R CBreak nil Q R1 R2 st -> Assertion_denote st R1.
    
  Hypothesis coWP_Ter3Case : forall Q R1 R2 st,
    R CCont nil Q R1 R2 st -> Assertion_denote st R2.

  Hypothesis coWP_PreCase : forall c k st Q R1 R2,
    R c k Q R1 R2 st ->
    reducible c k st ->
    (forall c' k' st', 
      cstep (c, k, st) (c', k', st') -> R c' k' Q R1 R2 st').

  Hypothesis coWP_IrCase : forall c k st Q R1 R2,
    R c k Q R1 R2 st ->
    irreducible c k st ->
    False.

  (* Hypothesis WP_IrCase: forall c k st Q R1 R2,
    R c k Q R1 R2 st -> ~irreducible c k st. *)

  Theorem CoInductiveWP_coind : forall c k Q R1 R2 st,
    R c k Q R1 R2 st -> coWP c k Q R1 R2 st.
    cofix CoInductiveWP_coind; intros.
    pose proof halt_choice c k st as [? | [? | ?]].
    {
      destruct H0 as [? | [? | ?]];
      destruct H0; subst; constructor; eauto.
    }
    {
      specialize (coWP_PreCase _ _ _ _ _ _ H H0).
      eapply coWP_Pre; eauto.
    }
    {
      specialize (coWP_IrCase _ _ _ _ _ _ H H0).
      inversion coWP_IrCase.
    }
  Qed.
End CoInductiveWP_coind.

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

Lemma coWP_WP_equiv: forall c k Q R1 R2 st,
  coWP c k Q R1 R2 st <-> WP c k Q R1 R2 st.
Proof.
  intros; split; intros.
  {
    intros n.
    revert c k Q R1 R2 st H.
    induction n; [constructor |]; intros.
    inversion H; subst; try (constructor; auto).
  }
  {
    intros.
    apply (CoInductiveWP_coind (fun c k Q R1 R2 st => WP c k Q R1 R2 st)); intros;
    try match goal with
      | H0: WP _ nil _ _ _ _ |- _ =>
      specialize (H0 (S O)); inversion H0; subst; auto;
      exfalso; eapply halt_reducible_ex; eauto;
      auto_halt
      end.
    {
      intros n.
      specialize (H0 (S n)).
      inversion H0; subst; auto;
      inversion H2.
    }
    {
      specialize (H0 (S O)).
      inversion H0; subst;
      try match goal with
        | H0: irreducible _ nil _ |- _ =>
        apply halt_irreducible_ex in H1; eauto; auto_halt
        end.
      eapply reducible_irreducible_ex; eauto.
    }
    auto.
  }
Qed.


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

