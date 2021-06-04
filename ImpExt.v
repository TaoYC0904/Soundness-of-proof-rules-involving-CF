Require Import Shallow.Imp.
Require Import Shallow.lib.RTClosure.

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
        revert a0 b0 H;
        refine (cstep_ind P _ _ _ _ _ _ _ _)
      end
    end;
    
    [ intros ? ? ? ? ?
    | intros ? ? ? ? ? ?
    | let IH := fresh "IHcstep" in
      intros ? ? ? ? ? ? IH;
      specialize_until_EQ IH;
      specialize (IH eq_refl)
    | intros ? ?
    | intros ? ? ? ? ? ?
    | intros ? ? ?
    | intros ? ? ?
    | intros ? ? ?];
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

Lemma zero_plus_equiv: forall (a: aexp),
  aexp_equiv (0 + a) a.
Proof.
  intros.
  unfold aexp_equiv.
  simpl.
  unfold Func.equiv, Func.add, constant_func.
  intros.
  simpl.
  lia.
Qed.

Lemma plus_zero_equiv: forall (a: aexp),
  aexp_equiv (a + 0) a.
Proof.
  intros.
  unfold aexp_equiv.
  simpl.
  unfold Func.equiv, Func.add, constant_func.
  intros.
  simpl.
  lia.
Qed.

Lemma minus_zero_equiv: forall (a: aexp),
  aexp_equiv (a - 0) a.
Proof.
  intros.
  unfold aexp_equiv.
  simpl.
  unfold Func.equiv, Func.sub, constant_func.
  intros.
  simpl.
  lia.
Qed.

Lemma zero_mult_equiv: forall (a: aexp),
  aexp_equiv (0 * a) 0.
Proof.
  intros.
  unfold aexp_equiv.
  simpl.
  unfold Func.equiv, Func.mul, constant_func.
  intros.
  simpl.
  lia.
Qed.

Lemma mult_zero_equiv: forall (a: aexp),
  aexp_equiv (a * 0) 0.
Proof.
  intros.
  unfold aexp_equiv.
  simpl.
  unfold Func.equiv, Func.mul, constant_func.
  intros.
  simpl.
  lia.
Qed.

Lemma one_mult_equiv: forall (a: aexp),
  aexp_equiv (1 * a) a.
Proof.
  intros.
  unfold aexp_equiv.
  simpl.
  unfold Func.equiv, Func.mul, constant_func.
  intros.
  lia.
Qed.

Lemma mult_one_equiv: forall (a: aexp),
  aexp_equiv (a * 1) a.
Proof.
  intros.
  unfold aexp_equiv.
  simpl.
  unfold Func.equiv, Func.mul, constant_func.
  intros.
  lia.
Qed.

Fixpoint remove_skip (c: com): com :=
  match c with
  | CSkip =>
      CSkip
  | CAss X E =>
      CAss X E
  | CSeq c1 c2 =>
      match remove_skip c1 with
      | CSkip => remove_skip c2
      | _ => CSeq (remove_skip c1) (remove_skip c2)
      end
  | CIf b c1 c2 =>
      CIf b (remove_skip c1) (remove_skip c2)
  | CWhile b c1 =>
      CWhile b (remove_skip c1)
  end.

Lemma remove_skip_skip_step: forall c1 c2 st1 st2,
  remove_skip c1 = CSkip ->
  cstep (c1, st1) (c2, st2) ->
  st1 = st2 /\ remove_skip c2 = CSkip.
Proof.
  intros.
  revert st1 c2 st2 H0.
  induction c1; try solve [inversion H]; intros.
  + inversion H0.
  + simpl in H.
    destruct (remove_skip c1_1) eqn:?H; try solve [inversion H].
    specialize (IHc1_1 eq_refl).
    inversion H0; subst.
    - specialize (IHc1_1 _ _ _ H3).
      destruct IHc1_1.
      split; [auto | simpl].
      rewrite H4, H.
      reflexivity.
    - auto.
Qed.

(* 2021-03-29 09:49 *)
