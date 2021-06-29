Require Import Coq.Lists.List.
Require Import Shallow.Imp.
Require Import Shallow.ImpCF.
Require Import Shallow.Embeddings.
Require Import Shallow.lib.RTClosure.

Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Operators_Properties.
(* Require Import Coq.Arith.PeanoNat. *)

Import Assertion_S.

Import SmallS.
Import Cont.

Open Scope nat_scope.

Lemma safe_mstep_pre: forall c k st c' k' st',
  safe c k st ->
  mstep (c, k, st) (c', k', st') ->
  safe c' k' st'.
Proof.
  intros.
  remember (c, k, st) as prog.
  remember (c', k', st') as prog'.
  revert c k st Heqprog H.
  unfold mstep in H0.
  apply rt_rt1n_iff in H0.
  induction H0; intros; subst.
  - inversion Heqprog; subst; auto.
  (* - intros n.
    specialize (H0 (S n)).
    inversion H0; subst;
    [ inversion H |
      inversion H |
      inversion H |].
    apply (H3 _ _ _ H). *)
  - destruct y as [[c'' k''] st''].
    apply (IHclos_refl_trans_1n eq_refl _ _ _ eq_refl).
    intros n.
    specialize (H1 (S n)).
    inversion H1; subst;
    [ inversion H |
      inversion H |
      inversion H |].
    apply (H4 _ _ _ H).
Qed.

(* guard = triple + dead *)

Definition simulation (sim : (com * continuation) -> (com * continuation) -> Prop) : Prop := forall c1 k1 c2 k2,
sim (c1, k1) (c2, k2) ->  (* c2 simulates c1 *)
(Halt c1 k1 -> (c1, k1) = (c2, k2) \/
               forall st, exists c' k', cstep (c2, k2, st) (c', k', st) /\
                                        sim (c1, k1) (c', k')) /\
(forall st, irreducible c1 k1 st -> irreducible c2 k2 st) /\
(forall c1' k1' st st',
  cstep (c1, k1, st) (c1', k1', st') ->
  exists c2' k2',
  mstep (c2, k2, st) (c2', k2', st') /\ sim (c1', k1') (c2', k2')).

Lemma safe_sim_term : forall n c1 c2 k1 k2 st sim,
  Halt c2 k2 \/ irreducible c2 k2 st ->
  simulation sim ->
  sim (c2, k2) (c1, k1) ->
  safe_n n c1 k1 st ->
  safe_n n c2 k2 st.
Proof.
  intros.

  pose proof halt_choice c2 k2 st as [? | [? | ?]].
  - clear H.
    pose proof (H0 _ _ _ _ H1) as [? _].
    specialize (H H3).
    destruct H3 as [? | [? | ?]]; destruct H3; subst; constructor.
  - exfalso. destruct H;
    [ apply (halt_reducible_ex c2 k2 st); auto |
      apply (reducible_irreducible_ex c2 k2 st); auto].
  - pose proof H0 _ _ _ _ H1 as [_ [? _]].
    specialize (H4 _ H3).
    inversion H2; [constructor; solve_wp_0 | | | |]; exfalso;
    [ apply (halt_irreducible_ex c1 k1 st); auto; subst; auto_halt |
      apply (halt_irreducible_ex c1 k1 st); auto; subst; auto_halt |
      apply (halt_irreducible_ex c1 k1 st); auto; subst; auto_halt |]; subst.
    apply (reducible_irreducible_ex c1 k1 st); auto.
Qed.

Lemma safe_sim : forall c1 c2 k1 k2 st sim,
  simulation sim ->
  sim (c2, k2) (c1, k1) ->
  safe c1 k1 st ->
  safe c2 k2 st.
Proof.
  intros.

  pose proof halt_choice c2 k2 st.
  destruct H2 as [? | [? | ?]].
  - intros n; specialize (H1 n).
    assert (Halt c2 k2 \/ irreducible c2 k2 st); [auto |].
    apply (safe_sim_term _ _ _ _ _ _ _ H3 H H0 H1).
  - intros n.
    revert c1 k1 c2 k2 st H0 H1 H2.
    induction n; intros; [constructor |].

    pose proof H _ _ _ _ H0 as [_ [_ ?]].
    apply safe_Pre; auto; intros.
    apply H3 in H4.
    destruct H4 as (c1' & k1' & ? & ?).

    pose proof safe_mstep_pre _ _ _ _ _ _ H1 H4.
    pose proof halt_choice c' k' st' as [? | [? | ?]].
    + specialize (H6 n).
      assert (Halt c' k' \/ irreducible c' k' st'); [auto |].
      apply (safe_sim_term _ _ _ _ _ _ _ H8 H H5 H6).
    + apply (IHn _ _ _ _ _ H5 H6 H7).
    + specialize (H6 n).
      assert (Halt c' k' \/ irreducible c' k' st'); [auto |].
      apply (safe_sim_term _ _ _ _ _ _ _ H8 H H5 H6).
  - intros n; specialize (H1 n).
    assert (Halt c2 k2 \/ irreducible c2 k2 st); [auto |].
    apply (safe_sim_term _ _ _ _ _ _ _ H3 H H0 H1).
Qed.

Lemma guard_sim : forall c1 c2 k1 k2 P sim,
  simulation sim ->
  sim (c2, k2) (c1, k1) ->
  guard P c1 k1 ->
  guard P c2 k2.
Proof.
  intros.
  intros st ?.
  specialize (H1 _ H2).
  clear H2.
  apply (safe_sim _ _ _ _ _ _ H H0 H1).
Qed.

Definition dead : com := CFor CSkip CSkip.

Lemma dead_reducible : forall k st, reducible dead k st.
Proof.
  intros.
  unfold dead.
  exists (CSeq CSkip CCont), (KLoop1 CSkip CSkip :: k), st.
  constructor.
Qed.

Lemma dead_safe : forall k st, safe dead k st.
Proof.
  intros.
  intros n.

  destruct n; [constructor |].
  apply safe_Pre; [apply dead_reducible | intros].
  inversion_clear H.

  assert (n <= n); [lia |].
  remember n as m.
  rewrite Heqm in H at 1.
  rewrite Heqm.
  clear Heqm.
  revert n k st' H.

  induction m; intros.
  - inversion H; subst. constructor.
  - destruct n; [constructor |].
    apply safe_Pre;
    [exists CSkip, (KSeq CCont :: KLoop1 CSkip CSkip :: k), st'; constructor | intros].
    inversion_clear H0.
    destruct n; [constructor |].
    apply safe_Pre;
    [exists CCont, (KLoop1 CSkip CSkip :: k), st'0; constructor | intros].
    inversion_clear H0.
    destruct n; [constructor |].
    apply safe_Pre;
    [exists CSkip, (KLoop2 CSkip CSkip :: k), st'1; constructor | intros].
    inversion_clear H0.
    destruct n; [constructor |].
    apply safe_Pre;
    [exists (CSeq CSkip CCont), (KLoop1 CSkip CSkip :: k), st'2; constructor | intros].
    inversion_clear H0.
    apply IHm; omega.
Qed.

Definition start_with_KLoop2 k : Prop :=
  match k with
  | KLoop2 _ _ :: k => True
  | _ => False
  end.

Inductive seq_inv_sim : (com * continuation) -> (com * continuation) -> Prop:=
| SI_sim_id : forall c k, seq_inv_sim (c, k) (c, k)
| SI_sim_bd : forall k, seq_inv_sim (CBreak, KSeq dead :: k) (CBreak, k)
| SI_sim_cd : forall k, (*~ start_with_KLoop2 k ->*) seq_inv_sim (CCont, KSeq dead :: k) (CCont, k)
.

Lemma seq_inv_sim_is_simulation : simulation seq_inv_sim.
Proof.
  unfold simulation; intros.
  split; [| split]; intros.
  {
    destruct H0 as [? | [? | ?]]; inversion H0; subst;
    inversion H; subst; auto; right; intros.
    (* - exists CBreak, nil; split; constructor.
    - exists CCont, nil; split; constructor. *)
  }
  {
    inversion H0; subst; inversion H; subst; try constructor.
    (* exfalso; apply H3; simpl; auto. *)
  }
  {
    inversion H; subst.
    - exists c1', k1'; split; constructor; auto.
    - inversion H0; subst.
      exists CBreak, k1'; split; [apply rt_refl | constructor].
      (* apply (rt_trans _ _ (CBreak, k1, st)); constructor; auto; constructor. *)
    - inversion H0; subst.
      exists CCont, k1'; split; [apply rt_refl | constructor].
      (* apply (rt_trans _ _ (CCont, k1, st)); constructor; auto; constructor. *)
  }
Qed.

Inductive seq_sim : (com * continuation) -> (com * continuation) -> Prop :=
| S_sim_id : forall c k, seq_sim (c, k) (c, k)
| S_sim_seq : forall c1 c2 k, seq_sim (c1, KSeq c2 :: k) (CSeq c1 c2, k)
.

Lemma seq_sim_is_simulation : simulation seq_sim.
Proof.
  unfold simulation; intros.
  split; [| split]; intros.
  {
    destruct H0 as [? | [? | ?]]; inversion H0; subst;
    inversion H; subst; auto.
  }
  {
    inversion H0; subst; inversion H; subst; try constructor.
  }
  {
    inversion H; subst.
    - exists c1', k1'; split; constructor; auto.
    - exists c1', k1'; split; [eapply rt_trans | constructor]; constructor;
      [apply CS_Seq | auto].
  }
Qed.

(* Definition WP c Q R1 R2 (st : state) : Prop :=
forall k, guard Q CSkip k ->
        guard R1 CBreak k ->
        guard R2 CCont k -> safe c k st. *)

Theorem seq_inv_valid_continuation : forall P c1 c2 Q R1 R2,
valid_continuation P (CSeq c1 c2) Q R1 R2 ->
  (exists Q', (valid_continuation P c1 Q' R1 R2) /\
    (valid_continuation Q' c2 Q R1 R2)).
Proof.
  intros.

  (* strongest post *)
  exists (fun st => exists st0, Assertion_Shallow.Assertion_denote st0 P /\ mstep (c1, nil, st0) (CSkip, nil, st)).
  split.
  {
    unfold valid_continuation.
    intros.
    pose proof guard_sim _ _ _ _ _ _ seq_inv_sim_is_simulation (SI_sim_bd k) H1.
    pose proof guard_sim _ _ _ _ _ _ seq_inv_sim_is_simulation (SI_sim_cd k) H2.
    assert (guard Q CSkip (KSeq dead :: k)).
    {
      clear. intros st ? n.
      destruct n; [constructor |].
      apply safe_Pre.
      + exists dead, k, st; constructor.
      + intros. inversion H0; subst.
        apply dead_safe.
    }
    specialize (H _ H5 H3 H4).

    revert H H0; clear.
    unfold guard, Assertion_Shallow.Assertion_denote; intros.
    
    specialize (H _ H1).
    assert (forall st0, mstep (c1, nil, st) (CSkip, nil, st0) -> safe CSkip k st0); [| clear H0 H1].
    { intros. apply H0. exists st; split; auto. }

    apply (safe_sim _ _ _ _ _ _ seq_sim_is_simulation (S_sim_seq _ _ _)) in H.
    replace k with (nil ++ k); auto.
    replace (KSeq c2 :: KSeq dead :: k) with (nil ++ KSeq c2 :: KSeq dead :: k) in H; auto.
    remember (@nil KElements) as k'.
    rewrite Heqk' in *. rewrite <- Heqk'. rewrite <- Heqk' in H.
    replace (c1, nil, st) with (c1, k', st) in H2; [| subst; auto].
    clear Heqk'.

    intros n.
    revert dependent st.
    (* revert c1 k. *)
    revert c1 k'.
    induction n; [constructor | intros].

    pose proof halt_choice c1 k' st as [? | [? | ?]];
    [destruct H0 as [? | [? | ?]]; destruct H0; subst | |
      inversion H0; subst].
    - apply H2; apply rt_refl.
    - (* by H after 2 step *)
      simpl in *.
      specialize (H (S (S (S n)))).
      inversion H; subst; specialize (H3 _ _ _ (CS_SeqBreak _ _ _)).
      inversion H3; subst; specialize (H5 _ _ _ (CS_SeqBreak _ _ _)).
      auto.
    - (* by H after 2 step *)
      simpl in *.
      specialize (H (S (S (S n)))).
      inversion H; subst; specialize (H3 _ _ _ (CS_SeqCont _ _ _)).
      inversion H3; subst; specialize (H5 _ _ _ (CS_SeqCont _ _ _)).
      auto.
    - apply safe_Pre.
      { replace k with (nil ++ k); auto. apply reducible_ctx_step; auto. }
      intros.
      assert (~ Halt c1 k'); [solve_wp_0 |].
      pose proof fill_cstep_inv _ _ _ _ _ _ _ H3 H1 as (k'' & ? & ?); subst.
      apply IHn; clear n IHn.
      + intros n.
        specialize (H (S n)).
        inversion H; subst;
        [ apply nil_app_neq in H8; inversion H8 |
          apply nil_app_neq in H8; inversion H8 |
          apply nil_app_neq in H8; inversion H8 |].
        apply H7; apply cstep_ctx_step; auto.
      + intros.
        apply H2.
        apply (rt_trans cstep _ (c', k'', st')); auto; constructor; auto.
    - specialize (H (S O)).
      inversion H; subst.
      simpl in H3.
      assert (irreducible CSkip (KLoop1 c0 c3 :: k0 ++ KSeq c2 :: KSeq dead :: k) st); [constructor |].
      exfalso; apply (reducible_irreducible_ex CSkip (KLoop1 c0 c3 :: k0 ++ KSeq c2 :: KSeq dead :: k) st); auto.
    - specialize (H (S O)).
      inversion H; subst.
      simpl in H3.
      assert (irreducible CCont (KLoop2 c0 c3 :: k0 ++ KSeq c2 :: KSeq dead :: k) st); [constructor |].
      exfalso; apply (reducible_irreducible_ex CCont (KLoop2 c0 c3 :: k0 ++ KSeq c2 :: KSeq dead :: k) st); auto.
  }
  {
    unfold valid_continuation.
    intros.
    specialize (H _ H0 H1 H2); clear H0 H1 H2.
    unfold guard, Assertion_Shallow.Assertion_denote; intros ? [st1 [? ?]].
    specialize (H _ H0); clear H0.

    apply (safe_sim _ _ _ _ _ _ seq_sim_is_simulation (S_sim_seq _ _ _)) in H.
    replace (KSeq c2 :: k) with (nil ++ KSeq c2 :: k) in H; auto.
    remember (@nil KElements) as k1.
    rewrite Heqk1 in H1 at 2; clear Heqk1.

    unfold mstep in H1.
    rewrite rt_rt1n_iff in H1.
    remember (c1, k1, st1) as prog.
    remember (CSkip, nil, st) as term.
    revert dependent st1. revert c1 k1.
    induction H1; intros; subst.
    - inversion Heqprog; subst.
      intros n.
      specialize (H (S n)).
      simpl in H.
      inversion H; subst.
      apply H2; constructor.
    - destruct y as [[c1' k1'] st1'].
      apply (IHclos_refl_trans_1n eq_refl c1' k1' st1'); auto.
      intros n.
      specialize (H0 (S n)).
      inversion H0; subst;
      [apply nil_app_neq in H5; inversion H5 |
       apply nil_app_neq in H5; inversion H5 |
       apply nil_app_neq in H5; inversion H5 |].
      apply H4.
      apply cstep_ctx_step; auto.
  }
Qed.

Module Ctx2Com.
Fixpoint ctx2com' k c : com :=
  match k with
  | nil => c
  | K :: k =>
    match K with
    | KSeq c2 => ctx2com' k (CSeq c c2)
    | KLoop1 c1 c2 => ctx2com' k (CFor1 c c1 c2)
    | KLoop2 c1 c2 => ctx2com' k (CFor2 c c1 c2)
    end
  end.

Definition ctx2com k : com :=
  match k with
  | nil => CSkip
  | K :: k =>
    match K with
    | KSeq c => ctx2com' k c
    | KLoop1 c1 c2 => ctx2com' k (CFor1 CCont c1 c2)
    | KLoop2 c1 c2 => ctx2com' k (CFor c1 c2)
    end
  end.

(* Lemma ctx2com_tail : forall a k K,
  ctx2com ((a :: k) ++ K :: nil) = CSeq (ctx2com (a :: k)) (ctx2com (K :: nil)).
Proof.
  intros.
  pose proof rev_involutive (a :: k).
  remember (rev (a :: k)) as k'.
  clear Heqk'.
  revert a k H.
  induction k'; intros.
  - simpl in H. apply nil_cons in H. inversion H.
  - simpl in H. *)


(* Fixpoint ctx2com k : com :=
  match k with
  | nil => CSkip
  | K :: k =>
    match K with
    | KSeq c => 
        match k with
        | nil => c
        | _ => CSeq c (ctx2com k)
        end
    | KLoop1 c1 c2 => 
        match k with
        | nil => CSeq c2 (CFor c1 c2)
        | _ => CSeq (CSeq c2 (CFor c1 c2)) (ctx2com k)
        end
    | KLoop2 c1 c2 => 
        match k with
        | nil => CFor c1 c2
        | _ => CSeq (CFor c1 c2) (ctx2com k)
        end
    end
  end. *)
End Ctx2Com.

Module reverse_Ctx2Com.

Fixpoint ctx2com' k : com :=
  match k with
  | nil => CSkip
  | K :: k =>
    match K with
    | KSeq c => CSeq (ctx2com' k) c
    | KLoop1 c1 c2 => CFor1 (ctx2com' k) c1 c2
    | KLoop2 c1 c2 => CFor2 (ctx2com' k) c1 c2
    end
  end.

Definition ctx2com k : com := ctx2com' (rev k).

Lemma ctx2com_nil_CSkip : forall k,
  ctx2com' k = CSkip -> nil = k.
Proof.
  intros.
  destruct k; auto.
  destruct k; simpl in *; inversion H.
Qed.

(* Lemma ctx2com_tail : forall a k K,
  ctx2com ((a :: k) ++ K :: nil) = CSeq (ctx2com (a :: k)) (ctx2com (K :: nil)).
Proof.
  intros.
  unfold ctx2com.
  remember (rev (K :: nil)) as k'.
  simpl.
  rewrite rev_app_distr.
  rewrite <- Heqk'.
  simpl in Heqk'.
  subst.
  remember (rev k) as k'.
  clear k Heqk'. rename k' into k.
  assert ((K :: nil) ++ k = K :: k); [auto |].
  rewrite H; clear H.
  revert K.
  induction k; intros.
  - simpl. destruct K, a; auto.
  - remember (a0 :: k) as k'.
    simpl.
    destruct K; subst;
    rewrite IHk; auto.
Qed. *)

End reverse_Ctx2Com.


Fixpoint ctx_split k : continuation * continuation * continuation :=
  match k with
  | nil => (nil, nil, nil)
  | K :: k =>
    match K with 
    | KSeq c =>
      match (ctx_split k) with 
      | (k1, k2, k3) => (KSeq c :: k1, k2, k3)
      end
    | KLoop1 c1 c2 | KLoop2 c1 c2 =>
      (nil, K :: nil, k)
    end
  end.

Lemma ctx_split_k : forall k ka kb kc,
  ctx_split k = (ka, kb, kc) ->
  k = ka ++ kb ++ kc.
Proof.
  intro.
  induction k; intros; simpl in H.
  - inversion_clear H; auto.
  - destruct a.
    + destruct (ctx_split k) as [[k1 k2] k3]; inversion H; subst.
      simpl. f_equal.
      apply IHk; auto.
    + inversion_clear H. auto.
    + inversion_clear H. auto.
Qed.

Inductive no_loop_ctx : continuation -> Prop :=
| nil_no_loop : no_loop_ctx nil
| kseq_no_loop : forall c k, no_loop_ctx k -> no_loop_ctx (KSeq c :: k).

Lemma no_loop_ctx_app : forall k1 k2,
  no_loop_ctx (k1 ++ k2) -> no_loop_ctx k1 /\ no_loop_ctx k2.
Proof.
  intro k1.
  induction k1; intros.
  - simpl in *; split; [constructor | auto].
  - inversion H; subst.
    apply IHk1 in H1; destruct H1.
    split; auto.
    constructor; auto.
Qed.

Lemma no_loop_ctx_rev : forall k,
  no_loop_ctx k -> no_loop_ctx (rev k).
Proof.
  intros.
  rewrite <- rev_involutive in H.
  remember (rev k) as k'; clear k Heqk'; rename k' into k.
  induction k; simpl in *; [constructor|].
  apply no_loop_ctx_app in H; destruct H.
  inversion H0; subst.
  constructor.
  apply IHk; auto.
Qed.

(* no loop on the path of evaluation *)
Fixpoint no_loop_com c : Prop :=
  match c with
  | CSkip | CAss _ _ | CBreak | CCont => True
  | CSeq c1 c2 => no_loop_com c1
  | CIf _ c1 c2 =>
      no_loop_com c1 /\ no_loop_com c2
  | _ => False
  end.

Lemma safe_break_no_loop : forall k st,
  no_loop_ctx k -> safe CBreak k st.
Proof.
  intros.
  induction k.
  - intros n; constructor.
  - inversion H; subst.
    specialize (IHk H1); clear H1.
    intros n.
    destruct n; constructor.
    + exists CBreak, k, st; constructor.
    + intros.
      inversion H0; subst.
      apply IHk.
Qed.

Lemma ctx_split_ka : forall k ka kb kc,
  ctx_split k = (ka, kb, kc) -> no_loop_ctx ka.
Proof.
  intro.
  induction k; intros; simpl in H.
  - inversion_clear H; constructor.
  - destruct a.
    + destruct (ctx_split k) as [[k1 k2] k3]; inversion H; subst.
      constructor. apply (IHk k1 kb kc); auto.
    + inversion_clear H; constructor.
    + inversion_clear H; constructor.
Qed.

Lemma ctx_split_kb : forall k ka kb kc,
  ctx_split k = (ka, kb, kc) ->
  kb = nil \/ exists K c1 c2, kb = K :: nil /\ (K = KLoop1 c1 c2 \/ K = KLoop2 c1 c2).
Proof.
  intro.
  induction k; intros; simpl in H.
  - inversion_clear H; left; auto.
  - destruct a.
    + destruct (ctx_split k) as [[k1 k2] k3]; inversion H; subst.
      apply (IHk k1 _ kc); auto.
    + right.
      inversion_clear H.
      exists (KLoop1 c1 c2), c1, c2; auto.
    + right.
      inversion_clear H.
      exists (KLoop2 c1 c2), c1, c2; auto.
Qed.

Lemma ctx_split_kc : forall k ka kb kc,
  ctx_split k = (ka, kb, kc) ->
  kb = nil -> kc = nil.
Proof.
  intro.
  induction k; intros; simpl in H.
  - inversion_clear H; auto.
  - destruct a.
    + destruct (ctx_split k) as [[k1 k2] k3]; inversion H; subst.
      apply (IHk k1 nil kc); auto.
    + inversion H; subst.
      inversion H3.
    + inversion H; subst.
      inversion H3.
Qed.


(* Import Ctx2Com. *)
Import reverse_Ctx2Com.

Lemma ctx2com_preserve_noloop : forall k,
  no_loop_ctx k ->
  no_loop_com (ctx2com k).
Proof.
  intros.
  unfold ctx2com.
  apply no_loop_ctx_rev in H.
  remember (rev k) as k'; clear k Heqk'; rename k' into k.
  induction k; simpl; auto.
  destruct a; [|inversion H|inversion H].
  simpl. apply IHk.
  inversion H; subst; auto.
Qed.

Definition con_safe_convert k : continuation :=
  match (ctx_split k) with
  | (ka, kb, kc) =>
    KSeq (ctx2com (ka ++ kb)) :: KSeq CBreak :: KLoop1 CSkip dead :: kc
  end.

Lemma continue_csc_guarded : forall P k,
  guard P CCont (con_safe_convert k).
Proof.
  unfold guard.
  intros.
  intros n.
  unfold con_safe_convert.
  destruct (ctx_split k) as [[k1 k2] k3].

  destruct n; [constructor |].
  apply safe_Pre; [exists CCont, (KSeq CBreak :: KLoop1 CSkip dead :: k3), st; constructor |].
  intros. inversion_clear H0.

  destruct n; [constructor |].
  apply safe_Pre; [exists CCont, (KLoop1 CSkip dead :: k3), st'; constructor |].
  intros. inversion_clear H0.

  destruct n; [constructor |].
  apply safe_Pre; [exists dead, (KLoop2 CSkip dead :: k3), st'0; constructor |].
  intros. inversion_clear H0.

  apply dead_safe.
Qed.

(* Inductive skipcsc_remove_tail_sim : (com * continuation) -> (com * continuation) -> Prop :=
| skipcsc_rtsim_id : forall c k, skipcsc_sim1 (c, k) (c, k)
| skipcsc_rtsim_1 : forall c k kc,
    skipcsc_sim1 (c, k ++ KSeq CBreak :: KLoop1 CSkip dead :: kc)
                 (c, k ++ kc)
| skipcsc_sim1_1 : 
    skipcsc_sim1 ()
. *)

Inductive ctx2com_sim : (com * continuation) -> (com * continuation) -> Prop :=
| ctx2com_sim_id : forall c k, ctx2com_sim (c, k) (c, k)
| ctx2com_sim_top : forall k k0, ctx2com_sim (ctx2com k, k0) (CSkip, k ++ k0).

Lemma ctx2com_sim_is_simulation : simulation ctx2com_sim.
Proof.
  unfold simulation.
  intros; split; [|split]; intros.
  {
    (* inversion H; subst; [left; auto |].
    inversion H0. *)
    destruct H0 as [? | [? | ?]]; inversion H0; subst;
    inversion H; subst; auto.
    - unfold ctx2com in H2.
      destruct k; simpl in *; inversion H2; auto.
      apply ctx2com_nil_CSkip in H2.
      apply app_cons_not_nil in H2. inversion H2.
    - unfold ctx2com in H2.
      destruct k; simpl in *; inversion H2; auto.
      exfalso. revert H2; clear; intros.
      remember (rev k0) as k1; clear Heqk1.
      destruct k1; [destruct k; inversion H2 |].
      destruct k1; inversion H2.
    - unfold ctx2com in H2.
      destruct k; simpl in *; inversion H2; auto.
      exfalso. revert H2; clear; intros.
      remember (rev k0) as k1; clear Heqk1.
      destruct k1; [destruct k; inversion H2 |].
      destruct k1; inversion H2.
  }
  {
    inversion H0; subst; inversion H; subst; try constructor.
    - apply ctx2com_nil_CSkip in H2.
      destruct k0; inversion H2; subst; auto.
      apply app_cons_not_nil in H3; inversion H3.
    - unfold ctx2com in H2.
      destruct (rev k0); inversion H2; subst.
      destruct k1; inversion H3.
  }
  {
    inversion H; subst;
    [exists c1', k1'; split; constructor; auto|].
    unfold ctx2com in H0.
    rewrite <- (rev_involutive k).
    remember (rev k) as k'.
    destruct k'.
    - simpl in *.
      exists c1', k1'; split; constructor; auto.
    - exists CSkip, (rev (k0 :: k') ++ k1).
      destruct k0; inversion H0; subst; simpl in *;
      (
        split; [apply rt_refl |];
        rewrite <- app_assoc; simpl;
        rewrite <- (rev_involutive k') at 1;
        remember (rev k') as k'';
        replace (ctx2com' (rev k'')) with (ctx2com k''); auto;
        constructor
      ).
  }
Qed.

Lemma skipcsc_safe_1: forall c k st,
  safe c k st ->
  safe c (k ++ KSeq CBreak :: KLoop1 CSkip dead :: nil) st.
Proof.
  intros.
  intros n; revert c k st H;
  induction n; intros; [constructor |].
  pose proof H (S n).
  inversion H0; subst; simpl in *.
  - apply safe_Pre; [exists CBreak, (KLoop1 CSkip dead :: nil), st; constructor | intros].
    inversion H1; subst.
    destruct n; [constructor |].
    apply safe_Pre; [exists CSkip, nil, st'; constructor| intros].
    inversion H2; subst; constructor.
  - apply safe_Pre; [exists CBreak, (KLoop1 CSkip dead :: nil), st; constructor | intros].
    inversion H1; subst.
    destruct n; [constructor |].
    apply safe_Pre; [exists CSkip, nil, st'; constructor| intros].
    inversion H2; subst; constructor.
  - apply safe_Pre; [exists CCont, (KLoop1 CSkip dead :: nil), st; constructor | intros].
    inversion H1; subst.
    destruct n; [constructor |].
    apply safe_Pre; [exists dead, (KLoop2 CSkip dead :: nil), st'; constructor| intros].
    inversion H2; subst.
    apply dead_safe.
  - apply safe_Pre; [apply reducible_ctx_step; auto|intros].
    apply fill_cstep_inv in H1; [|solve_wp_0].
    destruct H1 as [k'' [? ?]]; subst.
    apply IHn. clear dependent n.
    intros n.
    specialize (H (S n)).
    inversion H; subst;
    [inversion H4|inversion H4|inversion H4|].
    apply H3; auto.
Qed.

Inductive skipcsc_sim : (com * continuation) -> (com * continuation) -> Prop :=
| skipcsc_sim_id : forall c k, skipcsc_sim (c, k) (c, k)
| skipcsc_sim_ka : forall c ka K c1 c2 kc,
    K = KLoop1 c1 c2 \/ K = KLoop2 c1 c2 ->
    skipcsc_sim (c, ka ++ K :: KSeq CBreak :: KLoop1 CSkip dead :: kc) (c, ka ++ K :: kc)
| skipcsc_sim_bk : forall kc,
    skipcsc_sim (CSkip, KSeq CBreak :: KLoop1 CSkip dead :: kc) (CSkip, kc)
| skipcsc_sim_lp : forall kc,
    skipcsc_sim (CBreak, KLoop1 CSkip dead :: kc) (CSkip, kc)
.

Lemma skipcsc_sim_is_simulation: simulation skipcsc_sim.
Proof.
  unfold simulation.
  intros; split; [|split]; intros.
  {
    (* inversion H; subst; [left; auto |].
    inversion H0. *)
    destruct H0 as [? | [? | ?]]; inversion H0; subst;
    inversion H; subst; auto.
    - apply eq_Symmetric, app_cons_not_nil in H3; inversion H3.
    - apply eq_Symmetric, app_cons_not_nil in H3; inversion H3.
    - apply eq_Symmetric, app_cons_not_nil in H3; inversion H3.
  }
  {
    inversion H0; subst; inversion H; subst; try constructor.
    - destruct ka; inversion H3; subst; simpl in *; constructor.
    - destruct ka; inversion H3; subst; simpl in *; constructor.
  }
  {
    inversion H; subst;
    [exists c1', k1'; split; constructor; auto| | |].
    - pose proof (halt_choice c2 ka st) as [? | [? | ?]].
    {
      destruct H1 as [? | [? | ?]]; inversion H1; subst; destruct H2; subst; simpl in *; inversion H0; subst.
      - exists (CSeq c0 CCont), (KLoop1 c0 c3 :: kc); split;
        [constructor; constructor |].
        rewrite <- (app_nil_l (KLoop1 c0 c3 :: KSeq CBreak :: KLoop1 CSkip dead :: kc)).
        rewrite <- (app_nil_l (KLoop1 c0 c3 :: kc)).
        apply (skipcsc_sim_ka _ _ _ c0 c3); auto.
      - exists CSkip, kc; split; constructor; constructor.
      - exists CSkip, kc; split; constructor; constructor.
      - exists c1', (KLoop2 c0 c1' :: kc); split; try (constructor; constructor).
        rewrite <- (app_nil_l (KLoop2 c0 c1' :: KSeq CBreak :: KLoop1 CSkip dead :: kc)).
        rewrite <- (app_nil_l (KLoop2 c0 c1' :: kc)).
        apply (skipcsc_sim_ka _ _ _ c0 c1'); auto.
    }
    {
      apply fill_cstep_inv in H0; [| solve_wp_0].
      destruct H0 as [k' [? ?]]; subst.
      exists c1', (k' ++ K :: kc); split.
      - constructor.
        apply cstep_ctx_step; auto.
      - apply (skipcsc_sim_ka _ _ _ c0 c3); auto.
    }
    {
      apply fill_cstep_inv in H0; [| solve_wp_0].
      destruct H0 as [k' [? ?]]; subst.
      assert (reducible c2 ka st);
      [exists c1', k', st'; auto |].
      exfalso; apply (reducible_irreducible_ex c2 ka st); auto.
    }
    - inversion H0; subst.
      exists CSkip, k2; split; [apply rt_refl | constructor].
    - inversion H0; subst.
      exists CSkip, k1'; split; [apply rt_refl | constructor].
  }
Qed.

Lemma skipcsc_safe_2: forall ka c1 c2 kc st,
  safe CSkip (ka ++ KLoop1 c1 c2 :: kc) st ->
  safe CSkip (ka ++ KLoop1 c1 c2 :: KSeq CBreak :: KLoop1 CSkip dead :: kc) st.
Proof.
  intros.
  apply (safe_sim CSkip CSkip (ka ++ KLoop1 c1 c2 :: kc) (ka ++ KLoop1 c1 c2 :: KSeq CBreak :: KLoop1 CSkip dead :: kc) st _ skipcsc_sim_is_simulation); auto.
  eapply skipcsc_sim_ka; auto.
Qed.

Lemma skipcsc_safe_3: forall c1 c2 kc st,
  safe CSkip (KLoop2 c1 c2 :: kc) st ->
  safe CSkip (KSeq (CFor2 CSkip c1 c2) :: KSeq CBreak :: KLoop1 CSkip dead :: kc) st.
Proof.
  intros.
  intros n; destruct n; [constructor |].
  apply safe_Pre; [exists (CFor2 CSkip c1 c2), (KSeq CBreak :: KLoop1 CSkip dead :: kc), st; constructor|intros].
  inversion H0; subst; clear H0.
  destruct n; [constructor |].
  apply safe_Pre; [exists CSkip, (KLoop2 c1 c2 :: KSeq CBreak :: KLoop1 CSkip dead :: kc), st'; constructor|intros].
  inversion H0; subst; clear H0. rename st'0 into st.

  rewrite <- (app_nil_l (KLoop2 c1 c2 :: KSeq CBreak :: KLoop1 CSkip dead :: kc)).
  rewrite <- (app_nil_l (KLoop2 c1 c2 :: kc)) in H.
  revert n.
  replace (forall n : nat,
  safe_n n CSkip (nil ++ KLoop2 c1 c2 :: KSeq CBreak :: KLoop1 CSkip dead :: kc)
    st) with (safe CSkip (nil ++ KLoop2 c1 c2 :: KSeq CBreak :: KLoop1 CSkip dead :: kc)
    st); auto.
    pose proof safe_sim.
  apply (safe_sim CSkip CSkip (nil ++ KLoop2 c1 c2 :: kc) (nil ++ KLoop2 c1 c2 :: KSeq CBreak :: KLoop1 CSkip dead :: kc) st _ skipcsc_sim_is_simulation); auto.
  econstructor; auto.
Qed.

Lemma skipcsc_safe_4: forall k ka c1 c2 kc st,
  safe CSkip ((k :: ka) ++ KLoop2 c1 c2 :: kc) st ->
  safe CSkip ((k :: ka) ++ KLoop2 c1 c2 :: KSeq CBreak :: KLoop1 CSkip dead :: kc) st.
Proof.
  intros.
  eapply (safe_sim _ _ _ _ _ _ skipcsc_sim_is_simulation);
  [| apply H].
  econstructor; auto.
Qed.

Lemma skip_csc_guarded : forall P k,
  guard P CSkip k ->
  guard P CSkip (con_safe_convert k).
Proof.
  unfold con_safe_convert.
  intros.
  destruct (ctx_split k) as [[ka kb] kc] eqn:H0.
  pose proof ctx_split_k _ _ _ _ H0; subst.
  pose proof ctx_split_ka _ _ _ _ H0.
  pose proof ctx_split_kb _ _ _ _ H0.
  pose proof ctx_split_kc _ _ _ _ H0.
  destruct H2;
  [| clear H3; destruct H2 as (K & c1 & c2 & ? & [? | ?]); subst].
  {
    specialize (H3 H2); subst.
    simpl in *. rewrite app_nil_r in *.
    intros st Hst.
    specialize (H _ Hst); clear Hst.
    intros n; destruct n; [constructor |].
    apply safe_Pre;
    [exists (ctx2com ka), (KSeq CBreak :: KLoop1 CSkip dead :: nil), st; constructor|intros].
    inversion H2; subst.
    revert n.
    apply (safe_sim _ _ _ _ _ _ ctx2com_sim_is_simulation (ctx2com_sim_top _ _)).
    apply skipcsc_safe_1; auto.
  }
  {
    simpl in *.
    intros st ?.
    specialize (H _ H2).

    destruct ka.
    - unfold ctx2com. simpl in *.
      specialize (H 1).
      inversion H; subst.
      pose proof IR_ForSkip c1 c2 kc st.
      exfalso; apply (reducible_irreducible_ex CSkip (KLoop1 c1 c2 :: kc) st); auto.
    - intros n; destruct n; [constructor |].
      apply safe_Pre; [exists (ctx2com ((k :: ka) ++ KLoop1 c1 c2 :: nil)), (KSeq CBreak :: KLoop1 CSkip dead :: kc), st; constructor|intros].
      inversion H3; subst.
      revert n.
      apply (safe_sim _ _ _ _ _ _ ctx2com_sim_is_simulation (ctx2com_sim_top _ _)).
      replace ((k :: ka ++ KLoop1 c1 c2 :: nil) ++ KSeq CBreak :: KLoop1 CSkip dead :: kc) with ((k :: ka) ++ KLoop1 c1 c2 :: KSeq CBreak :: KLoop1 CSkip dead :: kc); [apply skipcsc_safe_2; auto |].
      rewrite app_comm_cons.
      rewrite <- app_assoc.
      f_equal.
  }
  {
    simpl in *.
    intros st ?.
    specialize (H _ H2).

    destruct ka.
    - unfold ctx2com. simpl in *.
      apply skipcsc_safe_3; auto.
    - intros n; destruct n; [constructor |].
      apply safe_Pre; [exists (ctx2com ((k :: ka) ++ KLoop2 c1 c2 :: nil)), (KSeq CBreak :: KLoop1 CSkip dead :: kc), st; constructor | intros].
      inversion H3; subst.
      revert n.
      apply (safe_sim _ _ _ _ _ _ ctx2com_sim_is_simulation (ctx2com_sim_top _ _)).
      rewrite app_comm_cons.
      rewrite <- app_assoc.
      simpl.
      apply skipcsc_safe_4; auto.
  }
Qed.

Inductive breakcsc_sim : (com * continuation) -> (com * continuation) -> Prop :=
| breakcsc_sim_id : forall c k, breakcsc_sim (c, k) (c, k)
| breakcsc_sim_1 : forall k k', no_loop_ctx k ->
      breakcsc_sim (CBreak, k ++ k') (CBreak, k')
.

Lemma breakcsc_sim_is_simulation : simulation breakcsc_sim.
Proof.
  unfold simulation; intros.
  split; [| split]; intros.
  {
    destruct H0 as [? | [? | ?]]; inversion H0; subst;
    inversion H; subst; auto.
    destruct k2; [| apply eq_Symmetric, app_cons_not_nil in H1; inversion H1].
    rewrite app_nil_r in H1; subst. left; auto.
  }
  {
    inversion H0; subst; inversion H; subst; try constructor.
    (* exfalso; apply H3; simpl; auto. *)
  }
  {
    inversion H; subst.
    - exists c1', k1'; split; constructor; auto.
    - destruct k; simpl in H0; [exists c1', k1'; split; constructor; auto|].
      inversion H0; subst; [| inversion H2 | inversion H2].
      exists CBreak, k2; split; [apply rt_refl | constructor].
      inversion H2; subst; auto.
  }
Qed.

Lemma break_csc_guarded : forall P k,
  guard P CBreak k ->
  guard P CBreak (con_safe_convert k).
Proof.
  unfold con_safe_convert.
  intros.
  destruct (ctx_split k) as [[ka kb] kc] eqn:H0.
  pose proof ctx_split_k _ _ _ _ H0; subst.
  pose proof ctx_split_ka _ _ _ _ H0.
  pose proof ctx_split_kb _ _ _ _ H0.
  pose proof ctx_split_kc _ _ _ _ H0.
  destruct H2;
  [| clear H3; destruct H2 as (K & c1 & c2 & ? & [? | ?]); subst].
  {
    specialize (H3 H2); subst.
    simpl in *. rewrite app_nil_r in *.
    intros ? _ n.
    destruct n; [constructor |].
    apply safe_Pre; [exists CBreak, (KSeq CBreak :: KLoop1 CSkip dead :: nil), st; constructor | intros].
    inversion H2; subst.
    destruct n; [constructor |].
    apply safe_Pre; [exists CBreak, (KLoop1 CSkip dead :: nil), st'; constructor | intros].
    inversion H3; subst.
    destruct n; [constructor |].
    apply safe_Pre; [exists CSkip, nil, st'0; constructor | intros].
    inversion H4; subst; constructor.
  }
  {
    simpl in *.
    intros st ?.
    specialize (H _ H2).
    
    destruct ka.
    - unfold ctx2com. simpl in *. 
      replace (KSeq (CFor1 CSkip c1 c2) :: KSeq CBreak :: KLoop1 CSkip dead :: kc) with ((KSeq (CFor1 CSkip c1 c2) :: KSeq CBreak :: nil) ++ KLoop1 CSkip dead :: kc); auto.
      assert (no_loop_ctx (KSeq (CFor1 CSkip c1 c2) :: KSeq CBreak :: nil)); [repeat constructor |].
      apply (safe_sim _ _ _ _ _ _ breakcsc_sim_is_simulation (breakcsc_sim_1 _ _  H3)).

      intros n.
      specialize (H n).
      destruct n; [constructor |].
      apply safe_Pre; [exists CSkip, kc, st; constructor |].
      inversion 1; subst.
      inversion H; subst.
      apply H7; constructor.
    - replace (KSeq (ctx2com ((k :: ka) ++ KLoop1 c1 c2 :: nil))
    :: KSeq CBreak :: KLoop1 CSkip dead :: kc) with ((KSeq (ctx2com ((k :: ka) ++ KLoop1 c1 c2 :: nil))
    :: KSeq CBreak :: nil) ++ KLoop1 CSkip dead :: kc); auto.
      assert (no_loop_ctx (KSeq (ctx2com ((k :: ka) ++ KLoop1 c1 c2 :: nil)) :: KSeq CBreak :: nil)); [repeat constructor|].
      apply (safe_sim _ _ _ _ _ _ breakcsc_sim_is_simulation (breakcsc_sim_1 _ _  H3)).

      assert (safe CBreak (KLoop1 c1 c2 :: kc) st).
      {
        revert H H1. clear. intros.
        revert dependent k. induction ka; intros.
        - inversion H1; subst.
          simpl in H.
          intros n. specialize (H (S n)).
          inversion H; subst.
          apply H4. constructor.
        - remember (a :: ka) as k'.
          inversion H1; subst.
          apply (IHka a); auto.
          intros n. specialize (H (S n)).
          inversion H; subst.
          apply H4. constructor.
      }
    
      intros n. specialize (H4 n).
      destruct n; [constructor |].
      apply safe_Pre; [exists CSkip, kc, st; constructor | intros].
      inversion H5; subst.
      inversion H4; subst.
      apply H8; constructor.
  }
  {
    simpl in *.
    intros st ?.
    specialize (H _ H2).

    destruct ka.
    - unfold ctx2com. simpl in *. 
      replace (KSeq (CFor2 CSkip c1 c2) :: KSeq CBreak :: KLoop1 CSkip dead :: kc) with ((KSeq (CFor2 CSkip c1 c2) :: KSeq CBreak :: nil) ++ KLoop1 CSkip dead :: kc); auto.
      assert (no_loop_ctx (KSeq (CFor2 CSkip c1 c2) :: KSeq CBreak :: nil)); [repeat constructor |].
      apply (safe_sim _ _ _ _ _ _ breakcsc_sim_is_simulation (breakcsc_sim_1 _ _  H3)).

      intros n.
      specialize (H n).
      destruct n; [constructor |].
      apply safe_Pre; [exists CSkip, kc, st; constructor |].
      inversion 1; subst.
      inversion H; subst.
      apply H7; constructor.
    - replace (KSeq (ctx2com ((k :: ka) ++ KLoop2 c1 c2 :: nil))
    :: KSeq CBreak :: KLoop1 CSkip dead :: kc) with ((KSeq (ctx2com ((k :: ka) ++ KLoop2 c1 c2 :: nil))
    :: KSeq CBreak :: nil) ++ KLoop1 CSkip dead :: kc); auto.
      assert (no_loop_ctx (KSeq (ctx2com ((k :: ka) ++ KLoop2 c1 c2 :: nil)) :: KSeq CBreak :: nil)); [repeat constructor|].
      apply (safe_sim _ _ _ _ _ _ breakcsc_sim_is_simulation (breakcsc_sim_1 _ _  H3)).

      assert (safe CBreak (KLoop2 c1 c2 :: kc) st).
      {
        revert H H1. clear. intros.
        revert dependent k. induction ka; intros.
        - inversion H1; subst.
          simpl in H.
          intros n. specialize (H (S n)).
          inversion H; subst.
          apply H4. constructor.
        - remember (a :: ka) as k'.
          inversion H1; subst.
          apply (IHka a); auto.
          intros n. specialize (H (S n)).
          inversion H; subst.
          apply H4. constructor.
      }
    
      intros n. specialize (H4 n).
      destruct n; [constructor |].
      apply safe_Pre; [exists CSkip, kc, st; constructor | intros].
      inversion H5; subst.
      inversion H4; subst.
      apply H8; constructor.
  }
Qed.

(* Inductive noconcsc_sim : (com * continuation) -> (com * continuation) -> Prop :=
| noconcsc_sim_id : forall c k, noconcsc_sim (c, k) (c, k)
| 

Lemma nocontinue_csc_guard : forall P c k,
  nocontinue c nil ->
  guard P c (con_safe_convert k) ->
  guard P c k.
Proof.
  intros.
  intros st ?.
  specialize (H0 _ H1); clear dependent P.
  unfold con_safe_convert in H0.
  destruct (ctx_split k) as [[ka kb] kc] eqn:eq.
  pose proof ctx_split_k _ _ _ _ eq; subst.
  pose proof ctx_split_ka _ _ _ _ eq.
  pose proof ctx_split_kb _ _ _ _ eq.
  pose proof ctx_split_kc _ _ _ _ eq.
  clear eq.

Qed. *)

Lemma nocontinue_valid_continuation_bot : forall P c Q R1 R2,
  nocontinue c nil ->
  valid_continuation P c Q R1 R2 ->
  valid_continuation P c Q R1 (fun _ => False).
Proof.
  unfold valid_continuation.
  intros; clear H3.
  apply skip_csc_guarded in H1.
  pose proof continue_csc_guarded R2 k.
  apply break_csc_guarded in H2.
  specialize (H0 _ H1 H2 H3); clear H1 H2 H3.
Admitted.

Theorem nocontinue_valid_continuation : forall P c Q R1 R2 R2',
  nocontinue c nil ->
  valid_continuation P c Q R1 R2 ->
  valid_continuation P c Q R1 R2'.
Proof.
  unfold valid_continuation.
  intros.
  pose proof break_csc_guarded.
Admitted.

Theorem if_seq_valid_continuation : forall P b c1 c2 c3 Q R1 R2,
  valid_continuation P (CSeq (CIf b c1 c2) c3) Q R1 R2 ->
  valid_continuation P (CIf b (CSeq c1 c3) (CSeq c2 c3)) Q R1 R2.
Proof.
Admitted.

Theorem loop_nocontinue_valid_continuation : forall P c1 c2 Q R1 R2,
  nocontinue c1 ->
  nocontinue c2 ->
  valid_continuation P (CFor (CSeq c1 c2) CSkip) Q R1 R2 ->
  valid_continuation P (CFor c1 c2) Q R1 R2.
Proof.
  unfold valid_continuation.
  intros.
Admitted. 
