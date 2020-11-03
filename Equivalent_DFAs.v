Require Import Nat PeanoNat List DFA Lia NatListSet DistinguishableStates.
Import ListNotations.

(*
  Two DFAs are said to be unidirectionally equivalent if the second DFA accepts every word the
  first DFA accepts.
*)
Definition equivalent_dfas g1 g2 := forall w,
  acceptsb g1 w = true -> acceptsb g2 w = true.

(* Since every state is a natural, max_state is the maximum natural in states. *)
Definition max_state g := max_in_list (states g).

(* Adds a given natural n to every state in the DFA *)
Fixpoint add_to_states g n :=
  match g with
  | state q accept::g => state (q + n) accept::add_to_states g n
  | symbol a::g => symbol a::add_to_states g n
  | transition q1 a q2::g => transition (q1 + n) a (q2 + n)::add_to_states g n
  | nil => nil
  end.

(*Definition add_to_states' g1 g2 n := g1 ++ add_to_states g2 n.*)
(* Join two DFAs *)
Definition join_dfa g1 g2 := g1 ++ add_to_states g2 (max_state g1 + 1).

(* Proof add_to_states is correct *)
Lemma add_to_states_correct g n q :
  In q (states g) <-> In (q+n) (states (add_to_states g n)).
Proof.
  induction g as [|[q1 acc|a|q1 a q2] g IH]; simpl; split; intro H.
  1,2: contradiction.
  - apply in_add__in_cons; apply in_add__in_cons in H; destruct H as [H|H].
    + subst; left; auto.
    + right; apply IH; auto.
  - apply in_add__in_cons; apply in_add__in_cons in H; destruct H as [H|H].
    + assert (q1 = q). nia. subst; left; auto.
    + right; apply IH; auto.
  - apply IH; auto.
  - apply IH; auto.
  - apply in_add__in_cons; apply in_add__in_cons in H; destruct H as [H|H].
    + subst; left; auto.
    + right; apply in_add__in_cons; apply in_add__in_cons in H; destruct H as [H|H].
      * subst; left; auto.
      * right; apply IH; auto.
  - apply in_add__in_cons; apply in_add__in_cons in H; destruct H as [H|H].
    + assert (q1 = q). nia. subst; left; auto.
    + right; apply in_add__in_cons; apply in_add__in_cons in H; destruct H as [H|H].
      * assert (q2 = q). nia. subst; left; auto.
      * right; apply IH; auto.
Qed.

(* Every state of the DFA returned by add_to_states applied to n is greater or equal to n. *)
Lemma add_to_states_min g n q :
  In q (states (add_to_states g n)) -> q >= n.
Proof.
  induction g as [|[q1 acc|a|q1 a q2] g IH].
  - contradiction.
  - simpl; intro H; apply in_add__in_cons in H; destruct H as [H|H]; try nia; auto.
  - auto.
  - simpl; intro H; apply in_add__in_cons in H; destruct H as [H|H];
    try (apply in_add__in_cons in H; destruct H as [H|H]); try nia;
    auto.
Qed.

(*
  The transitionf of g1 applied to some given q and a is equal to the transitionf of the joint DFAs
  applied to them if q is a state of g1.
*)
Lemma join_dfa_transitionf_l g1 g2 n q a :
  n > max_state g1 ->
  In q (states g1) ->
  transitionf g1 q a = transitionf (g1 ++ add_to_states g2 n) q a.
Proof.
  intros H H0; destruct (transitionf g1 q a) as [q3|] eqn:H1.
  - symmetry; apply transitionf_app; auto.
  - destruct (transitionf (g1 ++ add_to_states g2 n)) as [q'|] eqn:H2; auto;
    apply app_transitionf in H2; destruct H2 as [H2|H2].
    + rewrite <- H1, <- H2; auto.
    + apply transitionf_defined in H2; destruct H2 as [H2 _]; apply add_to_states_min in H2;
      apply leq_max_in_list in H0; unfold max_state in H, H2; nia.
Qed.

(* If q is a state of g1, q accepts the same words in g1 and in the joint DFAs. *)
Lemma join_dfa_accept_opt_l g1 g2 n q w :
  n > max_state g1 ->
  In q (states_opt g1) ->
  accept_opt g1 (xtransition g1 q w) =
  accept_opt (g1 ++ add_to_states g2 n) (xtransition (g1 ++ add_to_states g2 n) q w).
Proof.
  intro H; revert q;
  induction w as [|a w IH]; intros q H0; simpl; destruct q as [q|]; auto.
  - apply some_state_in_states_opt in H0; simpl; destruct (accept g1 q) eqn:H1.
    + symmetry; apply accept_app; auto.
    + destruct (accept (g1 ++ add_to_states g2 n) q) eqn:H2.
      2: auto.
      apply app_accept in H2; destruct H2 as [H2|H2].
      rewrite H1 in H2; discriminate.
      apply accept_in_states, add_to_states_min in H2; apply leq_max_in_list in H0;
      unfold max_state in H; nia.
  - replace (transitionf (g1 ++ add_to_states g2 n) q a) with (transitionf g1 q a).
    2: apply some_state_in_states_opt in H0; apply join_dfa_transitionf_l; auto.
    apply IH, transitionf_in_states_opt.
Qed.

(*
  transitionf of (add_to_states g2 n) applied to some given q and a is equal to the transitionf of
  the joint DFAs applied to them if q is a state of (add_to_states g2 n). n has to be greater than
  the maximum state of g1.
*)
Lemma join_dfa_transitionf_r g1 g2 n q a :
  n > max_state g1 ->
  In q (states (add_to_states g2 n)) ->
  transitionf (add_to_states g2 n) q a = transitionf (g1 ++ add_to_states g2 n) q a.
Proof.
  intros H H0; destruct (transitionf (add_to_states g2 n) q a) as [q3|] eqn:H1.
  - symmetry; apply transitionf_app_r; destruct (in_dec Nat.eq_dec q (states g1)) as [H2|H2].
    apply add_to_states_min in H0; unfold max_state in H; apply leq_max_in_list in H2; nia.
    2,3: auto.
    destruct (transitionf g1 q a) eqn:H3.
    2: auto.
    apply transitionf_defined in H3; destruct H3 as [H3 _]; contradiction.
  - destruct (transitionf (g1 ++ add_to_states g2 n) q a) as [q'|] eqn:H2.
    2: auto.
    apply app_transitionf in H2; destruct H2 as [H2|H2].
    + apply transitionf_defined in H2; destruct H2 as [H2 _]; apply leq_max_in_list in H2;
      apply add_to_states_min in H0; unfold max_state in H; nia.
    + rewrite <- H1, <- H2; auto.
Qed.

(* If q is a state of (add_to_states g2 n), q accepts the same words in g1 and in the joint DFAs. *) 
Lemma join_dfa_accept_opt_r g1 g2 n q w :
  n > max_state g1 ->
  In q (states_opt (add_to_states g2 n)) ->
  accept_opt (add_to_states g2 n) (xtransition (add_to_states g2 n) q w) =
  accept_opt (g1 ++ add_to_states g2 n) (xtransition (g1 ++ add_to_states g2 n) q w).
Proof.
  intro H; revert q;
  induction w as [|a w IH]; intros q H0; simpl; destruct q as [q|].
  - simpl; apply some_state_in_states_opt in H0; destruct (accept (add_to_states g2 n) q) eqn:H1.
    + symmetry; apply accept_app_r.
      2: auto.
      intro H2; apply add_to_states_min in H0; apply leq_max_in_list in H2;
      unfold max_state in H; nia.
    + destruct (accept (g1 ++ add_to_states g2 n) q) eqn:H2.
      2: auto.
      apply app_accept in H2; destruct H2 as [H2|H2].
      2: rewrite H1 in H2; discriminate.
      apply accept_in_states, leq_max_in_list in H2; apply add_to_states_min in H0;
      unfold max_state in H; nia.
  - auto.
  - replace (transitionf (g1 ++ add_to_states g2 n) q a) with (transitionf (add_to_states g2 n) q a).
    2: apply some_state_in_states_opt in H0; apply join_dfa_transitionf_r; auto.
    apply IH, transitionf_in_states_opt.
  - auto.
Qed.

(* A given q accepts a given word w in g iff (q + n) accepts w in (add_to_states g n). *)
Lemma add_to_states_accept g n q w :
  accept_opt g (xtransition g (Some q) w) = accept_opt (add_to_states g n) (xtransition (add_to_states g n) (Some (q + n)) w).
Proof.
  assert (H0: forall q q1 n, (q + n =? q1 + n) = (q =? q1)). {
    clear n q; intros q q1 n; destruct (q + n =? q1 + n) eqn:H0, (q =? q1) eqn:H1; auto.
    apply EqNat.beq_nat_true in H0; assert (q = q1); try nia;
    subst; rewrite Nat.eqb_refl in H1.
    2: apply EqNat.beq_nat_true in H1; subst; rewrite Nat.eqb_refl in H0.
    1,2: discriminate.
  }
  revert q; induction w as [|a w IH]; intro q; simpl.
  - induction g as [|[q1 acc|b|q1 b q2] g IH]; simpl in *; auto; rewrite H0;
    destruct (q =? q1); auto.
  - simpl; destruct (transitionf g q a) as [q'|] eqn:H.
    + replace (transitionf (add_to_states g n) (q + n) a) with (Some (q' + n)).
      apply IH.
      clear IH; induction g as [|[q1 acc|b|q1 b q2] g IH]; simpl in *; try discriminate; auto.
      rewrite H0; destruct (andb (q =? q1) (a =? b));
      try (injection H; intros; subst); auto.
    + replace (transitionf (add_to_states g n) (q + n) a) with (@None nat).
      rewrite xtransition_none, xtransition_none; auto.
      clear IH; induction g as [|[q1 acc|b|q1 b q2] g IH]; simpl in *; auto.
      rewrite H0; destruct (andb (q =? q1) (a =? b)); try discriminate; auto.
Qed.

(* Adds a given n to the start state if it exists *)
Definition add_to_start g n :=
  match start g with
  | Some q => Some (q + n)
  | None => None
  end.

(*
  The DFAs are equivalent iff the start state of g1 is equivalent to the start state of g2 plus
  (max_state g1 + 1).
*)
Lemma equivalent_joint_dfas g1 g2 :
  ~ distinguishable_states (join_dfa g1 g2) (start g1) (add_to_start g2 (max_state g1 + 1)) <->
  equivalent_dfas g1 g2.
Proof.
  split; intro H.
  - remember (join_dfa g1 g2) as g; remember (start g1) as q1; remember (add_to_start g2 (max_state g1 + 1)) as q2.
    assert (H0: forall w, accept_opt g (xtransition g q1 w) = true -> accept_opt g (xtransition g q2 w) = true).
    apply equivalent_states; auto.
    subst; intros w H1; specialize (H0 w); unfold acceptsb, ixtransition in H1;
    rewrite join_dfa_accept_opt_l with (g2:=g2) (n:=max_state g1 + 1) in H1.
    2: nia.
    2: apply start_in_states_opt.
    apply H0 in H1; unfold acceptsb, ixtransition; unfold add_to_start in H1; destruct (start g2) as [q|] eqn:H2.
    2: rewrite xtransition_none in H1; discriminate.
    rewrite add_to_states_accept with (n:=max_state g1 + 1); rewrite join_dfa_accept_opt_r with (g1:=g1).
    auto.
    nia.
    apply some_state_in_states_opt.
    apply add_to_states_correct, some_state_in_states_opt; rewrite <- H2; apply start_in_states_opt.
  - unfold equivalent_dfas in H; apply equivalent_states; intros w H0; specialize (H w).
    assert (H1: accept_opt g1 (xtransition g1 (start g1) w) = true). {
      rewrite <- H0; apply join_dfa_accept_opt_l. nia. apply start_in_states_opt.
    }
    apply H in H1; unfold acceptsb, ixtransition in H1; destruct (start g2) as [q|] eqn:H2.
    2: rewrite xtransition_none in H1; discriminate.
    rewrite add_to_states_accept with (n:=max_state g1 + 1) in H1;
    unfold add_to_start; rewrite H2; rewrite join_dfa_accept_opt_r with (g1:=g1) in H1.
    auto.
    nia.
    apply some_state_in_states_opt, add_to_states_correct, some_state_in_states_opt; rewrite <- H2;
    apply start_in_states_opt.
Qed.

(* Decidability of equivalent DFAs *)
Lemma equivalent_dfas_dec g1 g2 :
  {equivalent_dfas g1 g2} + {~ equivalent_dfas g1 g2}.
Proof.
  destruct (distinguishable_states_dec (join_dfa g1 g2) (start g1) (add_to_start g2 (max_state g1 + 1))) as [H|H].
  right; intro H0; apply equivalent_joint_dfas in H0; auto.
  left; apply equivalent_joint_dfas; auto.
Qed.