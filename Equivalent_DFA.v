Require Import Nat PeanoNat List DFA Lia NatListSet DistinguishableState.
Import ListNotations.

Definition max_state g := max_in_list (states g).

Fixpoint add_dfa' g n :=
  match g with
  | state q accept::g => state (q + n) accept::add_dfa' g n
  | symbol a::g => symbol a::add_dfa' g n
  | transition q1 a q2::g => transition (q1 + n) a (q2 + n)::add_dfa' g n
  | nil => nil
  end.

Lemma add_dfa'_correct g n q w :
  accept_opt g (xtransition g (Some q) w) = accept_opt (add_dfa' g n) (xtransition (add_dfa' g n) (Some (q + n)) w).
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
    + replace (transitionf (add_dfa' g n) (q + n) a) with (Some (q' + n)).
      apply IH.
      clear IH; induction g as [|[q1 acc|b|q1 b q2] g IH]; simpl in *; try discriminate; auto.
      rewrite H0; destruct (andb (q =? q1) (a =? b));
      try (injection H; intros; subst); auto.
    + replace (transitionf (add_dfa' g n) (q + n) a) with (@None nat).
      rewrite xtransition_none, xtransition_none; auto.
      clear IH; induction g as [|[q1 acc|b|q1 b q2] g IH]; simpl in *; auto.
      rewrite H0; destruct (andb (q =? q1) (a =? b)); try discriminate; auto.
Qed.

Lemma add_dfa'_states g n q :
  In q (states g) -> In (q+n) (states (add_dfa' g n)).
Proof.
  intro H; induction g as [|[q1 acc|a|q1 a q2] g IH]; simpl in *.
  - contradiction.
  - apply add_correct in H; apply add_correct; destruct H as [H|H]; subst; intuition.
  - auto.
  - apply add_correct in H; apply add_correct; destruct H as [H|H].
    subst; intuition.
    right; apply add_correct in H; apply add_correct; destruct H as [H|H]; subst; intuition.
Qed.

Lemma add_dfa'_min_state g n q :
  In q (states (add_dfa' g n)) -> q >= n.
Proof.
  induction g as [|[q1 acc|a|q1 a q2] g IH].
  - contradiction.
  - simpl; intro H; apply add_correct in H; destruct H as [H|H]; try nia; auto.
  - auto.
  - simpl; intro H; apply add_correct in H; destruct H as [H|H];
    try (apply add_correct in H; destruct H as [H|H]); try nia;
    auto.
Qed.

Definition add_dfa'' g1 g2 n := g1 ++ add_dfa' g2 n.

Lemma add_dfa_transition1 g1 g2 n q a :
  n > max_state g1 ->
  In q (states g1) ->
  transitionf g1 q a = transitionf (add_dfa'' g1 g2 n) q a.
Proof.
  intros H H0; destruct (transitionf g1 q a) as [q3|] eqn:H1.
  - symmetry; apply transitionf_app; auto.
  - destruct (transitionf (add_dfa'' g1 g2 n) q a) as [q'|] eqn:H2; auto;
    apply app_transitionf in H2; destruct H2 as [H2|H2].
    + rewrite <- H1, <- H2; auto.
    + apply transition_states, add_dfa'_min_state in H2; unfold max_state in H; apply max_in_list_correct in H0;
      nia.
Qed.

Lemma add_dfa_correct1 g1 g2 n q w :
  n > max_state g1 ->
  In q (states_opt g1) ->
  accept_opt g1 (xtransition g1 q w) = accept_opt (add_dfa'' g1 g2 n) (xtransition (add_dfa'' g1 g2 n) q w).
Proof.
  intro H; revert q;
  induction w as [|a w IH]; intros q H0; simpl; destruct q as [q|]; auto.
  - simpl; destruct H0 as [H0|H0]; try discriminate; apply states_opt'_correct in H0;
    unfold add_dfa''; destruct (accept g1 q) eqn:H1.
    + symmetry; apply accept_app; auto.
    + destruct (accept (g1 ++ add_dfa' g2 n) q) eqn:H2; auto; apply app_accept in H2; destruct H2 as [H2|H2].
      rewrite <- H1, <- H2; auto.
      apply accept_state, add_dfa'_min_state in H2; unfold max_state in H; apply max_in_list_correct in H0;
      nia.
  - replace (transitionf (add_dfa'' g1 g2 n) q a) with (transitionf g1 q a).
    2: destruct H0 as [ |H0]; try discriminate; apply states_opt'_correct in H0;
    apply add_dfa_transition1; auto.
    apply IH, transition_state_opt.
Qed.


Lemma add_dfa_transition2 g1 g2 n q a :
  n > max_state g1 ->
  In q (states (add_dfa' g2 n)) ->
  transitionf (add_dfa' g2 n) q a = transitionf (add_dfa'' g1 g2 n) q a.
Proof.
  intros H H0; destruct (transitionf (add_dfa' g2 n) q a) as [q3|] eqn:H1.
  - symmetry; apply transitionf_app_r; destruct (in_dec Nat.eq_dec q (states g1)) as [H2|H2]; auto.
    apply add_dfa'_min_state in H0; unfold max_state in H; apply max_in_list_correct in H2; nia.
  - destruct (transitionf (add_dfa'' g1 g2 n) q a) as [q'|] eqn:H2; auto;
    apply app_transitionf in H2; destruct H2 as [H2|H2].
    + apply transition_states in H2; apply add_dfa'_min_state in H0; unfold max_state in H; apply max_in_list_correct in H2;
      nia.
    + rewrite <- H1, <- H2; auto.
Qed.

Lemma add_dfa_correct2 g1 g2 n q w :
  n > max_state g1 ->
  In q (states_opt (add_dfa' g2 n)) ->
  accept_opt (add_dfa' g2 n) (xtransition (add_dfa' g2 n) q w) = accept_opt (add_dfa'' g1 g2 n) (xtransition (add_dfa'' g1 g2 n) q w).
Proof.
  intro H; revert q;
  induction w as [|a w IH]; intros q H0; simpl; destruct q as [q|]; auto.
  - simpl; destruct H0 as [H0|H0]; try discriminate; apply states_opt'_correct in H0;
    unfold add_dfa''; destruct (accept (add_dfa' g2 n) q) eqn:H1.
    + symmetry; apply accept_app_r; destruct (in_dec Nat.eq_dec q (states g1)) as [H2|H2]; auto.
      apply accept_state, add_dfa'_min_state in H1;
      unfold max_state in H; apply max_in_list_correct in H2; nia.
    + destruct (accept (g1 ++ add_dfa' g2 n) q) eqn:H2; auto; apply app_accept in H2; destruct H2 as [H2|H2].
      2: rewrite <- H1, <- H2; auto.
      apply accept_state in H2; apply add_dfa'_min_state in H0;
      unfold max_state in H; apply max_in_list_correct in H2; nia.
  - replace (transitionf (add_dfa'' g1 g2 n) q a) with (transitionf (add_dfa' g2 n) q a).
    2: destruct H0 as [ |H0]; try discriminate; apply states_opt'_correct in H0;
    apply add_dfa_transition2; auto.
    apply IH, transition_state_opt.
Qed.

Definition add_dfa g1 g2 := add_dfa'' g1 g2 (max_state g1 + 1).

Definition equivalent_dfas g1 g2 := forall w,
  acceptsb g1 w = true -> acceptsb g2 w = true.

Definition start_plus g n :=
  match start g with
  | Some q => Some (q + n)
  | None => None
  end.

Lemma equivalent_dfas_added g1 g2 :
  ~ distinguishable_states (add_dfa g1 g2) (start g1) (start_plus g2 (max_state g1 + 1)) <->
  equivalent_dfas g1 g2.
Proof.
  split; intro H.
  - remember (add_dfa g1 g2) as g; remember (start g1) as q1; remember (start_plus g2 (max_state g1 + 1)) as q2.
    assert (H0: forall w, accept_opt g (xtransition g q1 w) = true -> accept_opt g (xtransition g q2 w) = true).
    apply equivalent_states; auto.
    subst; intros w H1; specialize (H0 w); unfold acceptsb, ixtransition in H1;
    rewrite add_dfa_correct1 with (g2:=g2) (n:=max_state g1 + 1) in H1.
    2: nia.
    2: apply start_in_states.
    apply H0 in H1; unfold acceptsb, ixtransition; unfold start_plus in H1; destruct (start g2) as [q|] eqn:H2.
    2: rewrite xtransition_none in H1; discriminate.
    rewrite add_dfa'_correct with (n:=max_state g1 + 1); rewrite add_dfa_correct2 with (g1:=g1).
    auto.
    nia.
    apply states_opt_correct.
    apply add_dfa'_states, states_opt'_correct; rewrite <- H2;
    pose proof (start_in_states g2) as H3; destruct H3 as [H3|H3]; auto;
    rewrite H2 in H3; discriminate.
  - unfold equivalent_dfas in H; apply equivalent_states; intros w H0; specialize (H w).
    assert (H1: accept_opt g1 (xtransition g1 (start g1) w) = true). {
      rewrite <- H0; apply add_dfa_correct1. nia. apply start_in_states.
    }
    apply H in H1; unfold acceptsb, ixtransition in H1; destruct (start g2) as [q|] eqn:H2.
    2: rewrite xtransition_none in H1; discriminate.
    rewrite add_dfa'_correct with (n:=max_state g1 + 1) in H1;
    unfold start_plus; rewrite H2; rewrite add_dfa_correct2 with (g1:=g1) in H1.
    auto.
    nia.
    apply states_opt_correct, add_dfa'_states, states_opt'_correct; rewrite <- H2;
    pose proof (start_in_states g2) as H3; destruct H3 as [H3|H3]; auto;
    rewrite H2 in H3; discriminate.
Qed.

Lemma dfa_app_state g1 g2 q :
  In q (states_opt g1) -> In q (states_opt (g1++g2)).
Proof.
  intro H; induction g1 as [|[q1 acc|a|q1 a q2] g1 IH]; simpl in *.
  - destruct H as [H|[]]; auto.
  - destruct H as [H|H]. intuition. destruct q as [q|]. 2: intuition.
    apply states_opt'_correct, add_correct in H; destruct H as [H|H].
    subst; right; apply states_opt'_correct, add_correct; intuition.
    destruct IH.
    + right; apply states_opt'_correct; auto.
    + intuition.
    + apply states_opt'_correct in H0; right; apply states_opt'_correct, add_correct;
      intuition.
  - auto.
  - destruct H as [H|H]. intuition. destruct q as [q|]. 2: intuition.
    apply states_opt'_correct, add_correct in H; destruct H as [H|H].
    subst; right; apply states_opt'_correct, add_correct; intuition.
    apply add_correct in H; destruct H as [H|H].
    subst; right; apply states_opt'_correct, add_correct; right; apply add_correct; intuition.
    destruct IH.
    + right; apply states_opt'_correct; auto.
    + intuition.
    + apply states_opt'_correct in H0; right; apply states_opt'_correct, add_correct;
      right; apply add_correct; right; auto.
Qed.

Lemma dfa_app_state_r g1 g2 q :
  In q (states_opt g2) -> In q (states_opt (g1++g2)).
Proof.
  destruct q as [q|].
  2: left; auto.
  intro H; apply states_opt_correct in H; apply states_opt_correct;
  induction g1 as [|[q1 acc|a|q1 a q2] g1 IH]; simpl in *; auto.
  - apply add_correct; intuition.
  - apply add_correct; right; apply add_correct; intuition.
Qed.

Lemma equivalent_dfas_dec g1 g2 :
  {equivalent_dfas g1 g2} + {~ equivalent_dfas g1 g2}.
Proof.
  destruct (distinguishable_states_dec (add_dfa g1 g2) (start g1) (start_plus g2 (max_state g1 + 1))) as [H|H].
  apply dfa_app_state, start_in_states.
  { apply dfa_app_state_r; unfold start_plus; pose proof (start_in_states g2); destruct (start g2) as [q|].
    apply states_opt_correct; apply states_opt_correct in H; apply add_dfa'_states; auto.
    left; auto. }
  right; intro H0; apply equivalent_dfas_added in H0; auto.
  left; apply equivalent_dfas_added; auto.
Qed.