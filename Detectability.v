Require Import Nat PeanoNat List DFA Lia NatListSet Equivalent_DFA.
Import ListNotations.

Fixpoint projection unobservable w :=
  match w with
  | a::w =>
      if in_list a unobservable then
        projection unobservable w
      else
        a::projection unobservable w
  | nil => nil
  end.

Definition completely_undetectable g unobservable := forall w,
  acceptsb g w = true -> acceptsb g (projection unobservable w) = true.

Fixpoint loop q l :=
  match l with
  | a::l => transition q a q::loop q l
  | nil => nil
  end.

Lemma loop_observable_transition q q' unobservable a :
  in_list a unobservable = false -> transitionf (loop q' unobservable) q a = None.
Proof.
  intro H; induction unobservable as [|b l IH]; auto;
  simpl in *; rewrite Bool.andb_comm; assert (H0: b =? a = false).
  apply Bool.orb_false_elim in H; apply H.
  rewrite H0 in H; rewrite Nat.eqb_sym in H0; rewrite H0; auto.
Qed.

Fixpoint loop' l unobservable :=
  match l with
  | q::l => loop q unobservable ++ loop' l unobservable
  | nil => nil
  end.

Fixpoint remove_unobservable g unobservable :=
  match g with
  | transition q1 a q2::g =>
      if in_list a unobservable then
        state q1 (accept g q1)::state q2 (accept g q2)::remove_unobservable g unobservable
      else
        transition q1 a q2::remove_unobservable g unobservable
  | symbol a::g =>
      if in_list a unobservable then
        remove_unobservable g unobservable
      else
        symbol a::remove_unobservable g unobservable
  | e::g => e::remove_unobservable g unobservable
  | nil => nil
  end.

Lemma remove_unobservable_correct g a unobservable :
  In a unobservable -> ~ In a (alphabet (remove_unobservable g unobservable)).
Proof.
  induction g as [|[q acc|b|q1 b q2] g IH]; intro H.
  1,2: auto.
  1,2: simpl; destruct (in_list b unobservable) eqn:H0; auto;
    simpl; intro H1; apply add_correct in H1; destruct H1 as [H1|H1].
  2,4: intuition.
  1,2: subst; apply in_list_correct in H; rewrite H in H0; discriminate.
Qed.

Definition projection_dfa g unobservable := remove_unobservable g unobservable ++ loop' (states g) unobservable.

(*!!*)
Lemma transitionf_app_none_r g1 g2 q1 q2 a :
  transitionf g1 q1 a = None -> transitionf g2 q1 a = q2 -> transitionf (g1 ++ g2) q1 a = q2.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intros;
  try (destruct (andb (q1 =? q3) (a =? b))); try discriminate; auto.
Qed.

Lemma projection_dfa_unotransition g unobservable q a :
  In q (states g) ->
  in_list a unobservable = true ->
  transitionf (projection_dfa g unobservable) q a =
  Some q.
Proof.
  intros H H0; apply transitionf_app_none_r.
  destruct (transitionf (remove_unobservable g unobservable) q a) as [q'|] eqn:H1; auto;
  apply transition_alphabet in H1; apply in_list_correct, remove_unobservable_correct with (g:=g) in H0;
  contradiction.
  induction (states g) as [|q1 l IH]; try contradiction;
  simpl; destruct (Nat.eq_dec q1 q) as [H1|H1].
  subst; apply transitionf_app. {
    clear IH H l; induction unobservable as [|c l IH].
    - discriminate.
    - simpl; rewrite Nat.eqb_refl; apply in_list_correct in H0; destruct H0 as [H0|H0].
      + subst; rewrite Nat.eqb_refl; auto.
      + apply in_list_correct in H0; destruct (a =? c); auto.
  }
  destruct H as [H|H]; try contradiction.
  apply transitionf_app_r; auto; clear IH H H0 l a g;
  induction unobservable as [|c l IH].
  auto.
  simpl; intro H; apply add_correct in H; destruct H as [H|H];
  try (apply add_correct in H; destruct H as [H|H]); auto.
Qed.

(*!!*)
Lemma app_transitionf g1 g2 q1 q2 a :
  transitionf (g1 ++ g2) q1 a = q2 -> transitionf g1 q1 a = q2 \/ transitionf g2 q1 a = q2.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intro H;
  try (destruct (andb (q1 =? q3) (a =? b))); auto.
Qed.

(*!!*)
Lemma transitionf_app_none g1 g2 q1 q2 a :
  transitionf g1 q1 a = q2 -> transitionf g2 q1 a = None -> transitionf (g1 ++ g2) q1 a = q2.
Proof.
  induction g1 as [|[q3 acc|b|q3 b q4] g1 IH]; simpl; intros H H0; auto;
  try discriminate; try (destruct (andb (q1 =? q3) (a =? b))); subst; auto.
Qed.

Lemma projection_dfa_transition g unobservable q a :
  in_list a unobservable = false ->
  transitionf (projection_dfa g unobservable) q a =
  transitionf g q a.
Proof.
  intro H; apply transitionf_app_none.
  - induction g as [|[q1 acc|b|q1 b q2] g IH]; simpl;
    try (destruct (in_list b unobservable) eqn:H0); simpl; auto.
    + assert (H1: a =? b = false).
      apply Nat.eqb_neq; intro contra; subst; rewrite H in H0; discriminate.
      rewrite H1, Bool.andb_false_r; auto.
    + destruct (andb (q =? q1) (a =? b)); auto.
  - pose proof loop_observable_transition;
    induction g as [|[q1 acc|b|q1 b q2] g IH]; simpl; unfold add; auto.
    2: destruct (in_list q2 (states g)).
    3: simpl; destruct (orb (q2 =? q1) (in_list q1 (states g)));
        simpl; try (apply transitionf_app_none); try (apply transitionf_app_none); auto.
    1,2: destruct (in_list q1 (states g)); try (apply transitionf_app_none); auto.
Qed.

Lemma projection_dfa_xtransition g unobservable q w :
  In q (states_opt g) ->
  xtransition g q (projection unobservable w) =
  xtransition (projection_dfa g unobservable) q w.
Proof.
  revert q; induction w as [|a w IH].
  - auto.
  - intros q H0; simpl; destruct (in_list a unobservable) eqn:H.
    + rewrite IH; destruct q as [q|]; auto.
      2: apply xtransition_none.
      rewrite projection_dfa_unotransition; try (apply states_opt_correct); auto.
    + simpl; destruct q as [q|].
      2: auto.
      rewrite projection_dfa_transition; auto; apply IH, transition_state_opt.
Qed.

Lemma projection_dfa_start {g} unobservable :
  start g = start (projection_dfa g unobservable).
Proof.
  induction g as [|[q acc|b|q1 b q2] g IH]; unfold projection_dfa in *; simpl;
  try (destruct (in_list b unobservable)); auto.
Qed.

(*!!*)
Lemma accept_app_false g1 g2 q :
  accept g1 q = false -> accept g2 q = false -> accept (g1 ++ g2) q = false.
Proof.
  intros H H0; induction g1 as [|[q1 acc|b|q1 b q2] g1 IH]; simpl in *;
  try destruct (q =? q1); auto.
Qed.

Lemma projection_dfa_accepts g unobservable w :
  acceptsb g (projection unobservable w) = acceptsb (projection_dfa g unobservable) w.
Proof.
  unfold acceptsb, ixtransition; rewrite projection_dfa_xtransition, (projection_dfa_start unobservable);
  remember (xtransition (projection_dfa g unobservable) (start (projection_dfa g unobservable)) w) as q eqn:H;
  clear H. 2: apply start_in_states.
  unfold projection_dfa; assert (H: accept_opt (loop' (states g) unobservable) q = false). {
    induction (states g) as [|l q1 IH]; destruct q as [q|];
    simpl in *; try apply accept_app_false; auto;
    clear IH; induction unobservable; auto.
  }
  remember (loop' (states g) unobservable) as g2 eqn:H0; clear H0;
  induction g as [|[q1 acc|b|q1 a q2] g IH]; destruct q as [q|]; simpl in *; auto.
  - destruct (q =? q1); auto.
  - destruct (in_list b unobservable); simpl; auto.
  - destruct (in_list a unobservable); simpl; auto; destruct (q =? q1) eqn:H0.
    apply EqNat.beq_nat_true in H0; auto.
    destruct (q =? q2) eqn:H1;
    try apply EqNat.beq_nat_true in H1; auto.
Qed.

Theorem completely_undetectable_dec g unobservable :
  {completely_undetectable g unobservable} + {~ completely_undetectable g unobservable}.
Proof.
  destruct (equivalent_dfas_dec g (projection_dfa g unobservable)) as [H|H].
  - left; intros w H0; rewrite projection_dfa_accepts; auto.
  - right; intro H0; apply H; intros w H1; rewrite <- projection_dfa_accepts; auto.
Qed.