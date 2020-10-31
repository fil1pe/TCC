Require Import Nat PeanoNat List DFA Digraph Lia NatListSet.
Import ListNotations.

Fixpoint state_pairs' (q:option nat) (l:list (option nat)) :=
  match l with
  | q'::l => edge (q,q') (q,q')::state_pairs' q l
  | nil => nil
  end.

Lemma state_pairs'_correct q1 l q2 :
  In q2 l -> In (edge (q1,q2) (q1,q2)) (state_pairs' q1 l).
Proof.
  revert q1 q2;
  induction l as [|q l IH]; intros q1 q2.
  - contradiction.
  - intros [H|H].
    + subst; left; auto.
    + right; apply IH; auto.
Qed.

Lemma state_pairs'_states l q1 q2 q3 q4 q :
  In (edge (q1, q2) (q3, q4)) (state_pairs' q l) ->
  q1 = q3 /\ q2 = q4.
Proof.
  revert q1 q2 q3 q4 q; induction l as [|q' l IH].
  - contradiction.
  - intros q1 q2 q3 q4 q [H|H].
    + injection H; intros; subst; auto.
    + apply IH in H; auto.
Qed.

Fixpoint state_pairs'' g l :=
  match l with
  | q::l => state_pairs' q (states_opt g) ++ state_pairs'' g l
  | nil => nil
  end.

Lemma state_pairs_correct g l q1 q2 :
  In q1 l -> In q2 (states_opt g) ->
  In (edge (q1,q2) (q1,q2)) (state_pairs'' g l).
Proof.
  revert q1 q2; induction l as [|q l IH]; intros q1 q2.
  - contradiction.
  - intros [H|H]; intro H0.
    + subst; apply in_or_app; left; apply state_pairs'_correct; auto.
    + simpl; right; apply in_or_app; right; apply IH; auto.
Qed. 

Lemma state_pairs_states g l q1 q2 q3 q4 :
  In (edge (q1, q2) (q3, q4)) (state_pairs'' g l) ->
  q1 = q3 /\ q2 = q4.
Proof.
  revert q1 q2 q3 q4; induction l as [|q l IH]; intros q1 q2 q3 q4.
  - contradiction.
  - intro H; replace (state_pairs'' g (q :: l)) with (state_pairs' q (states_opt g) ++ state_pairs'' g l) in H.
    2: auto.
    apply in_app_or in H; destruct H as [H|H].
    + apply state_pairs'_states in H; auto.
    + apply IH; auto.
Qed.

Definition state_pairs g := state_pairs'' g (states_opt g).

Fixpoint transition_edges g q1 q2 symbols :=
  match symbols with
  | a::symbols =>
    edge (q1, q2) (xtransition g q1 [a], xtransition g q2 [a])::transition_edges g q1 q2 symbols
  | nil => nil
  end.

Lemma transition_edges_states g q1 q2 q3 q4 Q1 Q2 l :
  In (edge (q1, q2) (q3, q4)) (transition_edges g Q1 Q2 l) ->
  Q1 = q1 /\ Q2 = q2.
Proof.
  intro H; induction l as [|a l IH].
  - contradiction.
  - destruct H as [H|H].
    + injection H; subst; auto.
    + apply IH; auto.
Qed.

Lemma transition_edges_correct' g q1 q2 q3 q4 l :
  In (edge (q1, q2) (q3, q4)) (transition_edges g q1 q2 l) <->
  exists a, In a l /\ xtransition g q1 [a] = q3 /\ xtransition g q2 [a] = q4.
Proof.
  induction l as [|a l IH]; split.
  - contradiction.
  - intros [_ [[] _]].
  - intros [H|H].
    + exists a; injection H; intuition.
    + apply IH in H; destruct H as [b H];
      exists b; intuition.
  - intros [b [[H|H] H0]].
    + left; destruct H0 as [H0 H1]; subst; auto.
    + right; apply IH; exists b; auto.
Qed.

Lemma ex_xtransition_undef g q1 q2 :
  exists a, xtransition g q1 [a] = None /\ xtransition g q2 [a] = None.
Proof.
  destruct q1 as [q1|], q2 as [q2|].
  - assert (H: exists a, ~ In a (alphabet g)). {
      exists (max_in_list (alphabet g) + 1); intro H;
      apply max_in_list_correct in H; nia.
    }
    destruct H as [a H]; exists a.
    replace (xtransition g (Some q1) [a]) with (transitionf g q1 a).
    2: simpl; destruct (transitionf g q1 a); auto.
    replace (xtransition g (Some q2) [a]) with (transitionf g q2 a).
    2: simpl; destruct (transitionf g q2 a); auto.
    destruct (transitionf g q1 a) eqn:H0, (transitionf g q2 a) eqn:H1.
    1,2: apply transition_alphabet in H0; contradiction.
    apply transition_alphabet in H1; contradiction.
    auto.
  - pose proof (ex_xtransition_undef g (Some q1)) as H; destruct H as [a H];
    exists a; split; auto.
  - pose proof (ex_xtransition_undef g (Some q2)) as H; destruct H as [a H];
    exists a; split; auto.
  - exists O; auto.
Qed.

Lemma transition_edges_correct g q1 q2 q3 q4 :
  In (edge (q1, q2) (q3, q4))
    (edge (q1, q2) (None, None)::transition_edges g q1 q2 (alphabet g)) <->
  exists a, xtransition g q1 [a] = q3 /\ xtransition g q2 [a] = q4.
Proof.
  split.
  - intros [H|H].
    + injection H; intros; subst; apply ex_xtransition_undef. 
    + apply transition_edges_correct' in H; destruct H as [a [_ H]];
      exists a; auto.
  - intros [a H]; destruct (in_dec Nat.eq_dec a (alphabet g)) as [H0|H0].
    + right; apply transition_edges_correct'; exists a; auto.
    + left; destruct H as [H H1]; pose proof H0 as H2;
      apply xtransition_not_in_alphabet with (q:=q1) in H0;
      apply xtransition_not_in_alphabet with (q:=q2) in H2;
      subst; rewrite H0, H2; auto.
Qed.

Fixpoint dfa_digraph' g q1 states : digraph :=
  match states with
  | q2::states => edge (q1, q2) (None, None)::transition_edges g q1 q2 (alphabet g) ++ dfa_digraph' g q1 states
  | nil => nil
  end.

Lemma dfa_digraph'_state g q1 q2 q3 q4 Q1 l :
  In (edge (q1, q2) (q3, q4)) (dfa_digraph' g Q1 l) ->
  Q1 = q1.
Proof.
  intro H; induction l as [|q l IH].
  - contradiction.
  - destruct H as [H|H].
    + injection H; intros; auto.
    + simpl in H; apply in_app_or in H; destruct H as [H|H];
      try (apply transition_edges_states in H); intuition.
Qed.

Lemma dfa_digraph'_correct g l q1 q2 q3 q4 :
  In (edge (q1, q2) (q3, q4)) (dfa_digraph' g q1 l) <->
  In q2 l /\ exists a, xtransition g q1 [a] = q3 /\ xtransition g q2 [a] = q4.
Proof.
  induction l as [|q l IH]; split.
  - contradiction.
  - intros [[] _].
  - intro H; replace (dfa_digraph' g q1 (q :: l)) with 
      ((edge (q1, q) (None, None)::transition_edges g q1 q (alphabet g)) ++ dfa_digraph' g q1 l) in H.
    2: auto.
    apply in_app_or in H; destruct H as [H|H].
    + assert (q = q2). {
        destruct H as [H|H].
        - injection H; intuition.
        - apply transition_edges_states in H; intuition.
      }
      subst; apply transition_edges_correct in H; intuition.
    + apply IH in H; intuition.
  - intro H; replace (dfa_digraph' g q1 (q :: l)) with 
      ((edge (q1, q) (None, None)::transition_edges g q1 q (alphabet g)) ++ dfa_digraph' g q1 l).
    2: auto.
    apply in_or_app; destruct H as [[H|H] H0].
    + subst; left; apply transition_edges_correct; auto.
    + right; apply IH; auto.
Qed.

Fixpoint dfa_digraph'' g l :=
  match l with
  | q::l => dfa_digraph' g q (states_opt g) ++ dfa_digraph'' g l
  | nil => nil
  end.

Lemma dfa_digraph''_correct g l q1 q2 q3 q4 :
  In (edge (q1, q2) (q3, q4)) (dfa_digraph'' g l) <->
  In q1 l /\ In q2 (states_opt g) /\
  exists a, xtransition g q1 [a] = q3 /\ xtransition g q2 [a] = q4.
Proof.
  induction l as [|q l IH]; split.
  - contradiction.
  - intros [[] _].
  - intro H; replace (dfa_digraph'' g (q :: l)) with
      (dfa_digraph' g q (states_opt g) ++ dfa_digraph'' g l) in H.
    2: auto.
    apply in_app_or in H; destruct H as [H|H].
    + assert (q = q1). apply dfa_digraph'_state in H; auto.
      subst; apply dfa_digraph'_correct in H; intuition.
    + apply IH in H; intuition.
  - intro H; replace (dfa_digraph'' g (q :: l)) with
      (dfa_digraph' g q (states_opt g) ++ dfa_digraph'' g l).
    2: auto.
    apply in_or_app; destruct H as [[H|H] H0].
    + subst; left; apply dfa_digraph'_correct; auto.
    + right; apply IH; auto.
Qed.

Definition dfa_digraph g := state_pairs g ++ (dfa_digraph'' g (states_opt g)).

Lemma dfa_digraph_reachable1 g p1 p2 :
  reachable (dfa_digraph g) p1 p2 ->
  exists w, xtransition g (fst p1) w = fst p2 /\ xtransition g (snd p1) w = snd p2.
Proof.
  remember (dfa_digraph g); intro H; apply reachable'_correct in H;
  induction H; destruct v1 as [q1 q2], v2 as [q3 q4]; subst;
  simpl fst in *; simpl snd in *.
  - apply in_app_or in H; destruct H as [H|H].
    + apply state_pairs_states in H; destruct H; subst;
      exists nil; simpl;
      destruct q3, q4; auto.
    + apply dfa_digraph''_correct in H; destruct H as [_ [_ [a H]]];
      exists [a]; auto.
  - destruct IHreachable'.
    auto.
    destruct H1 as [H1 H2]; destruct v3 as [q5 q6];
    apply in_app_or in H0; destruct H0 as [H0|H0].
    + apply state_pairs_states in H0; destruct H0; subst;
      exists x; auto.
    + apply dfa_digraph''_correct in H0; destruct H0 as [_ [_ [a [H0 H3]]]];
      exists (x ++ [a]); rewrite xtransition_app, xtransition_app; subst; auto.
Qed.

Lemma dfa_digraph_reachable2 g p1 p2 w :
  In (fst p1) (states_opt g) -> In (snd p1) (states_opt g) ->
  xtransition g (fst p1) w = fst p2 /\ xtransition g (snd p1) w = snd p2 ->
  reachable (dfa_digraph g) p1 p2.
Proof.
  intros H H0 H1; apply reachable'_correct;
  destruct p1 as [q1 q2], p2 as [q3 q4];
  simpl fst in *; simpl snd in *;
  generalize dependent q4; generalize dependent q3;
  generalize dependent q2; generalize dependent q1;
  induction w as [|b w IH] using rev_ind; intros q1 H q2 H0 q3 q4 H1.
  - apply reach_neigh', in_or_app; left.
    assert (q1 = q3). destruct H1 as [H1 _], q1, q3; auto.
    assert (q2 = q4). destruct H1 as [_ H1], q2, q4; auto.
    subst; apply state_pairs_correct; auto.
  - apply reach_trans' with (xtransition g q1 w, xtransition g q2 w).
    apply IH; auto.
    apply in_or_app; right; apply dfa_digraph''_correct; repeat split.
    1,2: apply xtransition_in_states_opt; auto.
    exists b; rewrite <- xtransition_app, <- xtransition_app; auto.
Qed.

Definition reachable_states g q1 q2 q3 q4 := exists w,
  xtransition g q1 w = q3 /\ xtransition g q2 w = q4.

Lemma reachable_states_dec g q1 q2 q3 q4 :
  In q1 (states_opt g) -> In q2 (states_opt g) ->
  {reachable_states g q1 q2 q3 q4} + {~ reachable_states g q1 q2 q3 q4}.
Proof.
  assert (pair_eq_decH: forall (x y: option nat * option nat), {x=y} + {x<>y}). {
    destruct x as [x1 x2], y as [y1 y2];
    destruct x1 as [x1|]; destruct y1 as [y1|]; destruct x2 as [x2|]; destruct y2 as [y2|];
    try (right; discriminate); try (destruct (Nat.eq_dec x1 y1)); try (destruct (Nat.eq_dec x2 y2));
    subst; auto;
    right; intro H; injection H; intros; subst; contradiction.
  }
  intros H H0; destruct (reachable_dec pair_eq_decH (dfa_digraph g) (q1, q2) (q3, q4)) as [H1|H1].
  - apply dfa_digraph_reachable1 in H1; auto.
  - right; intros [w H2]; assert (reachable (dfa_digraph g) (q1, q2) (q3, q4)).
    apply dfa_digraph_reachable2 with w; auto.
    contradiction.
Qed.

Definition reachable_statesf g q1 q2 q3 q4 :=
  match in_states_opt_dec g q1, in_states_opt_dec g q2 with
  | left H, left H0 =>
    if reachable_states_dec g q1 q2 q3 q4 H H0 then
      true
    else
      false
  | _, _ => false
  end.

Lemma reachable_statesf_correct g q1 q2 q3 q4 :
  reachable_statesf g q1 q2 q3 q4 = true <-> In q1 (states_opt g) /\ In q2 (states_opt g) /\
  reachable_states g q1 q2 q3 q4.
Proof.
  unfold reachable_statesf; split; intro H.
  - destruct (in_states_opt_dec g q1) as [H0|H0], (in_states_opt_dec g q2) as [H1|H1].
    2-4: discriminate.
    destruct (reachable_states_dec g q1 q2 q3 q4 H0 H1) as [H2|H2].
    2: discriminate.
    auto.
  - destruct H as [H [H0 H1]];
    destruct (in_states_opt_dec g q1) as [H2|H2], (in_states_opt_dec g q2) as [H3|H3].
    destruct (reachable_states_dec g q1 q2 q3 q4 H2 H3) as [H4|H4].
    2-5: contradiction.
    auto.
Qed.

Fixpoint distinguishable_statesf' g q1 q2 l :=
  match l with
  | edge (q3, q4) _::l =>
    orb (match accept_opt g q3, accept_opt g q4 with
        | true, false => reachable_statesf g q1 q2 q3 q4
        | _, _ => false
        end)
        (distinguishable_statesf' g q1 q2 l)
  | nil => false
  end.

Lemma distinguishable_statesf'_correct g q1 q2 l :
  In q1 (states_opt g) -> In q2 (states_opt g) ->
  distinguishable_statesf' g q1 q2 l = true <->
  exists w q5 q6,
    In (edge (xtransition g q1 w, xtransition g q2 w) (q5, q6)) l /\
    accept_opt g (xtransition g q1 w) = true /\ accept_opt g (xtransition g q2 w) = false.
Proof.
  intros H H0; induction l as [|e l IH]; split.
  - discriminate.
  - intros [_ [_ [_ [[] _]]]].
  - intro H1; simpl in H1; destruct (distinguishable_statesf' g q1 q2 l).
    + assert (H2: true = true). auto. apply IH in H2; destruct H2 as [w [q5 [q6 [H2 H3]]]];
      exists w, q5, q6; intuition.
    + destruct e as [[q3 q4] [q5 q6]]; destruct (accept_opt g q3) eqn:H2, (accept_opt g q4) eqn:H3;
      try discriminate; rewrite Bool.orb_false_r in H1; apply reachable_statesf_correct in H1;
      destruct H1 as [_ [_ [w [H1 H4]]]]; subst; exists w, q5, q6; intuition.
  - intros [w [q5 [q6 [[H1|H1] [H2 H3]]]]].
    + subst; simpl; rewrite H2, H3; assert (H4: reachable_statesf g q1 q2 (xtransition g q1 w) (xtransition g q2 w) = true).
      apply reachable_statesf_correct; repeat split; try (exists w); auto.
      rewrite H4; auto.
    + destruct e as [[q3 q4] [q7 q8]]; simpl; rewrite Bool.orb_comm; assert (H4: distinguishable_statesf' g q1 q2 l = true).
      apply IH; exists w, q5, q6; intuition.
      rewrite H4; auto.
Qed.

Definition distinguishable_states g q1 q2 := exists w,
  accept_opt g (xtransition g q1 w) = true /\ accept_opt g (xtransition g q2 w) = false.

Definition distinguishable_statesf g q1 q2 := distinguishable_statesf' g q1 q2 (state_pairs g).

Lemma distinguishable_statesf_correct {g q1 q2} :
  In q1 (states_opt g) -> In q2 (states_opt g) ->
  distinguishable_statesf g q1 q2 = true <-> distinguishable_states g q1 q2.
Proof.
  intros H H0; split.
  - intro H1; apply distinguishable_statesf'_correct in H1; auto;
    destruct H1 as [w [q5 [q6 [_ [H1 H2]]]]]; exists w; intuition.
  - intros [w [H1 H2]]; apply distinguishable_statesf'_correct; auto;
    exists w, (xtransition g q1 w), (xtransition g q2 w); split; auto;
    apply state_pairs_correct; apply xtransition_in_states_opt; auto.
Qed.

Theorem distinguishable_states_dec g q1 q2 :
  In q1 (states_opt g) -> In q2 (states_opt g) ->
  {distinguishable_states g q1 q2} + {~ distinguishable_states g q1 q2}.
Proof.
  intros H H0; destruct (distinguishable_statesf g q1 q2) eqn:H1.
  - apply (distinguishable_statesf_correct H H0) in H1; auto.
  - right; intro H2; apply (distinguishable_statesf_correct H H0) in H2;
    rewrite H1 in H2; discriminate.
Qed.

Theorem equivalent_states g q1 q2 :
  ~ distinguishable_states g q1 q2 <->
  forall w,
    accept_opt g (xtransition g q1 w) = true -> accept_opt g (xtransition g q2 w) = true.
Proof.
  split.
  - intros H w H0; destruct (accept_opt g (xtransition g q2 w)) eqn:H1; auto;
    assert (distinguishable_states g q1 q2). exists w; auto.
    contradiction.
  - intros H [w [H0 H1]]; apply H in H0; rewrite H0 in H1; discriminate.
Qed.