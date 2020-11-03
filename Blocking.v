Require Import List DFA DistinguishableStates ReachableState NatListSet.

(* A blocking state is a state that no accept state is reachable from. *)
Definition blocking_state g q := forall w, accept_opt g (xtransition g q w) = false.

(* A state is blocking iff it is equivalent to the sink state (None). *)
Lemma equivalent_blocking_state_none g q :
  ~ distinguishable_states g q None <-> blocking_state g q.
Proof.
  split; intro H0.
  - intro w; assert (H1: accept_opt g (xtransition g q w) = true -> accept_opt g (xtransition g None w) = true).
      intro H1; apply equivalent_states with (q1:=q); auto.
    destruct (accept_opt g (xtransition g q w)).
    + destruct H1; try rewrite xtransition_none; auto.
    + auto.
  - intros [w [H1 _]]; specialize (H0 w); rewrite H0 in H1; discriminate.
Qed.

(* Decidability of blocking state *)
Theorem blocking_state_dec g q :
  {blocking_state g q} + {~ blocking_state g q}.
Proof.
  destruct (distinguishable_states_dec g q None) as [H0|H0].
  - right; intro H1; apply equivalent_blocking_state_none in H1; auto.
  - left; apply equivalent_blocking_state_none; auto.
Qed.

(*
  A DFA is said to be blocking if some w of its generated language is not a prefix of any w' in
  its marked/accept language (Cassandras, 2008).
*)
Definition blocking_dfa g := exists w, ixtransition g w <> None /\ ~ exists w', acceptsb g (w ++ w') = true.

(* A DFA is blocking iff any of its proper blocking states is reachable *)
Lemma blocking_dfa__blocking_states_reachable g :
  blocking_dfa g <-> exists q, In q (states g) /\ blocking_state g (Some q) /\ reachable_state g q.
Proof.
  unfold blocking_dfa, blocking_state, reachable_state, acceptsb, ixtransition; split.
  - intros [w [H H0]]; destruct (xtransition g (start g) w) as [q|] eqn:H1.
    2: destruct H; auto.
    exists q; split.
    + apply some_state_in_states_opt; rewrite <- H1; apply xtransition_in_states_opt, start_in_states_opt.
    + split.
      2: exists w; auto.
      intro w'; rewrite <- H1, <- xtransition_app; destruct (accept_opt g (xtransition g (start g) (w ++ w'))) eqn:H2.
      2: auto.
      assert (exists w', accept_opt g (xtransition g (start g) (w ++ w')) = true). exists w'; auto.
      contradiction.
  - intros [q [H [H0 [w H1]]]]; exists w; split.
    + rewrite H1; intro H2; discriminate.
    + intros [w' H2]; rewrite xtransition_app, H1 in H2; specialize (H0 w');
      rewrite H0 in H2; discriminate.
Qed.

(*
  Let P be a decidable proposition. We can decide whether there exists x in a given list l such
  that P x is true.
*)
Lemma ex_in_list_dec X l P :
  (forall x, {P x} + {~ P x}) ->
  {exists x:X, In x l /\ P x} + {~ exists x, In x l /\ P x}.
Proof.
  intro H; induction l as [|y l IH].
  - right; simpl; intros [_ [[] _]].
  - destruct IH as [IH|IH].
    + left; destruct IH as [x IH]; exists x; intuition.
    + specialize (H y); destruct H as [H|H].
      left; exists y; intuition.
      right; intros [x [[H0|H0] H1]].
      subst; contradiction.
      apply IH; exists x; intuition.
Qed.

(* Decidability of blocking DFA *)
Theorem blocking_dfa_dec g :
  {blocking_dfa g} + {~ blocking_dfa g}.
Proof.
  assert (H: {exists q, In q (states g) /\ blocking_state g (Some q) /\ reachable_state g q} +
  {~ exists q, In q (states g) /\ blocking_state g (Some q) /\ reachable_state g q}). {
    apply ex_in_list_dec; intro q; destruct (blocking_state_dec g (Some q)) as [H|H].
    - destruct (reachable_state_dec g q) as [H0|H0].
      + left; intuition.
      + right; intros [_ H1]; auto.
    - right; intros [H0 _]; auto.
  }
  destruct H as [H|H].
  - left; apply blocking_dfa__blocking_states_reachable; auto.
  - right; intro H0; apply blocking_dfa__blocking_states_reachable in H0; auto.
Qed.