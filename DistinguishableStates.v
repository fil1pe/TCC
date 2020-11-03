Require Import Nat PeanoNat List NatListSet DFA Digraph Lia.
Import ListNotations.

(*
  Two states q1 and q2 are said to be unidirectionally distinguishable if there exists a word that
  q1 accepts but q2 does not. This means xtransition over at least one word w is not an accept
  state from q2 but is from q1.
*)

Definition distinguishable_states g q1 q2 := exists w,
  accept_opt g (xtransition g q1 w) = true /\ accept_opt g (xtransition g q2 w) = false.

(* state_pairs: edges connecting every pair of states to itself. *)

Fixpoint state_pairs_loop1 (q:option nat) (l:list (option nat)) :=
  match l with
  | q'::l => edge (q,q') (q,q')::state_pairs_loop1 q l
  | nil => nil
  end.

Fixpoint state_pairs_loop2 g l :=
  match l with
  | q::l => state_pairs_loop1 q (states_opt g) ++ state_pairs_loop2 g l
  | nil => nil
  end.

Definition state_pairs g := state_pairs_loop2 g (states_opt g).

(*
  We can construct a digraph whose vertices are all the pairs of states of the DFA and whose edges
  connect each pair (q1, q2) to (q3, q4) where q3 is the result of xtransition from q1 over [a] and
  q4 is the result of xtransition from q2 over [a], for every symbol a. That is what dfa_digraph
  does here.
*)

Fixpoint transition_edges g q1 q2 l :=
  match l with
  | a::l =>
    edge (q1, q2) (xtransition g q1 [a], xtransition g q2 [a])::transition_edges g q1 q2 l
  | nil => nil
  end.

Fixpoint transition_edges_states g q1 l : digraph :=
  match l with
  | q2::l => edge (q1, q2) (None, None)::transition_edges g q1 q2 (alphabet g) ++ transition_edges_states g q1 l
  | nil => nil
  end.

Fixpoint dfa_digraph_states g l :=
  match l with
  | q::l => transition_edges_states g q (states_opt g) ++ dfa_digraph_states g l
  | nil => nil
  end.

Definition dfa_digraph g := state_pairs g ++ (dfa_digraph_states g (states_opt g)).

(* Proof state_pairs is correct *)
Lemma state_pairs_correct g q1 q2 :
  In q1 (states_opt g) -> In q2 (states_opt g) ->
  In (edge (q1,q2) (q1,q2)) (state_pairs g).
Proof.
  assert (P: forall q1 q2 l, In q2 l -> In (edge (q1,q2) (q1,q2)) (state_pairs_loop1 q1 l)). {
    clear q1 q2; intros q1 q2 l; induction l as [|q l IH].
    - contradiction.
    - intros [H|H].
      + subst; left; auto.
      + right; apply IH; auto.
  }
  unfold state_pairs; remember (states_opt g) as l eqn:H;
  replace (In q2 l) with (In q2 (states_opt g)). 2: subst; auto.
  clear H; induction l as [|q l IH].
  - contradiction.
  - intros [H|H]; intro H0.
    + subst; apply in_or_app; left; apply P; auto.
    + simpl; right; apply in_or_app; right; apply IH; auto.
Qed.

(* If edge (q1, q2) (q3, q4) is in state_pairs then q1 = q3 and q2 = q4. *)
Lemma state_pairs_snd g q1 q2 q3 q4 :
  In (edge (q1, q2) (q3, q4)) (state_pairs g) ->
  q1 = q3 /\ q2 = q4.
Proof.
  assert (P: forall q1 q2 q3 q4 q l, In (edge (q1, q2) (q3, q4)) (state_pairs_loop1 q l) ->
  q1 = q3 /\ q2 = q4). {
    clear q1 q2 q3 q4; intros q1 q2 q3 q4 q l; induction l as [|q' l IH].
    - contradiction.
    - intros [H|H].
      + injection H; intros; subst; auto.
      + apply IH in H; auto.
  }
  unfold state_pairs; induction (states_opt g) as [|q l IH].
  - contradiction.
  - intro H; replace (state_pairs_loop2 g (q :: l)) with (state_pairs_loop1 q (states_opt g) ++ state_pairs_loop2 g l) in H.
    2: auto.
    apply in_app_or in H; destruct H as [H|H].
    + apply P in H; auto.
    + apply IH; auto.
Qed.

(*
  There always exists a term a such that xtransition from a given q1 over [a] and xtransition from
  a given q2 over [a] are both undefined.
*)
Lemma ex_xtransition_undef g q1 q2 :
  exists a, xtransition g q1 [a] = None /\ xtransition g q2 [a] = None.
Proof.
  destruct q1 as [q1|], q2 as [q2|].
  - assert (H: exists a, ~ In a (alphabet g)). {
      exists (max_in_list (alphabet g) + 1); intro H;
      apply leq_max_in_list in H; nia.
    }
    destruct H as [a H]; exists a.
    replace (xtransition g (Some q1) [a]) with (transitionf g q1 a).
    2: simpl; destruct (transitionf g q1 a); auto.
    replace (xtransition g (Some q2) [a]) with (transitionf g q2 a).
    2: simpl; destruct (transitionf g q2 a); auto.
    destruct (transitionf g q1 a) eqn:H0, (transitionf g q2 a) eqn:H1.
    1,2: apply transitionf_defined in H0; destruct H0 as [_ H0]; contradiction.
    apply transitionf_defined in H1; destruct H1 as [_ H1]; contradiction.
    auto.
  - pose proof (ex_xtransition_undef g (Some q1)) as H; destruct H as [a H];
    exists a; split; auto.
  - pose proof (ex_xtransition_undef g (Some q2)) as H; destruct H as [a H];
    exists a; split; auto.
  - exists O; auto.
Qed.

(*
  If a given pair (q3, q4) is a neighbor of a given pair (q1, q2) in the digraph applied to a given
  list l, then q1 is in l, q2 is in states or None and there exists a symbol a such that
  xtransition from q1 over [a] results in q2 and xtransition from q2 over w results in q4.
*)
Lemma dfa_digraph_states_neighbor g q1 q2 q3 q4 l :
  In (edge (q1, q2) (q3, q4)) (dfa_digraph_states g l) <->
  In q1 l /\ In q2 (states_opt g) /\
  exists a, xtransition g q1 [a] = q3 /\ xtransition g q2 [a] = q4.
Proof.
  assert (P2: forall q1 q2 q3 q4 Q1 Q2 l, In (edge (q1, q2) (q3, q4)) (transition_edges g Q1 Q2 l) -> Q1 = q1 /\ Q2 = q2). {
    clear q1 q2 q3 q4 l; intros q1 q2 q3 q4 Q1 Q2 l H; induction l as [|a l IH].
    - contradiction.
    - destruct H as [H|H].
      + injection H; subst; auto.
      + apply IH; auto.
  }

  assert (P: forall q1 q2 q3 q4,
  In (edge (q1, q2) (q3, q4)) (edge (q1, q2) (None, None)::transition_edges g q1 q2 (alphabet g)) <->
  exists a, xtransition g q1 [a] = q3 /\ xtransition g q2 [a] = q4). {
    clear q1 q2 q3 q4 l; assert (P: forall q1 q2 q3 q4 l, In (edge (q1, q2) (q3, q4)) (transition_edges g q1 q2 l) <->
    exists a, In a l /\ xtransition g q1 [a] = q3 /\ xtransition g q2 [a] = q4). {
      intros q1 q2 q3 q4 l; induction l as [|a l IH]; split.
      - contradiction.
      - intros [_ [[] _]].
      - intros [H|H].
        + exists a; injection H; intuition.
        + apply IH in H; destruct H as [b H];
          exists b; intuition.
      - intros [b [[H|H] H0]].
        + left; destruct H0 as [H0 H1]; subst; auto.
        + right; apply IH; exists b; auto.
    }
    intros q1 q2 q3 q4; split.
    - intros [H|H].
      + injection H; intros; subst; apply ex_xtransition_undef. 
      + apply P in H; destruct H as [a [_ H]]; exists a; auto.
    - intros [a H]; destruct (in_dec Nat.eq_dec a (alphabet g)) as [H0|H0].
      + right; apply P; exists a; auto.
      + left; destruct H as [H H1]; pose proof H0 as H2;
        apply xtransition_not_in_alphabet with (q:=q1) in H0;
        apply xtransition_not_in_alphabet with (q:=q2) in H2;
        subst; rewrite H0, H2; auto.
  }

  assert (P0: forall q1 q2 q3 q4 Q l, In (edge (q1, q2) (q3, q4)) (transition_edges_states g Q l) ->
  Q = q1). {
    clear q1 q2 q3 q4 l; intros q1 q2 q3 q4 Q l H; induction l as [|q l IH].
    - contradiction.
    - destruct H as [H|H].
      + injection H; intros; auto.
      + simpl in H; apply in_app_or in H; destruct H as [H|H];
        try (apply P2 in H); intuition.
  }

  assert (P1: forall q1 q2 q3 q4 l, In (edge (q1, q2) (q3, q4)) (transition_edges_states g q1 l) <->
  In q2 l /\ exists a, xtransition g q1 [a] = q3 /\ xtransition g q2 [a] = q4). {
    clear q1 q2 q3 q4 l; intros q1 q2 q3 q4 l; induction l as [|q l IH]; split.
    - contradiction.
    - intros [[] _].
    - intro H; replace (transition_edges_states g q1 (q :: l)) with 
        ((edge (q1, q) (None, None)::transition_edges g q1 q (alphabet g)) ++ transition_edges_states g q1 l) in H.
      2: auto.
      apply in_app_or in H; destruct H as [H|H].
      + assert (q = q2). {
          destruct H as [H|H].
          - injection H; intuition.
          - apply P2 in H; intuition.
        }
        subst; apply P in H; intuition.
      + apply IH in H; intuition.
    - intro H; replace (transition_edges_states g q1 (q :: l)) with 
        ((edge (q1, q) (None, None)::transition_edges g q1 q (alphabet g)) ++ transition_edges_states g q1 l).
      2: auto.
      apply in_or_app; destruct H as [[H|H] H0].
      + subst; left; apply P; auto.
      + right; apply IH; auto.
  }

  induction l as [|q l IH]; split.
  - contradiction.
  - intros [[] _].
  - intro H; replace (dfa_digraph_states g (q :: l)) with
      (transition_edges_states g q (states_opt g) ++ dfa_digraph_states g l) in H.
    2: auto.
    apply in_app_or in H; destruct H as [H|H].
    + assert (q = q1). apply P0 in H; auto.
      subst; apply P1 in H; intuition.
    + apply IH in H; intuition.
  - intro H; replace (dfa_digraph_states g (q :: l)) with
      (transition_edges_states g q (states_opt g) ++ dfa_digraph_states g l).
    2: auto.
    apply in_or_app; destruct H as [[H|H] H0].
    + subst; left; apply P1; auto.
    + right; apply IH; auto.
Qed.

(*
  Given pairs (q1, q2) and (q3, q4), if (q3, q4) is reachable from (q1, q2) in the digraph, then
  exists w such that xtransition from q1 over w results in q3 and xtransition from q2 over w
  results in q4.
*)
Lemma reachable_dfa_digraph g p1 p2 :
  reachable (dfa_digraph g) p1 p2 ->
  exists w, xtransition g (fst p1) w = fst p2 /\ xtransition g (snd p1) w = snd p2.
Proof.
  remember (dfa_digraph g); intro H; apply reachable'_correct in H;
  induction H; destruct v1 as [q1 q2], v2 as [q3 q4]; subst;
  simpl fst in *; simpl snd in *.
  - apply in_app_or in H; destruct H as [H|H].
    + apply state_pairs_snd in H; destruct H; subst;
      exists nil; simpl;
      destruct q3, q4; auto.
    + apply dfa_digraph_states_neighbor in H; destruct H as [_ [_ [a H]]];
      exists [a]; auto.
  - destruct IHreachable'.
    auto.
    destruct H1 as [H1 H2]; destruct v3 as [q5 q6];
    apply in_app_or in H0; destruct H0 as [H0|H0].
    + apply state_pairs_snd in H0; destruct H0; subst;
      exists x; auto.
    + apply dfa_digraph_states_neighbor in H0; destruct H0 as [_ [_ [a [H0 H3]]]];
      exists (x ++ [a]); rewrite xtransition_app, xtransition_app; subst; auto.
Qed.

(*
  Given pairs (q1, q2) and (q3, q4) and word w, if q1 and q2 are states or None, xtransition from
  q1 over w results in q3 and xtransition from q2 over w results in q4, then (q3, q4) is reachable
  from (q1, q2) in the digraph.
*)
Lemma dfa_digraph_reachable g p1 p2 w :
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
  - apply reach'_neigh, in_or_app; left.
    assert (q1 = q3). destruct H1 as [H1 _], q1, q3; auto.
    assert (q2 = q4). destruct H1 as [_ H1], q2, q4; auto.
    subst; apply state_pairs_correct; auto.
  - apply reach'_ind with (xtransition g q1 w, xtransition g q2 w).
    apply IH; auto.
    apply in_or_app; right; apply dfa_digraph_states_neighbor; repeat split.
    1,2: apply xtransition_in_states_opt; auto.
    exists b; rewrite <- xtransition_app, <- xtransition_app; auto.
Qed.

(*
  Given terms q1, q2, q3 and q4, q1 and q2 are respectively reachable from q3 and q4 if there
  exists a word w such that xtransition from q1 over w results in q3, and xtransition from q2 over
  w results in q4.
*)
Definition reachable_states g q1 q2 q3 q4 := exists w,
  xtransition g q1 w = q3 /\ xtransition g q2 w = q4.

(* Decidability of reachable states *)
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
  - apply reachable_dfa_digraph in H1; auto.
  - right; intros [w H2]; assert (reachable (dfa_digraph g) (q1, q2) (q3, q4)).
    apply dfa_digraph_reachable with w; auto.
    contradiction.
Qed.

(* Now we can define a function that checks if two given terms are proper distinguishable states. *)

Definition reachable_statesf g q1 q2 q3 q4 :=
  match in_states_opt_dec g q1, in_states_opt_dec g q2 with
  | left H, left H0 =>
    if reachable_states_dec g q1 q2 q3 q4 H H0 then
      true
    else
      false
  | _, _ => false
  end.

Fixpoint distinguishable_statesf_loop g q1 q2 l :=
  match l with
  | edge (q3, q4) _::l =>
    orb (match accept_opt g q3, accept_opt g q4 with
        | true, false => reachable_statesf g q1 q2 q3 q4
        | _, _ => false
        end)
        (distinguishable_statesf_loop g q1 q2 l)
  | nil => false
  end.

Definition distinguishable_statesf g q1 q2 := distinguishable_statesf_loop g q1 q2 (state_pairs g).

(*
  Given q1 and q2, if they are both states or None, distinguishable_statesf applied to them must
  return true iff q1 and q2 are distinguishable states.
*)
Lemma distinguishable_statesf_correct g q1 q2 :
  In q1 (states_opt g) -> In q2 (states_opt g) ->
  distinguishable_statesf g q1 q2 = true <-> distinguishable_states g q1 q2.
Proof.
  assert (P: forall q1 q2 l, In q1 (states_opt g) -> In q2 (states_opt g) ->
  distinguishable_statesf_loop g q1 q2 l = true <->
  exists w q5 q6, In (edge (xtransition g q1 w, xtransition g q2 w) (q5, q6)) l /\
  accept_opt g (xtransition g q1 w) = true /\ accept_opt g (xtransition g q2 w) = false). {
    clear q1 q2; assert (P: forall q1 q2 q3 q4, reachable_statesf g q1 q2 q3 q4 = true <-> In q1 (states_opt g) /\ In q2 (states_opt g) /\
    reachable_states g q1 q2 q3 q4). {
      intros q1 q2 q3 q4; unfold reachable_statesf; split; intro H.
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
    }
    intros q1 q2 l H H0; induction l as [|e l IH]; split.
    - discriminate.
    - intros [_ [_ [_ [[] _]]]].
    - intro H1; simpl in H1; destruct (distinguishable_statesf_loop g q1 q2 l).
      + assert (H2: true = true). auto. apply IH in H2; destruct H2 as [w [q5 [q6 [H2 H3]]]];
        exists w, q5, q6; intuition.
      + destruct e as [[q3 q4] [q5 q6]]; destruct (accept_opt g q3) eqn:H2, (accept_opt g q4) eqn:H3;
        try discriminate; rewrite Bool.orb_false_r in H1; apply P in H1;
        destruct H1 as [_ [_ [w [H1 H4]]]]; subst; exists w, q5, q6; intuition.
    - intros [w [q5 [q6 [[H1|H1] [H2 H3]]]]].
      + subst; simpl; rewrite H2, H3; assert (H4: reachable_statesf g q1 q2 (xtransition g q1 w) (xtransition g q2 w) = true).
        apply P; repeat split; try (exists w); auto.
        rewrite H4; auto.
      + destruct e as [[q3 q4] [q7 q8]]; simpl; rewrite Bool.orb_comm; assert (H4: distinguishable_statesf_loop g q1 q2 l = true).
        apply IH; exists w, q5, q6; intuition.
        rewrite H4; auto.
  }
  intros H H0; split.
  - intro H1; apply P in H1; auto;
    destruct H1 as [w [q5 [q6 [_ [H1 H2]]]]]; exists w; intuition.
  - intros [w [H1 H2]]; apply P; auto;
    exists w, (xtransition g q1 w), (xtransition g q2 w); split; auto;
    apply state_pairs_correct; apply xtransition_in_states_opt; auto.
Qed.

(* Equivalent states: q2 accepts every word q1 accepts. *)
Theorem equivalent_states g q1 q2 :
  ~ distinguishable_states g q1 q2 <->
  forall w, accept_opt g (xtransition g q1 w) = true -> accept_opt g (xtransition g q2 w) = true.
Proof.
  split.
  - intros H w H0; destruct (accept_opt g (xtransition g q2 w)) eqn:H1; auto;
    assert (distinguishable_states g q1 q2). exists w; auto.
    contradiction.
  - intros H [w [H0 H1]]; apply H in H0; rewrite H0 in H1; discriminate.
Qed.

(*
  If two states q1 and q2 are bidirectionally equivalent, q3 and q1 are distinguishable iff q3 and
  q2 are also distinguishable.
*)
Lemma distinguishable_equivalent g q1 q2 q3 :
  ~ distinguishable_states g q1 q2 -> ~ distinguishable_states g q2 q1 ->
  distinguishable_states g q3 q1 <-> distinguishable_states g q3 q2.
Proof.
  intros H0 H1; assert (H: forall w, accept_opt g (xtransition g q1 w) = true <-> accept_opt g (xtransition g q2 w) = true).
    intro w; split; apply equivalent_states; auto.
  clear H0 H1; unfold distinguishable_states; split; intros [w [H0 H1]]; specialize (H w).
  - exists w; split.
    auto.
    destruct (accept_opt g (xtransition g q2 w)). 2: auto.
    destruct H as [_ H]; destruct H; auto.
  - exists w; split.
    auto.
    destruct (accept_opt g (xtransition g q1 w)). 2: auto.
    destruct H as [H _]; destruct H; auto.
Qed.

(*
  If two states q1 and q2 are bidirectionally equivalent, q1 and q3 are distinguishable iff q2 and
  q3 are also distinguishable.
*)
Lemma distinguishable_equivalent_r g q1 q2 q3 :
  ~ distinguishable_states g q1 q2 -> ~ distinguishable_states g q2 q1 ->
  distinguishable_states g q1 q3 <-> distinguishable_states g q2 q3.
Proof.
  intros H0 H1; assert (H: forall w, accept_opt g (xtransition g q1 w) = true <-> accept_opt g (xtransition g q2 w) = true).
    intro w; split; apply equivalent_states; auto.
  clear H0 H1; unfold distinguishable_states; split; intros [w [H0 H1]]; specialize (H w).
  - exists w; split.
    apply H; auto.
    destruct (accept_opt g (xtransition g q2 w)). 2: auto.
    destruct H as [_ H]; destruct H; auto.
  - exists w; split.
    apply H; auto.
    destruct (accept_opt g (xtransition g q1 w)). 2: auto.
    destruct H as [H _]; destruct H; auto.
Qed.

(* If a given q is not a state or None, it is bidirectionally equivalent to None. *)
Lemma not_in_states_opt__none g q :
  ~ In q (states_opt g) -> ~ distinguishable_states g q None /\ ~ distinguishable_states g None q.
Proof.
  intro H; split; apply equivalent_states; intros w H0; destruct w as [|a w].
  3,4: discriminate.
  - simpl xtransition in H0; destruct q as [q|].
    apply accept_in_states, some_state_in_states_opt in H0; contradiction.
    simpl in H0; discriminate.
  - simpl in H0; destruct q as [q|].
    2: assert (In None (states_opt g)); try left; auto.
    destruct (transitionf g q a) as [q'|] eqn:H1.
    2: rewrite xtransition_none in H0; discriminate.
    apply transitionf_defined in H1; destruct H1 as [H1 _]; apply some_state_in_states_opt in H1;
    auto.
Qed.

(* Decidability of distinguishable states *)
Theorem distinguishable_states_dec g q1 q2 :
  {distinguishable_states g q1 q2} + {~ distinguishable_states g q1 q2}.
Proof.
  destruct (in_states_opt_dec g q1) as [H|H]; destruct (in_states_opt_dec g q2) as [H0|H0].
  - destruct (distinguishable_statesf g q1 q2) eqn:H1.
    + apply (distinguishable_statesf_correct g q1 q2 H H0) in H1; auto.
    + right; intro H2; apply (distinguishable_statesf_correct g q1 q2 H H0) in H2;
      rewrite H1 in H2; discriminate.
  - destruct (distinguishable_statesf g q1 None) eqn:H1.
    + apply (distinguishable_statesf_correct g q1 None H) in H1.
      2: left; auto.
      left; apply distinguishable_equivalent with (q1:=None); apply not_in_states_opt__none in H0; intuition.
    + right; intro H2; pose proof (distinguishable_equivalent g None q2 q1) as H3; destruct H3.
      1,2: apply not_in_states_opt__none in H0; intuition.
      apply H4 in H2; apply distinguishable_statesf_correct in H2.
      rewrite H1 in H2; discriminate.
      auto.
      left; auto.
  - destruct (distinguishable_statesf g None q2) eqn:H1.
    + apply (distinguishable_statesf_correct g None q2) in H1.
      2: left; auto.
      2: auto.
      left; apply distinguishable_equivalent_r with (q1:=None); apply not_in_states_opt__none in H; intuition.
    + right; intro H2; pose proof (distinguishable_equivalent_r g None q1 q2) as H3; destruct H3.
      1,2: apply not_in_states_opt__none in H; intuition.
      apply H4 in H2; apply distinguishable_statesf_correct in H2.
      rewrite H1 in H2; discriminate.
      left; auto.
      auto.
  - destruct q1 as [q1|].
    2: intuition; destruct H; left; auto.
    right; apply equivalent_states; intros w H1; destruct w as [|a w].
    + apply accept_in_states, some_state_in_states_opt in H1; auto.
    + simpl in H1; destruct (transitionf g q1 a) as [q1'|] eqn:H2.
      2: rewrite xtransition_none in H1; discriminate.
      apply transitionf_defined in H2; destruct H2 as [H2 _]; apply some_state_in_states_opt in H2;
      auto.
Qed.