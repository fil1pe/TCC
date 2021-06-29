Require Import List Bool Lia sets nfa dfa normalizing.
Include ListNotations.


Fixpoint loop {A B} eq eq' (g:nfa_comp_list A B) f Q l :=
  match l with
  | nil => nil
  | a::l => match (ext_transition eq eq' g Q [a]) with
            | nil => loop eq eq' g f Q l
            | Q' => trans Q a Q'::f Q' ++ loop eq eq' g f Q l
            end
  end.

Lemma loop_in {A B} eq eq' (g:nfa_comp_list A B) f Q l a :
  In a l -> ext_transition eq eq' g Q [a] <> nil ->
  In (trans Q a (ext_transition eq eq' g Q [a])) (loop eq eq' g f Q l).
Proof.
  intros; induction l.
  1: destruct H.
  Opaque ext_transition.
  simpl; destruct (ext_transition eq eq' g Q [a]) eqn:H1.
  1: destruct H0; auto.
  destruct H.
  - subst; destruct (ext_transition eq eq' g Q [a]).
    1: discriminate.
    injection H1; intros; subst; intuition.
  - apply IHl in H.
    destruct (ext_transition eq eq' g Q [a0]).
    2: right; apply in_or_app; right.
    1,2: auto.
  Transparent ext_transition.
Qed.

Lemma in_loop {A B} eq eq' (g:nfa_comp_list A B) f Q l c :
  In c (loop eq eq' g f Q l) ->
  exists Q' a, In a l /\ Q' <> nil /\ Q' = ext_transition eq eq' g Q [a] /\
  In c (trans Q a Q'::f Q').
Proof.
  Opaque ext_transition.
  intros.
  induction l as [|b l].
  1: destruct H.
  simpl in H; destruct (ext_transition eq eq' g Q [b]) eqn:H0.
  1: apply IHl in H; destruct H as [Q' [a H]]; exists Q', a; intuition.
  replace (In c (trans Q b (a :: l0) :: f (a :: l0) ++ loop eq eq' g f Q l)) with
  (In c ((trans Q b (a :: l0) :: f (a :: l0)) ++ loop eq eq' g f Q l)) in H.
  2: auto.
  apply in_app_or in H; destruct H.
  - exists (a::l0), b; repeat split.
    1,3,4: intuition.
    intros contra; discriminate.
  - apply IHl in H; destruct H as [Q' [d H]]; exists Q', d; intuition.
  Transparent ext_transition.
Qed.

Lemma next_in_loop {A B} eq eq' (g:nfa_comp_list A B) f Q l a c :
  ext_transition eq eq' g Q [a] <> nil ->
  In a l ->
  In c (f (ext_transition eq eq' g Q [a])) ->
  In c (loop eq eq' g f Q l).
Proof.
  Opaque ext_transition.
  intros; induction l; destruct H0.
  - subst.
    simpl; destruct (ext_transition eq eq' g Q [a]).
    1: destruct H; auto.
    right; apply in_or_app; intuition.
  - simpl; destruct (ext_transition eq eq' g Q [a0]).
    1: intuition.
    right; apply in_or_app; intuition.
  Transparent ext_transition.
Qed.


Fixpoint n2dfa_trans {A B} eq eq' (g:nfa_comp_list A B) n Q :=
  match n with
  | O => nil
  | S n =>
    loop eq eq' g (n2dfa_trans eq eq' g n) Q (alphabet g)
  end.

Lemma trans_in_n2dfa_trans {A B} eq eq' (g:nfa_comp_list A B) Q0 Q Q' n a :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In (trans Q a Q') (n2dfa_trans eq eq' g n Q0) ->
  In a (alphabet g) /\ Q' <> nil /\ Q' = ext_transition eq eq' g Q [a].
Proof.
  intros;
  generalize dependent Q0;
  induction n; intros.
  1: destruct H0.
  simpl in H0; apply in_loop in H0; destruct H0 as [Q0' [b [H0 [H1 [H2 [H3|H3]]]]]].
  2: apply IHn in H3; clear IHn; auto.
  clear IHn; injection H3; intros; subst; split.
  2: split.
  1,2: auto.
  split; auto.
Qed.

Lemma trans_in_n2dfa_trans_eq {A B} eq eq' (g:nfa_comp_list A B) Q0 Q Q' n a :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In (trans Q a Q') (n2dfa_trans eq eq' g n Q0) ->
  In a (alphabet g) /\ Q' <> nil /\ eq_sets Q' (ext_transition eq eq' g Q [a]).
Proof.
  intros; apply trans_in_n2dfa_trans in H0.
  2: auto.
  destruct H0 as [H0 [H1 H2]]; subst; split.
  2: split.
  1,2: auto.
  apply eq_sets_self.
Qed.

Lemma n2dfa_trans_old_path {A B} eq eq' (g:nfa_comp_list A B) n w Q Q' q' :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  In q' Q' -> path (n2dfa_trans eq eq' g n Q) Q Q' w ->
  exists q, In q Q /\ path g q q' w.
Proof.
  intros.
  generalize dependent q';
  induction H2; intros.
  1: exists q'; intuition; constructor.
  apply trans_in_n2dfa_trans_eq in H1.
  2: auto.
  destruct H1 as [H1 [_ H4]].
  assert (In q' (ext_transition eq eq' g  q2 [a])).
    apply H4; auto.
  apply in_transition_ext in H5.
  2,3: auto.
  destruct H5 as [q'' [H5 H6]].
  apply IHpath in H5; destruct H5 as [q H5].
  exists q; split.
  2: apply path_next with q''.
  1-3: intuition.
Qed.

Lemma n2dfa_trans_new_path {A B} eq eq' (g:nfa_comp_list A B) n w Q q q' :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  length w <= n -> In q Q -> path g q q' w ->
  exists Q', In q' Q' /\ path (n2dfa_trans eq eq' g n Q) Q Q' w.
Proof.
  generalize dependent w;
  generalize dependent q;
  generalize dependent Q;
  induction n; intros.
  - assert (w = []).
      destruct w; inversion H1; auto.
    subst.
    inversion H3; subst.
    2: destruct w; discriminate.
    exists Q; split.
    2: constructor.
    auto.
  - destruct w as [|a w].
    + inversion H3; subst.
      2: destruct w; discriminate.
      exists Q; split.
      2: constructor.
      auto.
    + assert (exists q'', In (trans q a q'') g /\ path g q'' q' w).
        apply path_left; auto.
      destruct H4 as [q'' H4].
      destruct IHn with (ext_transition eq eq' g Q [a]) q'' w.
      1,2,5: intuition.
      1: simpl in H1; lia.
      {
        induction Q.
        1: destruct H2.
        destruct H2; simpl.
        1: subst; apply in_or_app; left; apply transition_in; intuition.
        apply in_or_app; right; intuition.
      }
      Opaque ext_transition.
      simpl n2dfa_trans.
      assert (In a (alphabet g)).
        apply trans_in_alphabet with q q''; intuition.
      clear IHn; exists x; split.
      1: intuition.
      assert (ext_transition eq eq' g Q [a] <> nil). {
        assert (In q'' (ext_transition eq eq' g Q [a])).
          apply transition_in_ext with q; intuition.
        destruct (ext_transition eq eq' g Q [a]).
        1: destruct H7.
        intros contra; discriminate.
      }
      apply path_left with (ext_transition eq eq' g Q [a]).
      1: apply loop_in; auto.
      subst; induction (alphabet g).
      1: destruct H6.
      simpl loop; subst.
      destruct H6.
      * subst; clear IHl; destruct (ext_transition eq eq' g Q [a]) eqn:H8.
        1: destruct H7; auto.
        replace (trans Q a (a0 :: l0) :: n2dfa_trans eq eq' g n (a0 :: l0) ++ loop eq eq' g (n2dfa_trans eq eq' g n) Q l)
        with ([trans Q a (a0 :: l0)] ++ n2dfa_trans eq eq' g n (a0 :: l0) ++ loop eq eq' g (n2dfa_trans eq eq' g n) Q l).
        2: auto.
        apply path_app; right; apply path_app; left; intuition.
      * destruct (ext_transition eq eq' g Q [a0]).
        1: intuition.
        replace (trans Q a0 (a1 :: l0) :: n2dfa_trans eq eq' g n (a1 :: l0) ++ loop eq eq' g (n2dfa_trans eq eq' g n) Q l)
        with ([trans Q a0 (a1 :: l0)] ++ n2dfa_trans eq eq' g n (a1 :: l0) ++ loop eq eq' g (n2dfa_trans eq eq' g n) Q l).
        2: auto.
        apply path_app; right; apply path_app; right; intuition.
      Transparent ext_transition.
Qed.

Lemma in_n2dfa_trans {A B} eq eq' (g:nfa_comp_list A B) n :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  forall Q c, subset Q (states g) -> In c (n2dfa_trans eq eq' g n Q) ->
  exists Q1 a Q2, c = trans Q1 a Q2 /\ subset Q1 (states g) /\ subset Q2 (states g).
Proof.
  intros H10;
  induction n; intros.
  1: destruct H0.
  simpl in H0; apply in_loop in H0; destruct H0 as [Q' [a [H0 [H1 [H2 [H3|H3]]]]]].
  - exists Q, a, Q'; split.
    2: split.
    1: symmetry; auto.
    1: auto.
    rewrite H2; apply ext_transition_subset; auto.
  - apply IHn with Q'.
    2: auto.
    rewrite H2; apply ext_transition_subset; auto.
Qed.

Lemma n2dfa_trans_in_states {A B} eq eq' (g:nfa_comp_list A B) Q Q1 n :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  let g' := n2dfa_trans eq eq' g n Q in
  subset Q (states g) ->
  In Q1 (states g') ->
  exists Q2 a, In (trans Q1 a Q2) g' \/ In (trans Q2 a Q1) g'.
Proof.
  intros;
  pose proof (in_n2dfa_trans eq eq' g n H Q);
  apply states_in in H1; destruct H1 as [H1|[H1|[H1|[Q' [a [H1|H1]]]]]].
  - apply (H2 (state Q1) H0) in H1;
    destruct H1 as [Q2 [b [Q3 [H1 [H3 H4]]]]];
    discriminate.
  - apply (H2 (start Q1) H0) in H1;
    destruct H1 as [Q2 [b [Q3 [H1 [H3 H4]]]]];
    discriminate.
  - apply (H2 (accept Q1) H0) in H1;
    destruct H1 as [Q2 [b [Q3 [H1 [H3 H4]]]]];
    discriminate.
  - exists Q', a; left; auto.
  - exists Q', a; right; auto.
Qed.

(*Lemma path_transitive {A B} (g:nfa_comp_list A B) q1 q2 q3 w1 w2 :
  path g q1 q2 w1 -> path g q2 q3 w2 -> path g q1 q3 (w1 ++ w2).
Proof.
  intros.
  induction H0.
  1: rewrite app_nil_r; auto.
  replace (w1 ++ w ++ [a]) with ((w1 ++ w) ++ [a]).
  2: rewrite app_assoc; auto.
  apply path_next with q2; auto.
Qed.*)

Definition pumping_length {A B} (g:nfa_comp_list A B) : nat.
Admitted.


Fixpoint n2dfa_accept_wrap {A B} eq (g:nfa_comp_list A B) states : nfa_comp_list (list A) B :=
  match states with
  | nil => nil
  | Q::states =>
    if has_accept_stateb eq g Q then
      accept Q::n2dfa_accept_wrap eq g states
    else
      n2dfa_accept_wrap eq g states
  end.

Lemma state_in_n2dfa_accept_wrap {A B} eq (g:nfa_comp_list A B) Q l :
  In Q (states (n2dfa_accept_wrap eq g l)) -> In Q l.
Proof.
  intros; induction l.
  1: destruct H.
  simpl in H; destruct (has_accept_stateb eq g a).
  2: intuition.
  destruct H; subst; intuition.
Qed.

Lemma in_n2dfa_accept_wrapp {A B} eq (g:nfa_comp_list A B) l :
  forall c, In c (n2dfa_accept_wrap eq g l) -> exists q, c = accept q.
Proof.
  intros; induction l.
  1: destruct H.
  simpl in H; destruct (has_accept_stateb eq g a).
  2: auto.
  destruct H.
  1: exists a; symmetry; auto.
  auto.
Qed.

Lemma dfa_app_n2dfa_accept_wrapp {A B} eq (g:nfa_comp_list A B) l :
  is_dfa' l ->
  is_dfa' (l ++ n2dfa_accept_wrap eq g (states l)).
Proof.
  intros; apply app_accept_is_dfa'.
  1: auto.
  intros.
  apply in_n2dfa_accept_wrapp with eq g (states l); auto.
Qed.


Definition n2dfa {A B} eq eq' (g:nfa_comp_list A B) :=
  let start_and_trans := start (start_states g)::n2dfa_trans eq eq' g (pumping_length g) (start_states g) in
  let normalized := normalize eq (start_and_trans) (start_and_trans) in
  match accept_states g with
  | nil => nil
  | _ => normalized ++ n2dfa_accept_wrap eq g (states (normalized))
  end.

Lemma n2dfa_nil {A B} eq eq' {g:nfa_comp_list A B} :
  accept_states g = [] -> n2dfa eq eq' g = [].
Proof.
  intros; unfold n2dfa; rewrite H; auto.
Qed.

Lemma n2dfa_states {A B eq eq'} {g:nfa_comp_list A B} Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In Q (states (n2dfa eq eq' g)) ->
  forall q, In q Q -> In q (states g).
Proof.
  intros H10; unfold n2dfa; intros; destruct (accept_states g) eqn:H1.
  1: destruct H.
  clear H1 a l; destruct H.
  {
    assert (eq_sets Q (start_states g)).
    2: apply H1 in H0; apply start_states_subset; auto.
    rewrite <- H; apply eq_sets_comm, get_set_eq; auto.
  }
  assert (forall q Q, In q Q -> In Q (states (n2dfa_trans eq eq' g (pumping_length g) (start_states g))) -> In q (states g)). {
    clear H H0 Q q; intros q Q H0 H1.
    assert (subset (start_states g) (states g)).
      apply start_states_subset.
    apply n2dfa_trans_in_states in H1.
    2,3: auto.
    destruct H1 as [Q2 [a [H1|H1]]].
    - apply in_n2dfa_trans in H1.
      2,3: auto.
      destruct H1 as [Q3 [b [Q5 [H1 H3]]]].
      injection H1; intros; subst.
      intuition.
    - apply in_n2dfa_trans in H1.
      2,3: auto.
      destruct H1 as [Q3 [b [Q5 [H1 H3]]]].
      injection H1; intros; subst.
      intuition.
  }
  apply in_app_states_or in H; destruct H.
  - apply state_in_normalize in H.
    2: auto.
    destruct H as [Q' [H H2]]; apply H1 with Q'.
    2: auto.
    apply H; auto.
  - apply state_in_n2dfa_accept_wrap in H; destruct H.
    {
      assert (eq_sets Q (start_states g)).
      2: apply H2 in H0; apply start_states_subset; auto.
      rewrite <- H; apply eq_sets_comm, get_set_eq; auto.
    }
    apply state_in_normalize in H.
    destruct H as [Q' [H H2]]; apply H1 with Q'.
    2,3: auto.
    apply H; auto.
Qed.

Lemma n2dfa_eq_states {A B} eq eq' (g:nfa_comp_list A B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  let g' := (n2dfa eq eq' g) in
  In Q1 (states g') -> In Q2 (states g') ->
  eq_sets Q1 Q2 -> Q1 = Q2.
Proof.
  unfold n2dfa; intros; destruct (accept_states g).
  1: destruct H0.
  apply in_app_states_or in H0; apply in_app_states_or in H1;
  destruct H0, H1.
  2,4: apply state_in_n2dfa_accept_wrap in H1.
  3,4: apply state_in_n2dfa_accept_wrap in H0.
  1-4: apply normalize_eq_sets with eq (start (start_states g) :: n2dfa_trans eq eq' g (pumping_length g) (start_states g)); auto.
Qed.

Lemma n2dfa_is_dfa {A B eq eq'} {g:nfa_comp_list A B} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  is_dfa' (n2dfa eq eq' g).
Proof.
  intros; unfold n2dfa; destruct (accept_states g).
  - apply cons_empty_dfa.
    apply (is_nfa_cons [] (lists_eq eq) eq' (lists_eq_correct H) H0).
  - apply dfa_app_n2dfa_accept_wrapp.
    clear a l.
    apply normalize_is_dfa'.
    1: auto.
    1: intros c; intuition.
    {
      intros; destruct H2, H3; try discriminate.
      apply trans_in_n2dfa_trans_eq in H2; apply trans_in_n2dfa_trans_eq in H3.
      2-4: auto.
      apply eq_sets_transitive with (ext_transition eq eq' g q1 [a]).
      1: apply eq_sets_comm; intuition.
      apply eq_sets_transitive with (ext_transition eq eq' g q3 [a]).
      2: apply eq_sets_comm; intuition.
      apply ext_transition_eq_sets, eq_sets_comm; auto.
    }
    apply cons_dfa_start.
    2: {
      assert (forall A (l:list A), (forall x, ~ In x l) -> l = []). {
        intros; destruct l.
        1: auto.
        specialize (H1 a); destruct H1; intuition.
      }
      apply H1; clear H1; intros q H1. apply start_states_in in H1.
      apply in_n2dfa_trans in H1.
      2: auto.
      2: apply start_states_subset.
      destruct H1 as [Q1 [a [Q2 [H1 _]]]]; discriminate.
    }
    assert (forall (g':nfa_comp_list (list A) B),
    (forall c, In c g' -> exists q a, c = trans q a (ext_transition eq eq' g q [a])) ->
    is_dfa' g').
    2: {
      apply H1; clear H1; intros; pose proof H1; apply in_n2dfa_trans in H1.
      2: auto.
      2: apply start_states_subset.
      destruct H1 as [Q1 [a [Q2 [H1 _]]]]; subst; apply trans_in_n2dfa_trans in H2.
      2: auto.
      exists Q1, a; destruct H2 as [H2 [H3 H4]]; subst; auto.
    }
    intros; induction g'.
    1: apply cons_empty_dfa, (is_nfa_cons [] (lists_eq eq) eq' (lists_eq_correct H) H0).
    pose proof H1; destruct H2 with a.
    1: left; auto.
    destruct H3 as [b H3]; subst.
    destruct (nfa_ex_trans_dec g' (is_nfa_cons g' (lists_eq eq) eq' (lists_eq_correct H) H0) x b).
    Opaque ext_transition.
    + destruct H3 as [y H3].
      destruct H2 with (trans x b y).
      1: intuition.
      destruct H4 as [b' H4]; injection H4; intros; subst.
      apply cons_dfa_trans_repeat.
      2: auto.
      apply IHg'; intros; apply H1; intuition.
    + apply cons_dfa_trans.
      2: auto.
      apply IHg'; intros; apply H1; intuition.
Qed.

Lemma n2dfa_accept {A B eq eq'} {g:nfa_comp_list A B} {Q} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  let g' := n2dfa eq eq' g in
  In Q (states g') ->
  In Q (accept_states g') <-> exists q, In q Q /\ In q (accept_states g).
Proof.
  unfold n2dfa; intros.
  destruct (accept_states g) eqn:H2.
  1: destruct H0.
  rewrite <- H2; clear H2 a l.
  pose proof (start_states_subset g) as H10;
  remember (start_states g) as Q0 eqn:H1; clear H1;
  remember (pumping_length g) as n eqn:H1; clear H1;
  split; intros.
  - clear H0; apply accept_states_in in H1.
    destruct H1.
    1: discriminate.
    apply in_app_or in H0; destruct H0.
    {
      apply accept_in_normalize in H0.
      2: auto.
      destruct H0 as [Q' [_ H0]].
      apply in_n2dfa_trans in H0.
      2,3: auto.
      destruct H0 as [Q1 [b [Q2 [H0 _]]]]; discriminate.
    }
    remember (states (normalize eq (start Q0 :: n2dfa_trans eq eq' g n Q0) (start Q0 :: n2dfa_trans eq eq' g n Q0))) as l eqn:H1; clear H1.
    induction l.
    1: destruct H0.
    1: simpl in H0.
    destruct (has_accept_stateb eq g a) eqn:H1.
    2: intuition.
    destruct H0.
    2: intuition.
    injection H0; intros; subst.
    apply has_accept_stateb_correct in H1; auto.
  - assert (In Q (states (normalize eq (start Q0 :: n2dfa_trans eq eq' g n Q0) (start Q0 :: n2dfa_trans eq eq' g n Q0)))). {
      apply in_app_states_or in H0; destruct H0.
      1: auto.
      apply state_in_n2dfa_accept_wrap in H0; auto.
    }
    clear H0;
    remember (normalize eq (start Q0 :: n2dfa_trans eq eq' g n Q0) (start Q0 :: n2dfa_trans eq eq' g n Q0)) as l eqn:H0; clear H0.
    apply accept_states_in; apply in_or_app; right;
    induction l.
    1: destruct H2.
    destruct a.
    + destruct H2; subst.
      * assert (has_accept_stateb eq g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; rewrite H0; left; auto.
      * simpl; destruct (has_accept_stateb eq g q).
        1: right.
        1,2: intuition.
    + intuition.
    + destruct H2; subst.
      * assert (has_accept_stateb eq g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; rewrite H0; left; auto.
      * simpl; destruct (has_accept_stateb eq g q).
        1: right.
        1,2: intuition.
    + destruct H2; subst.
      * assert (has_accept_stateb eq g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; rewrite H0; left; auto.
      * simpl; destruct (has_accept_stateb eq g q).
        1: right.
        1,2: intuition.
    + destruct H2; subst.
      2: destruct H0; subst.
      * assert (has_accept_stateb eq g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; rewrite H0; left; auto.
      * assert (has_accept_stateb eq g Q = true).
          apply has_accept_stateb_correct; auto.
        simpl; destruct (has_accept_stateb eq g q).
        1: right.
        1,2: simpl; rewrite H0; left; auto.
      * simpl; destruct (has_accept_stateb eq g q), (has_accept_stateb eq g q'); try right; try right.
        1-4: intuition.
Qed.

Lemma n2dfa_path {A B eq eq'} {g:nfa_comp_list A B} {Q q' w} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  let g' := (n2dfa eq eq' g) in
  (forall Q', path g' Q Q' w /\ In q' Q' -> exists q, path g q q' w /\ In q Q) /\
  (forall q, path g q q' w /\ In q Q -> exists Q', path g' Q Q' w /\ In q' Q').
Proof.
Admitted.

Lemma n2dfa_start_states {A B} eq eq' (g:nfa_comp_list A B) :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  n2dfa eq eq' g <> nil ->
  start_states (n2dfa eq eq' g) = [start_states g].
Proof.
  unfold n2dfa; intros; destruct (accept_states g).
  1: destruct H0; auto.
  clear H0 l.
  rewrite app_start_states_nil.
  2: {
    remember (states (normalize eq (start (start_states g) :: n2dfa_trans eq eq' g (pumping_length g) (start_states g))
     (start (start_states g) :: n2dfa_trans eq eq' g (pumping_length g) (start_states g)))) as l eqn:H0; clear H0.
    induction l.
    1: auto.
    simpl; destruct (has_accept_stateb eq g a0); auto.
  }
  simpl; unfold normalize_state; simpl.
  assert (eq_setsb eq (start_states g) (start_states g) = true).
    apply eq_setsb_correct; auto; split; auto.
  rewrite H0.
  assert (start_states (normalize eq (n2dfa_trans eq eq' g (pumping_length g) (start_states g))
    (start (start_states g) :: n2dfa_trans eq eq' g (pumping_length g) (start_states g))) = nil).
  2: rewrite H1; auto.
  apply normalize_start_states_nil.
  clear H0 a;
  generalize dependent (start_states g);
  induction (pumping_length g); intros.
  1: auto.
  simpl; induction (alphabet g).
  1: auto.
  Opaque ext_transition.
  simpl; destruct (ext_transition eq eq' g l [a]) eqn:H0.
  1: auto.
  simpl; rewrite <- (IHn (a0::l1)); apply app_start_states_nil.
  auto.
  Transparent ext_transition.
Qed.

Lemma n2dfa_language {A B} eq eq' (g:nfa_comp_list A B) :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  equivalent_nfas eq eq' (lists_eq eq) g (n2dfa eq eq' g).
Proof.
  unfold equivalent_nfas; intros; split.
  2: split.
  3: split.
  1-3: try apply lists_eq_correct; intuition.
  unfold accepts; intros; split; intros.
  - destruct H1 as [q [H1 H2]].
    apply ext_transition_list in H1; destruct H1 as [q0 [H1 H3]].
    apply path_ext_transition in H3.
    2,3: auto.
    destruct (@n2dfa_path A B eq eq' g (start_states g) q w H H0) as [_ H5].
    destruct H5 with q0.
    1: intuition.
    destruct H4 as [H4 H6].
    exists x; split.
    + rewrite n2dfa_start_states.
      2: auto.
      2: {
        assert (In x (ext_transition (lists_eq eq) eq' (n2dfa eq eq' g) [start_states g] w)).
          apply path_ext_transition; try apply lists_eq_correct; auto.
        assert (In (start_states g) (start_states (n2dfa eq eq' g))). {
          rewrite n2dfa_start_states.
          1,2: try left; auto.
          unfold n2dfa; destruct (accept_states g).
          1: destruct H2.
          simpl; discriminate.
        }
        clear H1 H2 H3 H4 H5 H6; destruct (n2dfa eq eq' g).
        2: intros contra; discriminate.
        generalize dependent [start_states g]; induction w; intros.
        2: simpl in H7; apply IHw in H7; auto.
        destruct H8.
      }
      apply path_ext_transition.
      1-3: try apply lists_eq_correct; auto.
    + apply (n2dfa_accept H).
      2: exists q; intuition.
      assert (In x (ext_transition (lists_eq eq) eq' (n2dfa eq eq' g) [start_states g] w)).
        apply path_ext_transition; try apply lists_eq_correct; auto.
      apply ext_transition_in_states in H7.
      1: auto.
      intros; destruct H8; subst.
      2: destruct H8.
      apply start_states_subset.
      rewrite n2dfa_start_states.
      1,2: try left; auto.
      unfold n2dfa; destruct (accept_states g).
      1: destruct H2.
      simpl; discriminate.
  - destruct H1 as [Q' [H1 H2]].
    rewrite n2dfa_start_states in H1.
    2: auto.
    2: {
      unfold n2dfa; unfold n2dfa in H2; destruct (accept_states g).
      1: destruct H2.
      simpl; intros contra; discriminate.
    }
    apply path_ext_transition in H1.
    2,3: try apply lists_eq_correct; auto.
    assert (exists q, In q Q' /\ In q (accept_states g)). {
      assert (In Q' (states (n2dfa eq eq' g))).
        apply accept_states_in, accept_in_states in H2; auto.
      apply (n2dfa_accept H H3); auto.
    }
    destruct H3 as [q' H4].
    destruct (@n2dfa_path A B eq eq' g (start_states g) q' w H H0) as [H5 _].
    destruct H5 with Q'.
    1: intuition.
    destruct H3 as [H3 H7].
    exists q'; split.
    2: intuition.
    apply ext_transition_single with x; split.
    1: auto.
    apply path_ext_transition; auto.
Qed.













