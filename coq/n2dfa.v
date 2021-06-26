Require Import List Bool Lia sets nfa dfa reversing.
Include ListNotations.


Fixpoint loop {A B} eq eq' (g:nfa_comp_list A B) f h Q l :=
  match l with
  | nil => nil
  | a::l => match (ext_transition eq eq' g Q [a]) with
            | nil => loop eq eq' g f h Q l
            | Q'' => let Q' := h Q'' in
                     trans Q a Q'::f Q' ++ loop eq eq' g f h Q l
            end
  end.

Lemma loop_in {A B} eq eq' (g:nfa_comp_list A B) f h Q l a :
  In a l -> ext_transition eq eq' g Q [a] <> nil ->
  In (trans Q a (h (ext_transition eq eq' g Q [a]))) (loop eq eq' g f h Q l).
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

Lemma in_loop {A B} eq eq' (g:nfa_comp_list A B) f h Q l c :
  In c (loop eq eq' g f h Q l) ->
  exists Q' a, In a l /\ Q' <> nil /\ Q' = ext_transition eq eq' g Q [a] /\
  In c (trans Q a (h Q')::f (h Q')).
Proof.
  Opaque ext_transition.
  intros.
  induction l as [|b l].
  1: destruct H.
  simpl in H; destruct (ext_transition eq eq' g Q [b]) eqn:H0.
  1: apply IHl in H; destruct H as [Q' [a H]]; exists Q', a; intuition.
  replace (trans Q b (h (a :: l0)) :: f (h (a :: l0)) ++ loop eq eq' g f h Q l) with
  ((trans Q b (h (a :: l0)) :: f (h (a :: l0))) ++ loop eq eq' g f h Q l) in H.
  2: auto.
  apply in_app_or in H; destruct H.
  - exists (a::l0), b; repeat split.
    1,3,4: intuition.
    intros contra; discriminate.
  - apply IHl in H; destruct H as [Q' [d H]]; exists Q', d; intuition.
  Transparent ext_transition.
Qed.

Lemma next_in_loop {A B} eq eq' (g:nfa_comp_list A B) f h Q l a c :
  ext_transition eq eq' g Q [a] <> nil ->
  In a l ->
  In c (f (h (ext_transition eq eq' g Q [a]))) ->
  In c (loop eq eq' g f h Q l).
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


Fixpoint n2dfa_trans {A B} eq eq' (g:nfa_comp_list A B) l n Q :=
  match n with
  | O => nil
  | S n =>
    loop eq eq' g (n2dfa_trans eq eq' g (Q::l) n) (fun Q' => get_set eq Q' (Q::l)) Q (alphabet g)
  end.

Lemma trans_in_n2dfa_trans {A B} eq eq' (g:nfa_comp_list A B) l Q0 Q Q' n a :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In (trans Q a Q') (n2dfa_trans eq eq' g l n Q0) ->
  In a (alphabet g) /\ Q' <> nil /\ eq_sets Q' (ext_transition eq eq' g Q [a]).
Proof.
  intros;
  generalize dependent Q0;
  generalize dependent l;
  induction n; intros.
  1: destruct H0.
  simpl in H0; apply in_loop in H0; destruct H0 as [Q0' [b [H0 [H1 [H2 [H3|H3]]]]]].
  2: apply IHn in H3; clear IHn; auto.
  clear IHn; injection H3; intros; subst; split.
  2: split.
  1: auto.
  + assert (eq_sets (ext_transition eq eq' g Q [a]) (if eq_setsb eq (ext_transition eq eq' g Q [a]) Q then Q else get_set eq (ext_transition eq eq' g Q [a]) l)). {
      destruct (eq_setsb eq (ext_transition eq eq' g Q [a]) Q) eqn:H2.
      1:apply eq_setsb_correct in H2; auto.
      apply get_set_eq; auto.
    }
    intros contra; rewrite contra in H2; clear contra.
    assert (exists q, In q (ext_transition eq eq' g Q [a])). {
      destruct (ext_transition eq eq' g Q [a]).
      1: destruct H1; auto.
      exists a0; intuition.
    }
    destruct H4 as [q H4]; destruct H2 with q; apply H5 in H4; destruct H4.
  + destruct (eq_setsb eq (ext_transition eq eq' g Q [a])) eqn:H4.
    1: apply eq_sets_comm; apply eq_setsb_correct in H4; auto.
    apply eq_sets_comm, get_set_eq; auto.
Qed.

Lemma n2dfa_trans_old_path {A B} eq eq' (g:nfa_comp_list A B) l n w Q Q' q' :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  In q' Q' -> path (n2dfa_trans eq eq' g l n Q) Q Q' w ->
  exists q, In q Q /\ path g q q' w.
Proof.
  intros.
  generalize dependent q';
  induction H2; intros.
  1: exists q'; intuition; constructor.
  apply trans_in_n2dfa_trans in H1.
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

Lemma n2dfa_trans_new_path {A B} eq eq' (g:nfa_comp_list A B) n l w Q q q' :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  length w <= n -> In q Q -> path g q q' w ->
  exists Q', In q' Q' /\ path (n2dfa_trans eq eq' g l n Q) Q Q' w.
Proof.
  generalize dependent w;
  generalize dependent q;
  generalize dependent Q;
  generalize dependent l;
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
      destruct IHn with (Q::l) ((fun Q'0 : list A => if eq_setsb eq Q'0 Q then Q else get_set eq Q'0 l) (ext_transition eq eq' g Q [a])) q'' w.
      1,2,5: intuition.
      1: simpl in H1; lia.
      {
        induction Q.
        1: destruct H2.
        destruct H2.
        - subst; assert (In q'' (ext_transition eq eq' g (q :: Q) [a])).
            simpl; apply in_or_app; left; apply transition_in; intuition.
          assert (eq_sets (if eq_setsb eq (ext_transition eq eq' g (q :: Q) [a]) (q :: Q) then q :: Q
          else get_set eq (ext_transition eq eq' g (q :: Q) [a]) l) (ext_transition eq eq' g (q :: Q) [a])).
          2: apply H5; auto.
          destruct (eq_setsb eq (ext_transition eq eq' g (q :: Q) [a]) (q :: Q)) eqn:H5.
          2: apply eq_sets_comm, get_set_eq; auto.
          apply eq_sets_comm; apply eq_setsb_correct in H5; auto.
        - apply IHQ in H2; clear IHQ.
          assert (In q'' (ext_transition eq eq' g Q [a])). {
            assert (eq_sets (if eq_setsb eq (ext_transition eq eq' g Q [a]) Q
            then Q else get_set eq (ext_transition eq eq' g Q [a]) l) (ext_transition eq eq' g Q [a])).
            2: apply H5; intuition.
            destruct (eq_setsb eq (ext_transition eq eq' g Q [a]) Q) eqn:H5.
            2: apply eq_sets_comm, get_set_eq; auto.
            apply eq_sets_comm; apply eq_setsb_correct in H5; auto.
          }
          assert (In q'' (ext_transition eq eq' g (a0 :: Q) [a])).
            simpl in *; apply in_or_app; right; auto.
          assert (eq_sets (if eq_setsb eq (ext_transition eq eq' g (a0 :: Q) [a]) (a0 :: Q)
          then a0 :: Q
          else get_set eq (ext_transition eq eq' g (a0 :: Q) [a]) l) (ext_transition eq eq' g (a0 :: Q) [a])).
          2: apply H7; auto.
          destruct (eq_setsb eq (ext_transition eq eq' g (a0 :: Q) [a]) (a0 :: Q)) eqn:H7.
          2: apply eq_sets_comm, get_set_eq; auto.
          apply eq_sets_comm; apply eq_setsb_correct in H7; auto.
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
      remember (fun Q' : list A => if eq_setsb eq Q' Q then Q else get_set eq Q' l) as h eqn:H8.
      apply path_left with (h (ext_transition eq eq' g Q [a])).
      1: apply loop_in; auto.
      subst; induction (alphabet g).
      1: destruct H6.
      simpl loop; subst.
      destruct H6.
      * subst; clear IHl0; destruct (ext_transition eq eq' g Q [a]) eqn:H8.
        1: destruct H7; auto.
        replace (trans Q a (if eq_setsb eq (a0 :: l1) Q then Q else get_set eq (a0 :: l1) l)
        :: n2dfa_trans eq eq' g (Q :: l) n (if eq_setsb eq (a0 :: l1) Q then Q else get_set eq (a0 :: l1) l) ++
        loop eq eq' g (n2dfa_trans eq eq' g (Q :: l) n) (fun Q' : list A => if eq_setsb eq Q' Q then Q else get_set eq Q' l) Q l0) with
        ([trans Q a (if eq_setsb eq (a0 :: l1) Q then Q else get_set eq (a0 :: l1) l)] ++
        n2dfa_trans eq eq' g (Q :: l) n (if eq_setsb eq (a0 :: l1) Q then Q else get_set eq (a0 :: l1) l) ++
        loop eq eq' g (n2dfa_trans eq eq' g (Q :: l) n) (fun Q' : list A => if eq_setsb eq Q' Q then Q else get_set eq Q' l) Q l0).
        2: auto.
        apply path_app; right; apply path_app; left; intuition.
      * destruct (ext_transition eq eq' g Q [a0]).
        1: intuition.
        replace (trans Q a0 (if eq_setsb eq (a1 :: l1) Q then Q else get_set eq (a1 :: l1) l)
        :: n2dfa_trans eq eq' g (Q :: l) n (if eq_setsb eq (a1 :: l1) Q then Q else get_set eq (a1 :: l1) l) ++
        loop eq eq' g (n2dfa_trans eq eq' g (Q :: l) n)
        (fun Q' : list A => if eq_setsb eq Q' Q then Q else get_set eq Q' l) Q l0) with
        ([trans Q a0 (if eq_setsb eq (a1 :: l1) Q then Q else get_set eq (a1 :: l1) l)] ++
        n2dfa_trans eq eq' g (Q :: l) n (if eq_setsb eq (a1 :: l1) Q then Q else get_set eq (a1 :: l1) l) ++
        loop eq eq' g (n2dfa_trans eq eq' g (Q :: l) n)
        (fun Q' : list A => if eq_setsb eq Q' Q then Q else get_set eq Q' l) Q l0).
        2: auto.
        apply path_app; right; apply path_app; right; intuition.
      Transparent ext_transition.
Qed.

Lemma in_n2dfa_trans {A B} eq eq' (g:nfa_comp_list A B) n :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  forall Q l c, subset Q (states g) -> In c (n2dfa_trans eq eq' g l n Q) ->
  exists Q1 a Q2, c = trans Q1 a Q2 /\ subset Q1 (states g) /\ subset Q2 (states g).
Proof.
  intros H10;
  induction n; intros.
  1: destruct H0.
  simpl in H0; apply in_loop in H0; destruct H0 as [Q' [a [H0 [H1 [H2 [H3|H3]]]]]].
  - exists Q, a, (if eq_setsb eq Q' Q then Q else get_set eq Q' l); split.
    2: split.
    1: symmetry; auto.
    1: auto.
    destruct (eq_setsb eq Q' Q).
    1: auto.
    apply subset_eq with Q'.
    2: apply get_set_eq; auto.
    rewrite H2; apply ext_transition_subset; auto.
  - apply IHn with (if eq_setsb eq Q' Q then Q else get_set eq Q' l) (Q::l).
    2: auto.
    destruct (eq_setsb eq Q' Q).
    1: auto.
    apply subset_eq with Q'.
    2: apply get_set_eq; auto.
    rewrite H2; apply ext_transition_subset; auto.
Qed.

Lemma n2dfa_trans_in_states {A B} eq eq' (g:nfa_comp_list A B) Q Q1 l n :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  let g' := n2dfa_trans eq eq' g l n Q in
  subset Q (states g) ->
  In Q1 (states g') ->
  exists Q2 a, In (trans Q1 a Q2) g' \/ In (trans Q2 a Q1) g'.
Proof.
  intros;
  pose proof (in_n2dfa_trans eq eq' g n H Q l);
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

Lemma n2dfa_trans_eq_states {A B} eq eq' (g:nfa_comp_list A B) l n Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  let g' := n2dfa_trans eq eq' g l n Q in
  forall Q1 Q2,
  In Q1 (states g') -> In Q2 (states g') ->
  eq_sets Q1 Q2 -> Q1 = Q2.
Proof.
Admitted.


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

Lemma in_n2dfa_accept_wrap {A B} eq (g:nfa_comp_list A B) Q l :
  In Q (states (n2dfa_accept_wrap eq g l)) -> In Q l.
Proof.
  intros; induction l.
  1: destruct H.
  simpl in H; destruct (has_accept_stateb eq g a).
  2: intuition.
  destruct H; subst; intuition.
Qed.


Definition n2dfa {A B} eq eq' (g:nfa_comp_list A B) :=
  let g' := n2dfa_trans eq eq' g nil (pumping_length g) (start_states g) in
  match accept_states g with
  | nil => nil
  | _ => start (start_states g)::g' ++ n2dfa_accept_wrap eq g (start_states g::states (g'))
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
  1: apply start_state_is_state; rewrite H; intuition.
  assert (In Q (states (n2dfa_trans eq eq' g nil (pumping_length g) (start_states g))) -> In q (states g)). {
    intros.
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
  1: intuition.
  apply in_n2dfa_accept_wrap in H; destruct H.
  1: apply start_state_is_state; rewrite H; auto.
  intuition.
Qed.

Lemma n2dfa_eq_states {A B} eq eq' (g:nfa_comp_list A B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  let g' := (n2dfa eq eq' g) in
  In Q1 (states g') -> In Q2 (states g') ->
  eq_sets Q1 Q2 -> Q1 = Q2.
Proof.
  Opaque ext_transition.
  intros H.
  assert (forall l n Q Q1 Q2, In Q1 (states (n2dfa_trans eq eq' g l n Q)) -> In Q2 (states (n2dfa_trans eq eq' g l n Q)) -> eq_sets Q1 Q2 -> Q1 = Q2).
    intros; apply n2dfa_trans_eq_states with eq eq' g l n Q; auto.
  unfold n2dfa; intros; destruct (accept_states g).
  1: destruct H1.
  assert (forall Q, In Q (states (n2dfa_trans eq eq' g [] (pumping_length g) (start_states g))) -> eq_sets (start_states g) Q -> start_states g = Q). {
    intros.
    assert (In (start_states g) (states (n2dfa_trans eq eq' g [] (pumping_length g) (start_states g)))). {
      clear H3 H2 H1 H0; destruct (pumping_length g) as [|n].
      1: destruct H4.
      apply n2dfa_trans_in_states in H4.
      3: apply start_states_subset.
      2: auto.
      destruct H4 as [Q3 [b [H4|H4]]].
      - simpl in H4; apply in_loop in H4; destruct H4 as [Q4 [c H4]].
        simpl; remember (fun Q' : list A => if eq_setsb eq Q' (start_states g) then start_states g else Q') as h eqn:H7.
        apply trans_in_states with c (h (ext_transition eq eq' g (start_states g) [c])); apply loop_in.
        1: intuition.
        destruct H4 as [_ [H4 [H6 _]]]; rewrite <- H6; auto.
      - simpl in H4; apply in_loop in H4; destruct H4 as [Q4 [c H4]].
        simpl; remember (fun Q' : list A => if eq_setsb eq Q' (start_states g) then start_states g else Q') as h eqn:H7.
        apply trans_in_states with c (h (ext_transition eq eq' g (start_states g) [c])); apply loop_in.
        1: intuition.
        destruct H4 as [_ [H4 [H6 _]]]; rewrite <- H6; auto.
    }
    apply H0 with nil (pumping_length g) (start_states g); auto.
  }
  destruct H1, H2.
  - symmetry in H1, H2; subst; auto.
  - symmetry in H1; subst;
    apply in_app_states_or in H2; destruct H2.
    1: auto.
    apply in_n2dfa_accept_wrap in H1; destruct H1; subst; auto.
  - symmetry; apply eq_sets_comm in H3; symmetry in H2; subst;
    apply in_app_states_or in H1; destruct H1.
    1: auto.
    apply in_n2dfa_accept_wrap in H1; destruct H1; subst; auto.
  - clear H4; apply in_app_states_or in H1; apply in_app_states_or in H2;
    destruct H1, H2.
    + apply H0 with nil (pumping_length g) (start_states g); auto.
    + apply in_n2dfa_accept_wrap in H2; destruct H2.
Admitted.

Lemma n2dfa_path {A B eq eq'} {g:nfa_comp_list A B} {Q q' w} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  let g' := (n2dfa eq eq' g) in
  (forall Q', path g' Q Q' w /\ In q' Q' -> exists q, path g q q' w /\ In q Q) /\
  (forall q, path g q q' w /\ In q Q -> exists Q', path g' Q Q' w /\ In q' Q').
Proof.
Admitted.

Lemma n2dfa_is_dfa {A B eq eq'} {g:nfa_comp_list A B} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  is_dfa' (n2dfa eq eq' g).
Proof.
Admitted.

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
  remember (@nil (list A)) as l eqn:H1; clear H1;
  remember (pumping_length g) as n eqn:H1; clear H1;
  split; intros.
  - clear H0; apply accept_states_in in H1.
    destruct H1.
    1: discriminate.
    apply in_app_or in H0; destruct H0.
    1: apply in_n2dfa_trans in H0; auto; destruct H0 as [Q1 [a [Q2 [H0 _]]]]; discriminate.
    remember (Q0::states (n2dfa_trans eq eq' g l n Q0)) as st eqn:H1; clear H1.
    induction st.
    1: destruct H0.
    simpl in H0; destruct (has_accept_stateb eq g a) eqn:H1.
    2: intuition.
    apply has_accept_stateb_correct in H1.
    1: destruct H0.
    2,3: auto.
    injection H0; intros; subst; auto.
  - destruct H1 as [q [H1 H2]].
    destruct H0; subst.
    + simpl; apply accept_states_in, in_or_app.
      assert (has_accept_stateb eq g Q = true). {
        apply has_accept_stateb_correct.
        1: auto.
        exists q; intuition.
      }
      rewrite H0; intuition.
    + assert (In Q (Q0::states (n2dfa_trans eq eq' g l n Q0)) -> In Q (accept_states (n2dfa_accept_wrap eq g (Q0::states (n2dfa_trans eq eq' g l n Q0))))). {
        remember (Q0 :: states (n2dfa_trans eq eq' g l n Q0)) as y eqn:H3; clear H3 H0; intros.
        induction y; destruct H0; subst.
        - assert (has_accept_stateb eq g Q = true).
            apply has_accept_stateb_correct; try exists q; intuition.
          simpl; rewrite H0; simpl; intuition.
        - simpl; destruct (has_accept_stateb eq g a).
          1,2: simpl; intuition.
      }
      apply in_app_states_or in H0; destruct H0.
      * apply accept_states_in; right; apply in_or_app; right;
        apply accept_states_in, H3; intuition.
      * apply accept_states_in; right; apply in_or_app; right;
        apply accept_states_in, H3;
        pose proof (in_n2dfa_accept_wrap eq g Q (Q0 :: states (n2dfa_trans eq eq' g l n Q0)));
        intuition.
Qed.










