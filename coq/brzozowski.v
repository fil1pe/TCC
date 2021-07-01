Require Import List Bool sets nfa dfa reversing n2dfa.
Include ListNotations.


(* Algoritmo de Brzozowski *)
Definition brzozowski {A B} (G:nfa A B) :=
  match G with
  | nfa_cons _ _ g eq eq' _ _ => n2dfa eq eq' (revert_nfa g)
  end.

(* Prova de que um estado final do autômato resultante do algoritmo é uma lista
com o estado inicial do autômato original *)
Lemma brzozowski_accept {A B eq eq'} {g:nfa_comp_list A B} {q0 Q} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  is_dfa' g -> In q0 (start_states g) ->
  let brz := (n2dfa eq eq' (revert_nfa g)) in
  (in_opt Q (Some (states brz)) \/ Q = None) ->
  in_opt Q (Some (accept_states brz)) <-> in_opt (Some q0) Q.
Proof.
  intro H10; intros.
  destruct H1.
  2: split; intros; subst; auto.
  destruct Q.
  2: destruct H1.
  pose proof H0.
  apply revert_start in H2.
  simpl; simpl in H1.
  split; intros.
  - apply (n2dfa_accept H10 H1) in H3; destruct H3 as [_q0 [H3 H4]].
    assert (_q0 = q0).
    2: subst; auto.
    apply revert_accept in H4; replace (revert_nfa (revert_nfa g)) with g in H4.
    2: apply revert_nfa_twice.
    apply dfa_start with g; auto.
  - apply (n2dfa_accept H10 H1); exists q0; auto.
Qed.

(* Prova da observação básica *)
Lemma basic_observation {A B eq eq'} {g:nfa_comp_list A B} {q' Q w} :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  is_dfa' g ->
  let brz := (n2dfa eq eq' (revert_nfa g)) in
  In Q (states brz) ->
  in_opt (Some q') (dfa_transition (lists_eq eq) eq' brz (Some Q) w) <->
  in_opt (dfa_transition eq eq' g (Some q') (revert w)) (Some Q).
Proof.
  intros H10 H11 H brz H12; intros; split; intros.
  - simpl in H0; destruct (ext_transition (lists_eq eq) eq' brz [Q] w) as [|Q' L] eqn:H1.
    1: destruct H0.
    assert (In Q' (ext_transition (lists_eq eq) eq' brz [Q] w)).
      rewrite H1; left; auto.
    apply path_ext_transition in H2.
    2: apply lists_eq_correct.
    2,3: auto.
    assert (path brz Q Q' w /\ In q' Q').
        split; auto.
    apply (n2dfa_path_reach H10 H11) in H3; destruct H3 as [q [H3 H4]].
    apply reverted_path in H3; replace (revert_nfa (revert_nfa g)) with g in H3.
    2: apply revert_nfa_twice.
    simpl; destruct (ext_transition eq eq' g [q'] (revert w)) as [|_q l] eqn:H5.
    + assert (In q []).
        rewrite <- H5; apply path_ext_transition; auto.
      destruct H6.
    + simpl.
      assert (In _q (ext_transition eq eq' g [q'] (revert w))).
        rewrite H5; left; auto.
      assert (In q (ext_transition eq eq' g [q'] (revert w))).
        apply path_ext_transition; auto.
      assert (_q = q).
        clear H5 l; remember (ext_transition eq eq' g [q'] (revert w)) as l;
        apply (@dfa_trans_ext A B eq eq' g q' q _q (revert w) l); auto.
      subst; auto.
  - simpl in H0; destruct (ext_transition eq eq' g [q'] (revert w)) as [|q l] eqn:H1; simpl in H0.
    1: destruct H0.
    assert (path g q' q (revert w)).
      apply path_ext_transition with eq eq'; try rewrite H1; intuition.
    apply reverted_path in H2; rewrite <- revert_twice in H2.
    assert (H3: exists Q', path brz Q Q' w /\ In q' Q').
      pose proof (@n2dfa_path_reach A B eq eq' (revert_nfa g) Q q' w H10 H11) as H3;
      destruct H3 as [_ H3]; apply H3 with q; auto.
    destruct H3 as [Q' [H3 H4]].
    apply (path_ext_transition (lists_eq eq) eq' brz Q Q' w (lists_eq_correct H10) H11) in H3.
    simpl; destruct (ext_transition (lists_eq eq) eq' brz [Q] w) as [|_Q' L] eqn:H5.
    1: destruct H3.
    assert (_Q' = Q').
    2: subst; auto.
    apply (@dfa_trans_ext (list A) B (lists_eq eq) eq' brz Q Q' _Q' w (_Q' :: L)).
    1: apply lists_eq_correct; auto.
    1,3-5: intuition.
    apply n2dfa_is_dfa; auto.
Qed.

(* Prova de que todos os estados do algoritmo de Brzozowski são distinguíveis *)
Lemma brzozowski_disting' {A B} eq eq' (g:nfa_comp_list A B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  (forall q, In q (states g) -> reachable_state eq eq' g q) ->
  is_dfa' g ->
  let brz := (n2dfa eq eq' (revert_nfa g)) in
  In Q1 (states brz) -> In Q2 (states brz) ->
  dfa_indisting_states (lists_eq eq) eq' brz Q1 Q2 ->
  Q1 = Q2.
Proof.
  intros H11 H12 H10.
  intros.
  unfold dfa_indisting_states in H2.
  destruct (start_states g) eqn:H4.
  - apply revert_nfa_start_nil, (n2dfa_nil eq eq') in H4.
    assert (brz = []).
      auto.
    rewrite H3 in H0.
    destruct H0.
  - assert (H3: exists q0, In q0 (start_states g)).
      exists a; rewrite H4; intuition.
    destruct H3 as [q0 H3]; clear H4.
    assert (forall w, in_opt (Some q0) (dfa_transition (lists_eq eq) eq' brz (Some Q1) w) <->
    in_opt (Some q0) (dfa_transition (lists_eq eq) eq' brz (Some Q2) w)). {
      intros.
      specialize (H2 w).
      replace brz with (n2dfa eq eq' (revert_nfa g)) in H2.
      2: auto.
      rewrite (brzozowski_accept H11 H H3), (brzozowski_accept H11 H H3) in H2.
      intuition.
      - simpl; destruct (ext_transition (lists_eq eq) eq'
          (n2dfa eq eq' (revert_nfa g)) [Q2] w) eqn:H4.
        1: right; auto.
        left; simpl.
        apply (ext_transition_in_states (lists_eq eq) eq' (n2dfa eq eq' (revert_nfa g) : nfa_comp_list (list A) B) [Q2] l0 w).
        2: rewrite H4; intuition.
        intros; destruct H5.
        2: destruct H5.
        subst; auto.
      - simpl; destruct (ext_transition (lists_eq eq) eq'
          (n2dfa eq eq' (revert_nfa g)) [Q1] w) eqn:H4.
        1: right; auto.
        left; simpl.
        apply (ext_transition_in_states (lists_eq eq) eq' (n2dfa eq eq' (revert_nfa g) : nfa_comp_list (list A) B) [Q1] l0 w).
        2: rewrite H4; intuition.
        intros; destruct H5.
        2: destruct H5.
        subst; auto.
    }
    clear H2.
    assert (H5: forall w, in_opt (dfa_transition eq eq' g (Some q0) (revert w)) (Some Q1) <->
    in_opt (dfa_transition eq eq' g (Some q0) (revert w)) (Some Q2)). {
      intros.
      specialize (H4 w).
      replace brz with (n2dfa eq eq' (revert_nfa g)) in H4.
      2: auto.
      rewrite (basic_observation H11 H12 H), (basic_observation H11 H12 H) in H4;
      intuition.
    }
    clear H4.
    assert (forall w, in_opt (dfa_transition eq eq' g (Some q0) w) (Some Q1) <->
    in_opt (dfa_transition eq eq' g (Some q0) w) (Some Q2)). {
      intros.
      specialize (H5 (revert w)).
      replace w with (revert (revert w)).
      2: symmetry; apply revert_twice.
      auto.
    }
    clear H5.
    assert (forall q, in_opt q (Some Q1) <-> in_opt q (Some Q2)). {
      destruct q as [q|].
      2: intuition.
      replace brz with (n2dfa eq eq' (revert_nfa g)) in H0, H1.
      2: auto.
      simpl; split; intros.
      - apply (n2dfa_states Q1) with q in H0.
        2: auto.
        pose proof (revert_states_are_states g q) as H5; destruct H5 as [H5 _];
        apply H5 in H0; clear H5.
        apply H10 in H0; destruct H0 as [w H0].
        apply ext_transition_list in H0.
        destruct H0 as [q0' [H5 H6]].
        assert (q0' = q0).
          apply dfa_start with g; auto.
        subst.
        specialize (H2 w); simpl in H2;
        destruct (ext_transition eq eq' g [q0] w) eqn:H7.
        1: destruct H6.
        2: auto.
        assert (q = a0). {
          assert (In a0 (a0::l0)).
            left; auto.
          apply dfa_trans_ext with eq eq' g q0 w (a0::l0); auto.
        }
        subst; intuition.
      - apply (n2dfa_states Q2) with q in H1.
        2: auto.
        pose proof (revert_states_are_states g q) as H5; destruct H5 as [H5 _];
        apply H5 in H1; clear H5.
        apply H10 in H1; destruct H1 as [w H1].
        apply ext_transition_list in H1.
        destruct H1 as [q0' [H5 H6]].
        assert (q0' = q0).
          apply dfa_start with g; auto.
        subst.
        specialize (H2 w); simpl in H2;
        destruct (ext_transition eq eq' g [q0] w) eqn:H7.
        1: destruct H6.
        2: auto.
        assert (q = a0). {
          assert (In a0 (a0::l0)).
            left; auto.
          apply dfa_trans_ext with eq eq' g q0 w (a0::l0); auto.
        }
        subst; intuition.
    }
    assert (eq_sets Q1 Q2). {
      unfold eq_sets; intros q.
      specialize (H4 (Some q)).
      intuition.
    }
    apply (n2dfa_eq_states eq eq' (revert_nfa g)) in H5; auto.
Qed.

(* Prova de que a linguagem é reversa *)
Lemma brzozowski_language {A B} eq eq' (g:nfa_comp_list A B) w :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  (forall q, In q (states g) -> reachable_state eq eq' g q) ->
  let brz := (n2dfa eq eq' (revert_nfa g)) in
  accepts (lists_eq eq) eq' brz w <-> accepts eq eq' g (revert w).
Proof.
  intros.
  assert (equivalent_nfas eq eq' (lists_eq eq) (revert_nfa g) brz).
    intros; apply n2dfa_language; auto.
  split; intros.
  - destruct H2 as [_ [_ [_ H2]]];
    apply reverted_nfa_lang.
    1,2: auto.
    apply H2; rewrite <- revert_twice; auto.
  - destruct H2 as [_ [_ [_ H2]]].
    apply H2. apply reverted_nfa_lang.
    1,2: auto.
    rewrite <- revert_nfa_twice; auto.
    
Qed.













