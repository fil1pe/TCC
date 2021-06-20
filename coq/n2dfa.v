Require Import List Bool Lia sets nfa dfa reversing.
Include ListNotations.


Fixpoint n2dfa'_loop {A B} eq eq' (g:nfa_comp_list A B) f Q l :=
  match l with
  | nil => nil
  | a::l => match (ext_transition eq eq' g Q [a]) with
            | nil => n2dfa'_loop eq eq' g f Q l
            | Q' => trans Q a Q'::f Q' ++ n2dfa'_loop eq eq' g f Q l
            end
  end.

Fixpoint n2dfa' {A B} eq eq' (g:nfa_comp_list A B) n Q :=
  match n with
  | O => nil
  | S n =>
    n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) Q (alphabet g)
  end.


Lemma n2dfa'_loop_in {A B} eq eq' (g:nfa_comp_list A B) f Q l a :
  In a l -> ext_transition eq eq' g Q [a] <> nil ->
  In (trans Q a (ext_transition eq eq' g Q [a])) (n2dfa'_loop eq eq' g f Q l).
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

Lemma in_n2dfa'_loop {A B} eq eq' (g:nfa_comp_list A B) f Q l c :
  In c (n2dfa'_loop eq eq' g f Q l) ->
  exists Q' a, In a l /\ Q' <> nil /\ Q' = ext_transition eq eq' g Q [a] /\
  In c (trans Q a Q'::f Q').
Proof.
  Opaque ext_transition.
  intros.
  induction l as [|b l].
  1: destruct H.
  simpl in H; destruct (ext_transition eq eq' g Q [b]) eqn:H0.
  1: apply IHl in H; destruct H as [Q' [a H]]; exists Q', a; intuition.
  replace (trans Q b (a :: l0) :: f (a :: l0) ++ n2dfa'_loop eq eq' g f Q l) with
  ((trans Q b (a :: l0) :: f (a :: l0)) ++ n2dfa'_loop eq eq' g f Q l) in H.
  2: auto.
  apply in_app_or in H; destruct H.
  - exists (a::l0), b; repeat split.
    1,3,4: intuition.
    intros contra; discriminate.
  - apply IHl in H; destruct H as [Q' [d H]]; exists Q', d; intuition.
  Transparent ext_transition.
Qed.

Lemma in_trans_n2dfa' {A B} eq eq' (g:nfa_comp_list A B) Q0 Q Q' n a :
  In (trans Q a Q') (n2dfa' eq eq' g n Q0) ->
  In a (alphabet g) /\ Q' <> nil /\ Q' = ext_transition eq eq' g Q [a].
Proof.
  Opaque ext_transition.
  intros;
  generalize dependent Q0;
  generalize dependent Q';
  generalize dependent Q;
  induction n; intros.
  1: destruct H.
  apply in_n2dfa'_loop in H;
  destruct H as [Q'' [b [H [H0 [H1 [H2|H2]]]]]].
  1: injection H2; intros; subst; intuition.
  apply IHn in H2; auto.
  Transparent ext_transition.
Qed.

Lemma n2dfa'_new_path {A B} eq eq' (g:nfa_comp_list A B) n w Q q q' :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  length w <= n -> In q Q -> path g q q' w ->
  exists Q', In q' Q' /\ path (n2dfa' eq eq' g n Q) Q Q' w.
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
        destruct H2.
        - subst; apply in_or_app; left;
          apply transition_in; intuition.
        - apply in_or_app; right; intuition.
      }
      Opaque ext_transition.
      simpl n2dfa'.
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
      1: apply n2dfa'_loop_in; auto.
      induction (alphabet g).
      1: destruct H6.
      simpl n2dfa'_loop.
      destruct H6.
      * subst; clear IHl; destruct (ext_transition eq eq' g Q [a]) eqn:H8.
        1: destruct H7; auto.
        symmetry in H8; subst.
        replace (trans Q a (a0 :: l0) :: n2dfa' eq eq' g n (a0 :: l0) ++ n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) Q l) with
        ([trans Q a (a0 :: l0)] ++ n2dfa' eq eq' g n (a0 :: l0) ++ n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) Q l).
        2: auto.
        apply path_app; right; apply path_app; left; intuition.
      * destruct (ext_transition eq eq' g Q [a0]).
        1: intuition.
        replace (trans Q a0 (a1 :: l0) :: n2dfa' eq eq' g n (a1 :: l0) ++ n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) Q l) with
        ([trans Q a0 (a1 :: l0)] ++ n2dfa' eq eq' g n (a1 :: l0) ++ n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) Q l).
        2: auto.
        apply path_app; right; apply path_app; right; intuition.
      Transparent ext_transition.
Qed.

Lemma n2dfa'_old_path {A B} eq eq' (g:nfa_comp_list A B) n w Q Q' q' :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  In q' Q' -> path (n2dfa' eq eq' g n Q) Q Q' w ->
  exists q, In q Q /\ path g q q' w.
Proof.
  intros;
  generalize dependent q';
  induction H2; intros.
  1: exists q'; split; try constructor; auto.
  apply in_trans_n2dfa' in H1; destruct H1 as [H1 [_ H4]].
  rewrite H4 in H3.
  apply in_transition_ext in H3.
  2,3: auto.
  destruct H3 as [q'' [H3 H5]].
  apply IHpath in H3.
  destruct H3 as [q H3].
  exists q; split.
  2: apply path_next with q''.
  1-3: intuition.
Qed.


Fixpoint n2dfa'_loop_op {A B} eq eq' (g:nfa_comp_list A B) f h Q l :=
  match l with
  | nil => nil
  | a::l => match (ext_transition eq eq' g Q [a]) with
            | nil => n2dfa'_loop_op eq eq' g f h Q l
            | _Q' => let Q' := h _Q' in
                     trans Q a Q'::f Q' ++ n2dfa'_loop_op eq eq' g f h Q l
            end
  end.

Fixpoint n2dfa'_op {A B} eq eq' (g:nfa_comp_list A B) l Q n :=
  match n with
  | O => nil
  | S n =>
    if inb (lists_eq eq) Q l then
      nil
    else
      n2dfa'_loop_op eq eq' g (fun Q' => n2dfa'_op eq eq' g (Q::l) Q' n) (fun Q' => get_set eq Q' (Q::l)) Q (alphabet g)
  end.

(*Definition visited {A B} (eq:A->A->bool) (eq':B->B->bool) (g:nfa_comp_list A B)
(L:nfa_comp_list (list A) B) (l:list (list A)) : Prop :=
  (forall Q, In Q l -> forall a, ext_transition eq eq' g Q [a] = nil \/
    exists Q', eq_sets Q' (ext_transition eq eq' g Q [a]) /\ In (trans Q a Q') L) /\
  (forall Q a Q', In (trans Q a Q') L -> eq_sets Q' (ext_transition eq eq' g Q [a]) /\ In Q l).

Lemma n2dfa'_trans {A B} eq eq' (g:nfa_comp_list A B) Q Q1 a Q2 n :
  In (trans Q1 a Q2) (n2dfa' eq eq' g n Q) ->
  Q2 = ext_transition eq eq' g Q1 [a] /\ Q2 <> nil.
Proof.
Admitted.

Lemma n2dfa'_op_correct {A B} eq eq' (g:nfa_comp_list A B) n :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  forall  Q0 Q1 Q2 a l L,
  In (trans Q1 a Q2) (n2dfa' eq eq' g n Q0) ->
  visited eq eq' g L l ->
  exists Q3 Q4, eq_sets Q1 Q3 /\ eq_sets Q2 Q4 /\ In (trans Q3 a Q4) (L++n2dfa'_op eq eq' g l Q0 n).
Proof.
  intro H10; induction n; intros.
  1: destruct H.
  assert (Q1 = Q0 \/ exists b Q5, Q5 = ext_transition eq eq' g Q0 [b] /\ In (trans Q1 a Q2) (n2dfa' eq eq' g n Q5)).
    admit.
  destruct H1 as [H1|[b [Q5 [H1 H2]]]].
  - subst; exists Q0; simpl.
    destruct (inb (lists_eq eq) Q0 l) eqn:H1.
    + destruct H0 as [H0 H2].
      apply (inb_correct (lists_eq eq) Q0 l (lists_eq_correct H10)) in H1.
      assert (ext_transition eq eq' g Q0 [a] = [] \/ (exists Q' : list A, eq_sets Q' (ext_transition eq eq' g Q0 [a]) /\ In (trans Q0 a Q') L)).
        auto.
      destruct H3.
      * apply n2dfa'_trans in H; destruct H as [H H4];
        rewrite <- H3 in H4; apply H4 in H; destruct H.
      * destruct H3 as [Q4 H3].
        exists Q4; intuition.
        1: split; auto.
        apply n2dfa'_trans in H; destruct H as [H _];
        split; intros.
        1: apply H4; rewrite <- H; auto.
        apply H4 in H3; rewrite H; auto.
    + simpl in H.
      admit.
  - assert (exists L', visited eq eq' g L' [Q0]).
      admit.
    destruct H3 as [L' H3].
    assert (visited eq eq' g (L++L') (Q0::l)). {
      destruct H3 as [H3 H4]; destruct H0 as [H5 H6]; split; intros.
      - destruct H0.
        + subst; destruct H3 with Q a0.
          1,2: intuition.
          right; destruct H0 as [Q' H0]; exists Q'; intuition.
        + destruct H5 with Q a0.
          1,2: intuition.
          right; destruct H7 as [Q' H7]; exists Q'; intuition.
      - apply in_app_or in H0; destruct H0.
        1: destruct H6 with Q a0 Q'; intuition.
        destruct H4 with Q a0 Q'.
        1: auto.
        destruct H8; subst; intuition; destruct H8.
    }
    pose proof H4.
    apply (IHn Q5 Q1 Q2 a (Q0::l) (L++L') H2) in H5.
    destruct H5 as [Q3 [Q4 [H5 [H6 H7]]]]; exists Q3, Q4; split.
    2: split.
    1,2: auto.
    clear H5 H6 H2.
Admitted.


Lemma n2dfa'kdsdsakdksa {A B} eq eq' (g:nfa_comp_list A B) q q' w :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  path g q q' w ->
  exists Q Q', In q Q /\ In q' Q' /\ path (n2dfa' eq eq' g nil Q (length w)) Q Q' w.
Proof.
  intros.
  induction H1.
  - admit.
  - destruct IHpath as [Q [Q' [H3 [H4 H5]]]]; exists Q.




Lemma n2dfa'_new_path {A B} eq eq' (g:nfa_comp_list A B) n w :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) -> (forall a b, a=b <-> eq' a b=true) ->
  length w <= n ->
  forall q q', path g q q' w ->
  exists Q Q', In q Q /\ In q' Q' /\ path (n2dfa' eq eq' g nil Q n) Q Q' w.
Proof.
  intros.
  induction H2.
  - exists [q], [q]. admit.
  - assert (length w <= n).
      rewrite app_length in H1; lia.
    apply IHpath in H4; clear IHpath; destruct H4 as [Q [Q' [H4 [H5 H6]]]];
    exists Q.
    assert (exists Q'', In q3 Q'' /\ In (trans Q' a Q'') (n2dfa' eq eq' g [] Q n)). {
      generalize dependent (@nil (list A)).
      induction n; intros.
      - admit.
      - inversion H1.
        + subst. admit.
        + subst. specialize (IHn H1).


      replace (length (w ++ [a])) with (S (length w)) in H1.
      2: rewrite app_length; simpl; lia.
      induction n.
      - admit.
      - inversion H1.
        2: subst; apply IHn in H8.
        + admit.
        + destruct H8 as [Q'' [H9 H10]]; exists Q''; split.
          1: auto.
          clear H9 IHn H6 H5 H4 H3 H2 H1.
          admit.
        + clear H8 IHn H5 H4 H3 H2 H1.
          induction n.
          * simpl. simpl in H6.
    }
    destruct H7 as [Q'' [H7 H8]]; exists Q''; repeat split.
    3: apply path_next with Q'.
    1-4: auto.
Admitted.*)

Definition n2dfa {A B} (eq:A->A->bool) (eq':B->B->bool) (g:nfa_comp_list A B) : nfa_comp_list (list A) B.
Admitted.

Lemma n2dfa_nil {A B} eq eq' {g:nfa_comp_list A B} :
  accept_states g = [] -> n2dfa eq eq' g = [].
Proof.
Admitted.

Lemma n2dfa_states {A B eq eq'} {g:nfa_comp_list A B} Q :
  In Q (states (n2dfa eq eq' (revert_nfa g))) ->
  forall q, In q Q -> In q (states g).
Proof.
Admitted.

Lemma n2dfa_eq_states {A B} eq eq' (g:nfa_comp_list A B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  let brz := (n2dfa eq eq' (revert_nfa g)) in
  In Q1 (states brz) -> In Q2 (states brz) ->
  eq_sets Q1 Q2 -> Q1 = Q2.
Proof.
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
Admitted.