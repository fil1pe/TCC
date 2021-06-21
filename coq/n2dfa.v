Require Import List Bool Lia sets nfa dfa reversing.
Include ListNotations.


Fixpoint n2dfa'_loop {A B} eq eq' (g:nfa_comp_list A B) f h Q l :=
  match l with
  | nil => nil
  | a::l => match (ext_transition eq eq' g Q [a]) with
            | nil => n2dfa'_loop eq eq' g f h Q l
            | Q'' => let Q' := h Q'' in
                     trans Q a Q'::f Q' ++ n2dfa'_loop eq eq' g f h Q l
            end
  end.

Fixpoint n2dfa' {A B} eq eq' (g:nfa_comp_list A B) n Q :=
  match n with
  | O => nil
  | S n =>
    n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) (fun Q' => Q') Q (alphabet g)
  end.


Lemma n2dfa'_loop_in {A B} eq eq' (g:nfa_comp_list A B) f h Q l a :
  In a l -> ext_transition eq eq' g Q [a] <> nil ->
  In (trans Q a (h (ext_transition eq eq' g Q [a]))) (n2dfa'_loop eq eq' g f h Q l).
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

Lemma in_n2dfa'_loop {A B} eq eq' (g:nfa_comp_list A B) f h Q l c :
  In c (n2dfa'_loop eq eq' g f h Q l) ->
  exists Q' a, In a l /\ Q' <> nil /\ Q' = ext_transition eq eq' g Q [a] /\
  In c (trans Q a (h Q')::f (h Q')).
Proof.
  Opaque ext_transition.
  intros.
  induction l as [|b l].
  1: destruct H.
  simpl in H; destruct (ext_transition eq eq' g Q [b]) eqn:H0.
  1: apply IHl in H; destruct H as [Q' [a H]]; exists Q', a; intuition.
  replace (trans Q b (h (a :: l0)) :: f (h (a :: l0)) ++ n2dfa'_loop eq eq' g f h Q l) with
  ((trans Q b (h (a :: l0)) :: f (h (a :: l0))) ++ n2dfa'_loop eq eq' g f h Q l) in H.
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
      apply path_left with (ext_transition eq eq' g Q [a]). {
        remember (fun Q' : list A => Q') as h eqn:H8.
        replace (trans Q a (ext_transition eq eq' g Q [a])) with
        (trans Q a (h (ext_transition eq eq' g Q [a]))).
        2: rewrite H8; auto.
        apply n2dfa'_loop_in; auto.
      }
      induction (alphabet g).
      1: destruct H6.
      simpl n2dfa'_loop.
      destruct H6.
      * subst; clear IHl; destruct (ext_transition eq eq' g Q [a]) eqn:H8.
        1: destruct H7; auto.
        symmetry in H8; subst.
        replace (trans Q a (a0 :: l0) :: n2dfa' eq eq' g n (a0 :: l0) ++ n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) (fun Q' : list A => Q') Q l) with
        ([trans Q a (a0 :: l0)] ++ n2dfa' eq eq' g n (a0 :: l0) ++ n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) (fun Q' : list A => Q') Q l).
        2: auto.
        apply path_app; right; apply path_app; left; intuition.
      * destruct (ext_transition eq eq' g Q [a0]).
        1: intuition.
        replace (trans Q a0 (a1 :: l0) :: n2dfa' eq eq' g n (a1 :: l0) ++ n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) (fun Q' : list A => Q') Q l) with
        ([trans Q a0 (a1 :: l0)] ++ n2dfa' eq eq' g n (a1 :: l0) ++ n2dfa'_loop eq eq' g (n2dfa' eq eq' g n) (fun Q' : list A => Q') Q l).
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


(* A versão otimizada do algoritmo *)
Fixpoint n2dfa'_op {A B} eq eq' (g:nfa_comp_list A B) l n Q :=
  match n with
  | O => nil
  | S n =>
    if inb (lists_eq eq) Q l then
      nil
    else
      n2dfa'_loop eq eq' g (n2dfa'_op eq eq' g (Q::l) n) (fun Q' => get_set eq Q' (Q::l)) Q (alphabet g)
  end.


Lemma get_set_eq {A} (eq:A->A->bool) s l :
  (forall a b, a=b <-> eq a b = true) ->
  eq_sets s (get_set eq s l).
Proof.
  intros; induction l.
  1: split; auto.
  simpl; destruct (eq_setsb eq s a) eqn:H0.
  2: auto.
  apply eq_setsb_correct in H0; auto.
Qed.

Lemma get_set_correct {A} (eq:A->A->bool) s l :
  (forall a b, a=b <-> eq a b = true) ->
  (get_set eq s l = s) \/
  exists s', get_set eq s l = s' /\ eq_sets s' s /\ inb (lists_eq eq) s' l = true.
Proof.
  intros; induction l.
  1: intuition.
  simpl; destruct (eq_setsb eq s a) eqn:H0.
  - right; exists a; split.
    2: split.
    1: auto.
    1: apply eq_setsb_correct in H0; try apply eq_sets_comm; auto.
    replace (lists_eq eq a a) with true.
    1: auto.
    symmetry; apply lists_eq_correct; auto.
  - destruct IHl as [IHl|[s' H1]].
    1: left; auto.
    right; exists s'; intuition. 
Qed.


Lemma next_n2dfa'_loop {A B} eq eq' (g:nfa_comp_list A B) f h Q l a c :
  ext_transition eq eq' g Q [a] <> nil ->
  In a l ->
  In c (f (h (ext_transition eq eq' g Q [a]))) ->
  In c (n2dfa'_loop eq eq' g f h Q l).
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

Lemma n2dfa'_op_correct {A B} eq eq' (g:nfa_comp_list A B) n Q0 a :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (forall  Q1 Q2,
  In (trans Q1 a Q2) (n2dfa' eq eq' g n Q0) ->
  exists Q3 Q4, eq_sets Q1 Q3 /\ eq_sets Q2 Q4 /\ In (trans Q3 a Q4) (n2dfa'_op eq eq' g [] n Q0)) /\
  (forall Q3 Q4, In (trans Q3 a Q4) (n2dfa'_op eq eq' g [] n Q0) ->
  exists Q1 Q2, eq_sets Q1 Q3 /\ eq_sets Q2 Q4 /\ In (trans Q1 a Q2) (n2dfa' eq eq' g n Q0)).
Proof.
  Opaque ext_transition.
  intros; split; intros.

  {
    generalize dependent Q0;
    induction n; intros.
    1: destruct H0.
    pose proof H0; simpl in H0; apply in_n2dfa'_loop in H0;
    destruct H0 as [Q1' [b [H2 [H3 [H4 H5]]]]].
    destruct H5.
    - injection H0; intros; subst; clear H0 IHn.
      exists Q1; simpl.
      remember (fun Q' : list A => if eq_setsb eq Q' Q1 then Q1 else Q') as h eqn:H20.
      exists (h(ext_transition eq eq' g Q1 [a])); split.
      2: split.
      2: subst; destruct (eq_setsb eq (ext_transition eq eq' g Q1 [a]) Q1) eqn:H4.
      1,3: split; intuition.
      1: apply eq_setsb_correct in H4; auto.
      apply n2dfa'_loop_in; auto.
    - apply IHn in H0; clear IHn.
      destruct H0 as [Q3 [Q4 [H5 [H6 H7]]]]; clear H1.
      admit.
  }

  remember (@nil (list A)) as vis eqn:H1; clear H1.
  generalize dependent Q0;
  generalize dependent vis;
  induction n; intros.
  1: destruct H0.
  simpl in H0; destruct (inb (lists_eq eq) Q0) eqn:H1.
  1: destruct H0.
  remember (fun Q' : list A => if eq_setsb eq Q' Q0 then Q0 else get_set eq Q' vis) as h eqn:H20.
  apply in_n2dfa'_loop in H0.
  destruct H0 as [Q' [b [H4 [H5 [H6 H7]]]]].
  destruct H7.
  - injection H0; intros; subst.
    destruct (eq_setsb eq (ext_transition eq eq' g Q3 [a])) eqn:H10.
    + apply eq_setsb_correct in H10.
      2: auto.
      exists Q3, (ext_transition eq eq' g Q3 [a]).
      split.
      2: split.
      1: split; intuition.
      1: auto.
      simpl; remember (fun Q' : list A => Q') as h eqn:H20.
      replace (ext_transition eq eq' g Q3 [a]) with (h (ext_transition eq eq' g Q3 [a])).
      2: subst; auto.
      apply n2dfa'_loop_in; auto.
    + exists Q3, (ext_transition eq eq' g Q3 [a]).
      split.
      2: split.
      1: split; intuition.
      1: apply get_set_eq; auto.
      simpl; remember (fun Q' : list A => Q') as h eqn:H20.
      replace (ext_transition eq eq' g Q3 [a]) with (h (ext_transition eq eq' g Q3 [a])).
      2: subst; auto.
      apply n2dfa'_loop_in; auto.
  - subst.
    destruct (eq_setsb eq (ext_transition eq eq' g Q0 [b]) Q0) eqn:H10.
    + clear IHn.
      destruct n.
      1: destruct H0.
      simpl in H0.
      assert (lists_eq eq Q0 Q0 = true).
        apply lists_eq_correct; auto.
      rewrite H2, orb_true_l in H0.
      destruct H0.
    + assert ((get_set eq (ext_transition eq eq' g Q0 [b]) vis = ext_transition eq eq' g Q0 [b]) \/ exists s', get_set eq (ext_transition eq eq' g Q0 [b]) vis = s' /\
      eq_sets s' (ext_transition eq eq' g Q0 [b]) /\ inb (lists_eq eq) s' vis = true).
        apply get_set_correct; auto.
      destruct H2.
      * rewrite H2 in H0.
        apply IHn in H0; destruct H0 as [Q1 [Q2 [H0 [H6 H7]]]].
        exists Q1, Q2; split.
        2: split.
        1,2: auto.
        simpl.
        apply next_n2dfa'_loop with b; auto.
      * destruct H2 as [Q'' [H2 [_ H3]]]; subst; destruct n as [|n].
        1: destruct H0.
        simpl in H0; rewrite H3, orb_true_r in H0; destruct H0.
  Transparent ext_transition.
Admitted.


(*Fixpoint pow {B} (w:list B) n :=
  match n with
  | O => nil
  | S n => w ++ pow w n
  end.

Definition max_length {A B} (g:nfa_comp_list A B) :=
  length (states g).

Lemma pumping {A B} (g:nfa_comp_list A B) q1 q3 w :
  is_dfa' g ->
  path g q1 q3 w -> exists w1 w2 w3 n q2, w = w1 ++ (pow w2 n) ++ w3 /\
  path g q1 q2 w1 /\ path g q2 q2 w2 /\ path g q2 q3 w3 /\
  length w2 <= max_length g /\
  length (w1 ++ w3) <= max_length g.
Proof.
Admitted.*)

Lemma path_transitive {A B} (g:nfa_comp_list A B) q1 q2 q3 w1 w2 :
  path g q1 q2 w1 -> path g q2 q3 w2 -> path g q1 q3 (w1 ++ w2).
Proof.
  intros.
  induction H0.
  1: rewrite app_nil_r; auto.
  replace (w1 ++ w ++ [a]) with ((w1 ++ w) ++ [a]).
  2: rewrite app_assoc; auto.
  apply path_next with q2; auto.
Qed.


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