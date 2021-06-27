Require Import List Bool Lia sets nfa.
Include ListNotations.

Definition normalize_state {A B} eq (g:nfa_comp_list (list A) B) Q :=
  get_set eq Q (states g).

Lemma normalize_state_or {A B} eq (g:nfa_comp_list (list A) B) Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  normalize_state eq g Q = Q \/ In (normalize_state eq g Q) (states g).
Proof.
  unfold normalize_state; intros; generalize dependent (states g); intros; induction l.
  1: left; intuition.
  simpl; destruct (eq_setsb eq Q a).
  1: right; left; auto.
  destruct IHl; intuition.
Qed.

Lemma normalize_state_eq_sets {A B} eq (g:nfa_comp_list (list A) B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  (exists Q1', eq_sets Q1 Q1' /\ In Q1' (states g)) ->
  (exists Q2', eq_sets Q2 Q2' /\ In Q2' (states g)) ->
  eq_sets Q1 Q2 ->
  normalize_state eq g Q1 = normalize_state eq g Q2.
Proof.
  unfold normalize_state; intros; generalize dependent (states g); intros; induction l.
  1: destruct H0 as [Q1' [_ []]].
  simpl; assert (eq_setsb eq Q1 a = eq_setsb eq Q2 a). {
    destruct (eq_setsb eq Q1 a) eqn:H3, (eq_setsb eq Q2 a) eqn:H4.
    1,4: auto.
    - apply eq_setsb_correct in H3.
      2: auto.
      assert (eq_setsb eq Q2 a = true).
      2: rewrite H4 in H5; discriminate.
      apply eq_setsb_correct.
      1: auto.
      apply eq_sets_transitive with Q1; auto.
    - apply eq_setsb_correct in H4.
      2: auto.
      assert (eq_setsb eq Q1 a = true).
      2: rewrite H3 in H5; discriminate.
      apply eq_setsb_correct.
      1: auto.
      apply eq_sets_transitive with Q2.
      1: apply eq_sets_comm.
      1,2: auto.
  }
  destruct (eq_setsb eq Q2 a) eqn:H4; rewrite H3.
  1: auto.
  apply IHl.
  - clear H1; destruct H0 as [Q1' [H0 [H1|H1]]]; subst.
    + assert (eq_setsb eq Q1 Q1' = true).
        apply eq_setsb_correct; auto.
      rewrite H1 in H3; discriminate.
    + exists Q1'; intuition.
  - clear H0; destruct H1 as [Q2' [H0 [H1|H1]]]; subst.
    + assert (eq_setsb eq Q2 Q2' = true).
        apply eq_setsb_correct; auto.
      rewrite H1 in H4; discriminate.
    + exists Q2'; intuition.
Qed.

Fixpoint normalize {A B} eq (g g':nfa_comp_list (list A) B) :=
  match g with
  | nil => nil
  | state Q::g => state (normalize_state eq g' Q)::normalize eq g g'
  | symbol a::g => symbol a::normalize eq g g'
  | start Q::g => start (normalize_state eq g' Q)::normalize eq g g'
  | accept Q::g => accept (normalize_state eq g' Q)::normalize eq g g'
  | trans Q a Q'::g => trans (normalize_state eq g' Q) a (normalize_state eq g' Q')::normalize eq g g'
  end.

Lemma in_normalize {A B} eq (g g':nfa_comp_list (list A) B) Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In Q (states (normalize eq g g')) ->
  exists Q', Q = normalize_state eq g' Q' /\ eq_sets Q Q'.
Proof.
  intros; generalize dependent g'; induction g; intros.
  1: destruct H0.
  destruct a.
  - simpl in H0; destruct H0.
    2: apply IHg; auto.
    exists q; split.
    1: symmetry; auto.
    rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
  - apply IHg; auto.
  - simpl in H0; destruct H0.
    2: apply IHg; auto.
    exists q; split.
    1: symmetry; auto.
    rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
  - simpl in H0; destruct H0.
    2: apply IHg; auto.
    exists q; split.
    1: symmetry; auto.
    rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
  - simpl in H0; destruct H0.
    2: simpl in H0; destruct H0.
    3: apply IHg; auto.
    1: exists q; split.
    1: symmetry; auto.
    1: rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
    exists q'; split.
    symmetry; auto.
    rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
Qed.

Lemma normalize_eq_sets_generic {A B} eq (g g':nfa_comp_list (list A) B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In Q1 (states (normalize eq g g')) -> In Q1 (states g') ->
  In Q2 (states (normalize eq g g')) -> In Q2 (states g') ->
  eq_sets Q1 Q2 ->
  Q1 = Q2.
Proof.
  intros.
  apply in_normalize in H0; apply in_normalize in H2.
  2-4: auto.
  destruct H0 as [Q1' [H0 H5]]; destruct H2 as [Q2' [H2 H6]]; subst.
  apply normalize_state_eq_sets.
  1: auto.
  - exists (normalize_state eq g' Q1'); split.
    1: apply eq_sets_comm.
    1,2: auto.
  - exists (normalize_state eq g' Q2'); split.
    1: apply eq_sets_comm.
    1,2: auto.
  - apply eq_sets_transitive with (normalize_state eq g' Q1').
    1: auto.
    apply eq_sets_transitive with (normalize_state eq g' Q2').
    1: apply eq_sets_comm; auto.
    auto.
Qed.

Lemma normalize_eq_sets {A B} eq (g:nfa_comp_list (list A) B) Q1 Q2 :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In Q1 (states (normalize eq g g)) ->
  In Q2 (states (normalize eq g g)) ->
  eq_sets Q1 Q2 ->
  Q1 = Q2.
Proof.
  intros H.
  assert (forall Q g', In Q (states (normalize eq g g')) -> In Q (states g') \/ In Q (states g)). {
    intros; generalize dependent g'; induction g; intros.
    1: destruct H0.
    destruct a.
    - destruct H0.
      + simpl; destruct (normalize_state_or eq g' q H).
        1: right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + apply IHg in H0; destruct H0.
        1: left; auto.
        right; right; auto.
    - apply IHg; auto.
    - destruct H0.
      + simpl; destruct (normalize_state_or eq g' q H).
        1: right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + apply IHg in H0; destruct H0.
        1: left; auto.
        right; right; auto.
    - destruct H0.
      + simpl; destruct (normalize_state_or eq g' q H).
        1: right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + apply IHg in H0; destruct H0.
        1: left; auto.
        right; right; auto.
    - destruct H0.
      2: destruct H0.
      + simpl; destruct (normalize_state_or eq g' q H).
        1: right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + simpl; destruct (normalize_state_or eq g' q' H).
        1: right; right; left; rewrite <- H1; auto.
        left; rewrite <- H0; auto.
      + apply IHg in H0; destruct H0.
        1: left; auto.
        right; right; intuition.
  }
  intros; apply normalize_eq_sets_generic with eq g g.
  1,2,4,6: auto.
  - apply H0 in H1; destruct H1; auto.
  - apply H0 in H2; destruct H2; auto.
Qed.

Lemma accept_in_normalize {A B} eq (g:nfa_comp_list (list A) B) l Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In (accept Q) (normalize eq g l) -> exists Q', eq_sets Q Q' /\ In (accept Q') g.
Proof.
  intros;
  generalize dependent l;
  induction g; intros.
  1: destruct H0.
  destruct a.
  - destruct H0.
    1: discriminate.
    apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
    1: intuition.
    right; intuition.
  - destruct H0.
    1: discriminate.
    apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
    1: intuition.
    right; intuition.
  - destruct H0.
    1: discriminate.
    apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
    1: intuition.
    right; intuition.
  - destruct H0.
    + injection H0; intros; subst; exists q; split.
      2: intuition.
      apply eq_sets_comm, get_set_eq; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      1: intuition.
      right; intuition.
  - destruct H0.
    1: discriminate.
    apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
    1: intuition.
    right; intuition.
Qed.

Lemma state_in_normalize {A B} eq (g:nfa_comp_list (list A) B) l Q :
  (forall q1 q2, q1=q2 <-> eq q1 q2=true) ->
  In Q (states (normalize eq g l)) -> exists Q', eq_sets Q Q' /\ In Q' (states g).
Proof.
  intros;
  generalize dependent l;
  induction g; intros.
  1: destruct H0.
  destruct a.
  - destruct H0.
    + exists q; split.
      1: rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
      left; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      1: intuition.
      right; intuition.
  - apply IHg in H0; auto.
  - destruct H0.
    + exists q; split.
      1: rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
      left; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      1: intuition.
      right; intuition.
  - destruct H0.
    + exists q; split.
      1: rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
      left; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      1: intuition.
      right; intuition.
  - destruct H0.
    2: destruct H0.
    + exists q; split.
      1: rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
      left; auto.
    + exists q'; split.
      1: rewrite <- H0; apply eq_sets_comm, get_set_eq; auto.
      right; left; auto.
    + apply IHg in H0; destruct H0 as [Q' H0]; exists Q'; split.
      1: intuition.
      right; intuition.
Qed.

Lemma normalize_start_states_nil {A B} eq (g:nfa_comp_list (list A) B) l :
  start_states g = nil -> start_states (normalize eq g l) = nil.
Proof.
  intros; generalize dependent l; induction g; intros.
  1: auto.
  destruct a.
  1,2,4,5: apply IHg, H.
  discriminate.
Qed.













