Require Import Coq.Init.Nat Coq.Lists.List Omega.
Import ListNotations.
Require BinIntDef.


Definition state := nat.

Definition event := nat.


Module Type DFA.

Parameter states_num_minus_1 : nat.

Parameter events_num_minus_1 : nat.

Parameter transition : state->event->state.

Parameter is_marked : state->bool.

End DFA.


Module DFAUtils (G : DFA).

Definition states_num := S G.states_num_minus_1.

Definition events_num := S G.events_num_minus_1.

Definition is_sink_state (q:state) := q >= states_num.

Definition is_sink_stateb (q:state) := states_num <=? q.

Definition is_valid_event (e:event) := e <? events_num.

Fixpoint xtransition q w :=
  if is_sink_stateb q then states_num else
    match w with
      e::w => if is_valid_event e then
                xtransition (G.transition q e) w
              else
                states_num |
      []  => q
    end.

Definition ixtransition := xtransition 0.

Fixpoint transition_list' q events_num :=
  match events_num with
    S n => (n, xtransition q [n]) :: transition_list' q n |
     O  => []
  end.

Definition transition_list q := transition_list' q events_num.

Lemma ixtransition_nil__0 : ixtransition [] = 0.
Proof.
  unfold ixtransition.
  reflexivity.
Qed.

Definition is_proper_transition q e := ~ is_sink_state (xtransition q [e]).

Definition is_generated w := ~ is_sink_state (ixtransition w).

Lemma is_sink_stateb__is_sink_state : forall q,
  is_sink_stateb q = true <-> is_sink_state q.
Proof.
  intro q.
  split; intro H.
  - apply leb_complete, H.
  - apply leb_correct, H.
Qed.

Lemma isnt_sink_stateb__isnt_sink_state : forall q,
  is_sink_stateb q = false <-> ~ is_sink_state q.
Proof.
  intro q.
  split; intro H.
  - unfold not.
    intro contra.
    apply is_sink_stateb__is_sink_state in contra.
    rewrite H in contra.
    discriminate contra.
  - unfold is_sink_state in H.
    unfold is_sink_stateb.
    apply leb_iff_conv.
    apply not_ge in H.
    apply H.
Qed.

Lemma first_sink_state : is_sink_stateb states_num = true.
Proof.
  apply is_sink_stateb__is_sink_state.
  unfold is_sink_state.
  omega.
Qed.

Lemma xtransition_sink_state : forall w q,
  is_sink_stateb q = true -> xtransition q w = states_num.
Proof.
  intros w q H.
  destruct w.
  - simpl. rewrite H. reflexivity.
  - simpl.
    rewrite H.
    reflexivity.
Qed.

Theorem xtransition_distr : forall w w' q,
  xtransition q (w ++ w') = xtransition (xtransition q w) w'.
Proof.
  intros w w'.
  induction w; intro q.
  - simpl. destruct (is_sink_stateb q) eqn:eq.
    + pose proof first_sink_state as H.
      apply xtransition_sink_state with (w:=w') in H.
      apply xtransition_sink_state with (w:=w') in eq.
      rewrite eq, H.
      reflexivity.
    + reflexivity.
  - simpl.
    pose proof first_sink_state as H.
    apply xtransition_sink_state with (w:=w') in H.
    destruct (is_sink_stateb q) eqn:eq.
    + rewrite H. reflexivity.
    + destruct (is_valid_event a).
      * apply IHw.
      * rewrite H. reflexivity.
Qed.

Theorem ixtransition_distr : forall w w',
  ixtransition (w ++ w') = xtransition (ixtransition w) w'.
Proof.
  intros w w'.
  unfold ixtransition.
  apply xtransition_distr.
Qed.

Theorem prefix_closed : forall w w',
  is_generated (w ++ w') -> is_generated w.
Proof.
  unfold is_generated, ixtransition, not.
  intros w w' H H0.
  rewrite xtransition_distr in H.
  apply is_sink_stateb__is_sink_state in H0.
  apply H, is_sink_stateb__is_sink_state.
  destruct w'; simpl; rewrite H0; apply first_sink_state.
Qed.

End DFAUtils.