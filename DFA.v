Require Import Coq.Init.Nat Coq.Lists.List Omega.
Import ListNotations.
Require BinIntDef.

Definition state := nat.
Axiom states_num_minus_1 : nat.
(* Definition states_num_minus_1 := 7. *)
Definition states_num := S states_num_minus_1.

Inductive event := add | rem | oth (e : nat).
Axiom oth_events_num : nat.
(* Definition oth_events_num := 0. *)

Axiom transition : state->event->state.
(* Definition transition (q:state) e : state :=
  match q, e with
    0, add => 1 |
    1, add => 2 |
    2, rem => 3 |
    3, rem => 1 |
    0, rem => 4 |
    4, add => 5 |
    5, add => 6 |
    6, add => 1 |
    _,  _  => 8
  end. *)

Axiom is_marked : state->bool.

Definition DFA := (states_num, transition, is_marked).

(*
  The states of the DFA are 0, 1, ... and states_num-1.
  The initial state is the state 0.
  The sink state is the state n where n = states_num.
  All transitions to states n where n > states_num will be considered
  transitions to the sink state.
  The events are add, rem, oth 0, oth 1, ... and oth (oth_events_num-1).
*)

Definition is_sink_state (q:state) := q >= states_num.

Definition is_sink_stateb (q:state) := states_num <=? q.

Definition event_eq e1 e2 :=
  match e1, e2 with
     add  ,  add   => true     |
     rem  ,  rem   => true     |
    oth e1, oth e2 => e1 =? e2 |
      _   ,    _   => false
  end.

Definition is_valid_event e :=
  match e with
     add  => true               |
     rem  => true               |
    oth e => e <? oth_events_num
  end.

Fixpoint xtransition q w :=
  if is_sink_stateb q then states_num else
    match w with
      e::w => if is_valid_event e then
                xtransition (transition q e) w
              else
                states_num |
      []  => q
    end.

Definition ixtransition := xtransition 0.

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
