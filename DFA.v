Require Import Coq.Init.Nat Coq.Lists.List Omega.
Import ListNotations.
Require BinIntDef.

Definition state := nat.

Axiom states_num_minus_1 : nat.
(* Definition states_num_minus_1 := 5. *)

Definition states_num := S states_num_minus_1.

Inductive event := add | rem | oth.

(* Definition transition (q:state) e :=
  match q, e with
    0, add => 5 |
    0, rem => 1 |
    1, add => 2 |
    2, rem => 3 |
    3, add => 4 |
    4, rem => 1 |
    5, add => 1 |
    _,  _  => 10
  end. *)
Axiom transition : state->event->state.

(* Definition is_marked (q:state) :=
  match q with
    _ => false
  end. *)
Axiom is_marked : state->bool.

Definition DFA := (states_num, transition, is_marked).

Definition is_sink_state (q:state) := q >= states_num.

Definition is_sink_stateb (q:state) := states_num <=? q.

(*
  The states of the DFA are {0, 1, ..., states_num-1}.
  The initial state is the state 0.
  The sink state is any state n where n >= states_num.
*)

Fixpoint xtransition q w :=
  match w with
    a::w => if is_sink_stateb q then
              q
            else
              xtransition (transition q a) w |
    []  => q
  end.

Definition ixtransition w := xtransition 0 w.

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

Lemma xtransition_sink_state : forall w q,
  is_sink_stateb q = true -> xtransition q w = q.
Proof.
  intros w q H.
  destruct w.
  - reflexivity.
  - simpl.
    rewrite H.
    reflexivity.
Qed.

Theorem xtransition_distr : forall w w' q,
  xtransition q (w ++ w') = xtransition (xtransition q w) w'.
Proof.
  intros w w'.
  induction w as [|e w IHw].
  - reflexivity.
  - intro q.
    simpl.
    destruct (is_sink_stateb q) eqn:H0.
    + symmetry; apply xtransition_sink_state.
      apply H0.
    + apply IHw.
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
  destruct w'.
  - simpl.
    apply H0.
  - simpl.
    rewrite H0.
    apply H0.
Qed.
