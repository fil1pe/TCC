Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Inductive state {Q} :=
  sink_state | proper_state (q : Q).

Record DFA {Q E} := {
  transition: Q -> E -> @state Q;
  initial_state: Q;
  is_marked: Q -> bool
}.

Definition is_proper_transition {Q E} (G:@DFA Q E) q e := exists q',
  proper_state q' = transition G q e.

(* Extended transition function: *)

Fixpoint extended_transition {Q E} (G:@DFA Q E) q w : state :=
  match q with
    sink_state => sink_state |
    proper_state q' =>  match w with
                          [] => proper_state q' |
                          e::w' =>
                            extended_transition G (transition G q' e) w'
                        end
  end.

Lemma extended_transition__transition: forall {Q E} {G:@DFA Q E} q e,
  extended_transition G (proper_state q) [e] = transition G q e.
Proof.
  intros Q E G q e.
  simpl.
  destruct (transition G q e); reflexivity.
Qed.

Lemma transition_sink_state: forall {Q E} (G:@DFA Q E) w,
  extended_transition G sink_state w = sink_state.
Proof.
  intros Q E G w.
  destruct w; reflexivity.
Qed.

Theorem dist_extended_transition: forall {Q E} (G:@DFA Q E) w w' q,
    extended_transition G q (w ++ w') =
    extended_transition G (extended_transition G q w) w'.
Proof.
  intros Q E G w.
  induction w as [|e w IHw].
  - intros w' q. simpl. destruct q; reflexivity.
  - intros w' q. simpl. destruct q.
    + symmetry. apply transition_sink_state.
    + rewrite IHw. reflexivity.
Qed.

(* Generated language: *)

Definition generates {Q E} (G:@DFA Q E) w : Prop :=
  ~ extended_transition G (proper_state (initial_state G)) w = sink_state.

Theorem prefix_closed: forall {Q E} (G:@DFA Q E) w w',
    generates G (w ++ w') -> generates G w.
Proof.
  unfold generates, not.
  intros Q E G w w' H0 H1.
  rewrite dist_extended_transition in H0.
  rewrite H1 in H0.
  apply H0.
  destruct w'; reflexivity.
Qed.

