Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.
(*Unset Strict Implicit.
Unset Printing Implicit Defensive.*)

Inductive state {Q : Type} :=
  sink_state | proper_state (q : Q).

Record dfa (Q E : Type) := {
  transition: Q -> E -> @state Q;
  initial_state: Q;
  is_marked: Q -> bool
}.

(* Extended transition function: *)

Fixpoint extended_transition {Q E : Type} (g : dfa Q E) q w : state :=
  match q with
    sink_state => sink_state |
    proper_state q' =>  match w with
                          [] => proper_state q' |
                          e::w' =>
                            extended_transition g ((transition g) q' e) w'
                        end
  end.

Lemma transition_over_sink_state:
  forall (Q E : Type) (g : dfa Q E) w,
    extended_transition g sink_state w = sink_state.
Proof.
  intros Q E g w.
  destruct w.
  reflexivity.
  reflexivity.
Qed.

Theorem dist_extended_transition:
  forall (Q E : Type) (g : dfa Q E) w w' q,
    extended_transition g q (w ++ w') =
    extended_transition g (extended_transition g q w) w'.
Proof.
  intros Q E g w.
  induction w as [|e w IHw].
  - intros w' q. simpl. destruct q. reflexivity. reflexivity.
  - intros w' q. simpl. destruct q.
    + symmetry. apply transition_over_sink_state.
    + rewrite IHw. reflexivity.
Qed.

(* Generated language: *)

Definition in_language {Q E : Type} (g : dfa Q E) w : Prop :=
  ~ extended_transition g (proper_state (initial_state g)) w = sink_state.

Notation " x ==> g " := (in_language g x) (at level 60). (* ? *)

Theorem prefix_closed:
  forall (Q E : Type) (g : dfa Q E) w w',
    (w ++ w') ==> g -> w ==> g.
Proof.
  unfold in_language, not.
  intros Q E g w w' H0 H1.
  rewrite dist_extended_transition in H0. rewrite H1 in H0. apply H0.
  destruct w'. reflexivity. reflexivity.
Qed.

(*
Example:

Inductive states1 : Type :=
  q0 (* initial state *) |
  q1 |
  q2 (* final state *).

Inductive events1 : Type := a | b.

Definition transition1 (q:states1) (e:events1) : state :=
  match q, e with
  q0, a => proper_state q1 |
  q1, b => proper_state q2 |
  q2, a => proper_state q1 |
  _, _ => sink_state
  end.

Definition is_marked1 (q:states1) : bool :=
  match q with
  q2 => true |
  _ => false
  end.

Definition dfa1 :=
  {| transition := transition1; initial_state := q0; is_marked := is_marked1 |}.

Check dfa1.

Compute extended_transition dfa1 (proper_state q0) [a;b;a;b;a;b].

Theorem dfa1_test1 : [a;b;a;b;a;b] ==> dfa1.
Proof.
  unfold in_language.
  unfold not.
  intros H.
  discriminate H.
Qed.
*)

