Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive states {Q : Type} : Type :=
  | sink_state
  | state (q : Q).

Record dfa (Q E : Type) := {
  delta: Q -> E -> @states Q;
  initial_state: Q;
  is_final: Q -> bool
}.

(* Extended transition function: *)

Fixpoint extended_delta {Q E : Type} (g : dfa Q E) (q : @states Q) (w : list E) : @states Q :=
  match q with
  | sink_state => sink_state
  | state q' => match w with
                | [] => state q'
                | e::w' => extended_delta g (g.(delta) q' e) w'
                end
  end.

Lemma extended_delta_sink_state:
  forall (Q E : Type) (g : dfa Q E) w,
    extended_delta g sink_state w = sink_state.
Proof.
  intros.
  destruct w.
  reflexivity.
  reflexivity.
Qed.

Theorem dist_extended_delta:
  forall (Q E : Type) (g : dfa Q E) w w' q,
    extended_delta g q (w ++ w') =
    extended_delta g (extended_delta g q w) w'.
Proof.
  intros.
  generalize dependent q.
  generalize dependent w'.
  induction w.
  - intros. simpl. destruct q. reflexivity. reflexivity.
  - intros. simpl. destruct q.
    + symmetry. apply extended_delta_sink_state.
    + rewrite IHw. reflexivity.
Qed.

(* Generated language: *)

Definition in_language {Q E : Type} (g : dfa Q E) (w : list E) : Prop :=
  ~ extended_delta g (state g.(initial_state)) w = sink_state.

Notation " x ==> g " := (in_language g x) (at level 60). (* ? *)

Theorem prefix_closed:
  forall (Q E : Type) (g : dfa Q E) w w',
    (w ++ w') ==> g -> w ==> g.
Proof.
  unfold in_language, not.
  intros.
  rewrite dist_extended_delta in H. rewrite H0 in H. apply H.
  destruct w'. reflexivity. reflexivity.
Qed.

(*
Example:

Inductive states1 : Type :=
  | q0 (* initial state *)
  | q1
  | q2 (* final state *).

Inductive events1 : Type :=
  | a
  | b.

Definition delta1 (q:states1) (e:events1) : @states states1 :=
  match q, e with
  | q0, a => state q1
  | q1, b => state q2
  | q2, a => state q1
  | _, _ => sink_state
  end.

Definition is_final1 (q:states1) : bool :=
  match q with
  | q2 => true
  | _ => false
  end.

Definition dfa1 :=
  {| delta := delta1; initial_state := q0; is_final := is_final1 |}.

Check dfa1.

Compute extended_delta dfa1 (state q0) [a;b;a;b;a;b].

Theorem dfa1_test1 : [a;b;a;b;a;b] ==> dfa1.
Proof.
  unfold in_language.
  unfold not.
  intros.
  discriminate H.
Qed.
*)

