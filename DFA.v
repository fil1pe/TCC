Require Import Coq.Init.Nat Coq.Lists.List Omega.
Import ListNotations.
Require BinIntDef.

Definition state := nat.

Definition states_num := 6.
(* Axiom states_num : nat. *)

Inductive event := add | rem | oth.

Definition count_event e :=
  match e with
    add =>   1%Z  |
    rem => (-1)%Z |
    oth =>   0%Z
  end.

Definition transition (q:state) e :=
  match q, e with
    0, add => 5 |
    0, rem => 1 |
    1, add => 2 |
    2, rem => 3 |
    3, add => 4 |
    4, rem => 1 |
    5, add => 1 |
    _,  _  => 10
  end.
(* Axiom transition : state->event->state. *)

Definition is_marked (q:state) :=
  match q with
    _ => false
  end.

Definition DFA := (states_num, transition, is_marked).

Definition is_sink_state q := q >= states_num.

Definition is_sink_stateb q := states_num <=? q.

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

Definition is_generated w := ~ is_sink_state (xtransition 0 w).

Theorem xtransition_distr : forall w w' q,
  xtransition q (w ++ w') = xtransition (xtransition q w) w'.
Proof.
  intros w w'.
  induction w as [|e w IHw].
  - reflexivity.
  - intro q.
    simpl.
    apply IHw.
Qed.

Theorem prefix_closed: forall w w',
  is_generated (w ++ w') -> is_generated w.
Proof.
  unfold is_generated, is_sink_state, not.
  intros w w' H.
  

