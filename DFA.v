Require Import Coq.Init.Nat Coq.Lists.List Omega.
Require BinIntDef.
Local Open Scope Z_scope.

Definition state := nat.

Definition states_num := 6%nat.
(* Axiom states_num : nat. *)

Inductive event := add | rem | oth.

Definition count_event e :=
  match e with
    add =>  1 |
    rem => -1 |
    oth =>  0
  end.

Definition transition q e :=
  match q, e with
    0%nat, add => 5%nat |
    0%nat, rem => 1%nat |
    1%nat, add => 2%nat |
    2%nat, rem => 3%nat |
    3%nat, add => 4%nat |
    4%nat, rem => 1%nat |
    5%nat, add => 1%nat |
      _  ,  _  => 10%nat
  end.
(* Axiom transition : nat->event->nat. *)

Definition is_marked (q:nat) :=
  match q with
    _ => false
  end.

Definition DFA := (states_num, transition, is_marked).

(*
  The initial state of the DFA is the state 0.
  The sink state is any state n where n >= states_num.
*)