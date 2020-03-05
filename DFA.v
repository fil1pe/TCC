Require Import Coq.Init.Nat Coq.Lists.List Omega.
Require BinIntDef.
Local Open Scope Z_scope.

Inductive event := add | rem | oth.

Definition count_event e :=
  match e with
    add =>  1 |
    rem => -1 |
    oth =>  0
  end.

Definition states_num := 6%nat.
(* Axiom states_num : nat. *)

Definition transition (q:nat) (e:event) :=
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