Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record dfa (Q E : Type) := {
  delta : Q -> E -> Q;
  initial_state : Q;
  is_final : Q -> bool;
  sink_state : Q
}.

(* Extended delta:*)

Fixpoint delta' {Q E : Type} (g : dfa Q E) (q : Q) (w : list E) : Q :=
  match w with
  | [] => q
  | e::w' => delta' g (g.(delta) q e) w'
  end.

(* Generated language: *)

Definition in_language {Q E : Type} (g : dfa Q E) (w : list E) : Prop :=
  ~ delta' g g.(initial_state) w = g.(sink_state).

(* Example:

Inductive states1 : Type :=
  | q0 (* initial state *)
  | q1
  | q2 (* final state *)
  | q3.

Inductive events1 : Type :=
  | a
  | b.

Definition delta1 (q:states1) (e:events1) : states1 :=
  match q, e with
  | q0, a => q1
  | q1, b => q2
  | q2, a => q1
  | _, _ => q3
  end.

Definition is_final1 (q:states1) : bool :=
  match q with
  | q2 => true
  | _ => false
  end.

Definition dfa1 :=
  {| delta := delta1; initial_state := q0; is_final := is_final1; sink_state := q3 |}.

Check dfa1.

Compute delta' dfa1 q0 [a;b;a;b;a;b].

Theorem dfa1_test1 : in_language dfa1 [a;b;a;b;a;b].
Proof.
  unfold in_language, not.
  intros.
  discriminate H.
Qed.

*)

Require Export Arith_base.
Require Import BinPos BinInt BinNat Pnat Nnat.
Local Open Scope Z_scope.

Inductive events {E : Type} : Type :=
  | add
  | rem
  | other (e : E).

Fixpoint buffer_count {E : Type} (w : list (@events E)) : Z :=
  match w with
  | [] => 0
  | add::w' => buffer_count w' + 1
  | rem::w' => buffer_count w' - 1
  | _::w' => buffer_count w'
  end.

Check [add;rem].

(* not working *)

Compute buffer_count [rem;add;add].