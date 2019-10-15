Record dfa (Q E : Type) := {
  delta : Q -> E -> Q;
  initial_state : Q;
  is_final : Q -> bool
}.

(* Example *)

Inductive states1 : Type :=
  | q0 (* initial state *)
  | q1
  | q2 (* final state *)
  | q3. (* ? *)

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
  {| delta := delta1; initial_state := q0; is_final := is_final1 |}.

Check dfa1.



