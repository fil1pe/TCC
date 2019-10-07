(* We can define word as list of events ;-) *)
Inductive word {E:Type} : Type :=
  | empty
  | headw (e : E) (w : @word E).

Notation "e :: w" := (headw e w)
                     (at level 60, right associativity).
Notation "[ ]" := empty.
Notation "[ x ; .. ; y ]" := (headw x .. (headw y empty) ..).



Inductive DFA : Type :=
  | dfa (Q E : Type) (delta : Q->E->Q) (q0 : Q) (Qm : list Q) (n : nat).

Notation "( Q , E , delta , q0 , Qm , n )" := (dfa Q E delta q0 Qm n).



Fixpoint extended_fun {Q E : Type} (f : Q->(@word E)->Q) (q : Q) (w : word)
 : Q :=
  match w with
  | [] => q
  | e::w' => extended_fun f (f q e) w'
  end.



Definition language {E : Type} (G : DFA) : Type :=
  match G with
  | (Q,E,delta,q0,Qm,n) =>
  end.




Inductive events {E : Type} : Type :=
  | add
  | rem
  | other (e : E).



Fixpoint buffer_count {E : Type} (w : @word (@events E)) : nat :=
  match w with
  | [] => 0
  | add::w' => buffer_count w' + 1
  | rem::w' => buffer_count w' - 1
  | _::w' => buffer_count w'
  end.

Compute buffer_count [add;add;rem;rem;rem]. (* shall be -1 *)