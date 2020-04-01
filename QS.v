Require Import Coq.Lists.List Omega Coq.Bool.Bool.
Import ListNotations.
Require Import DFA.
Local Open Scope Z_scope.

Record qs_dfa {A B} := {
  g : @dfa A B;
  n0 : Z;
  n : Z;
  n_correct : n >= n0;
  count_event : B -> Z;
  count_event_correct : forall e, In e (E g) -> count_event e = 1 \/
                        count_event e = -1 \/ count_event e = 0
}.

Section QS.

Variables (A : Type) (B : Type) (qs : @qs_dfa A B).

Fixpoint count_buffer w :=
  match w with
  | e::w' => (count_event qs e) + count_buffer w'
  | nil => 0
  end.

Lemma count_buffer_distr w1 w2 :
  count_buffer (w1 ++ w2) = count_buffer w1 + count_buffer w2.
Proof.
  induction w1 as [|e w1' IH];
  auto;
  simpl; rewrite IH; omega.
Qed.

Lemma count_buffer_distr' w e :
  count_buffer (w ++ [e]) = count_buffer w + (count_event qs e).
Proof.
  rewrite count_buffer_distr; simpl; omega.
Qed.

End QS.