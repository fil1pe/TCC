Require Import Coq.Init.Nat Coq.Lists.List Omega DFA.
Import ListNotations.


Module Type QS <: DFA.

  Parameter states_num_minus_1 : nat.

  Parameter events_num_minus_1 : nat.

  Parameter transition : state->event->state.

  Parameter is_marked : state->bool.

  Parameter count_event : event->Z.

  Parameter n : Z.

  Parameter n0 : Z.

End QS.


Require BinIntDef.
Local Open Scope Z_scope.

Module BufferUtils (G : QS).

  Fixpoint count_buffer w :=
    match w with
       []  => 0                               |
      e::w => G.count_event e + count_buffer w
    end.

  Lemma count_buffer_distr : forall w1 w2,
    count_buffer (w1 ++ w2) = count_buffer w1 + count_buffer w2.
  Proof.
    intros w1 w2.
    induction w1 as [|e w1 IHw1].
    - reflexivity.
    - simpl; rewrite IHw1; omega.
  Qed.

  Lemma count_buffer_distr' : forall w e,
    count_buffer (w ++ [e]) = count_buffer w + G.count_event e.
  Proof.
    intros w e; rewrite count_buffer_distr; simpl; omega.
  Qed.

End BufferUtils.