Require Import Coq.Lists.List Omega Coq.Bool.Bool.
Import ListNotations.
Require Import DFA.
Local Open Scope Z_scope.

Record qs_dfa {A B} := {
  g : @dfa A B;
  n0 : Z;
  n : Z;
  n1 : Z;
  n_correct : n >= n0;
  n1_correct : n1 <= n0;
  count_event : B -> Z
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

Theorem count_word_pow: forall w n,
  count_buffer (word_pow B w n) = (Z.of_nat n) * (count_buffer w).
Proof.
  intros w n.
  induction n as [|n IH]. auto.
  replace (word_pow B w (S n)) with (w ++ word_pow B w n).
  rewrite count_buffer_distr, IH, Nat2Z.inj_succ, <- Zmult_succ_l_reverse;
  omega.
  auto.
Qed.

End QS.