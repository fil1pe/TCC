Require Import Coq.Lists.List Omega Coq.Bool.Bool.
Import ListNotations.
Require Import DFA.
Local Open Scope Z_scope.

Module Type QS (dfa : DFA).
  Include DFAUtils dfa.
  
  Variable count_event : dfa.B -> Z.
  Variable n0 : Z.
  Variable n1 : Z.
  Variable n : Z.
  Axiom n_correct : n >= n0.
  Axiom n1_correct : n1 <= n0.
End QS.

Module QSUtils (dfa : DFA).
Include QS dfa.

Fixpoint count_buffer w :=
  match w with
  | e::w' => count_event e + count_buffer w'
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
  count_buffer (w ++ [e]) = count_buffer w + (count_event e).
Proof.
  rewrite count_buffer_distr; simpl; omega.
Qed.

Theorem count_word_pow: forall w n,
  count_buffer (word_pow w n) = (Z.of_nat n) * (count_buffer w).
Proof.
  intros w n;
  induction n as [|n IH]; auto;
  replace (word_pow w (S n)) with (w ++ word_pow w n); auto;
  rewrite count_buffer_distr, IH, Nat2Z.inj_succ, <- Zmult_succ_l_reverse;
  omega.
Qed.

Lemma q0_cycle: forall w n,
  ixtransition w = (q0) -> ixtransition (word_pow w n) = (q0).
Proof.
  intros w n H.
  induction n as [|n IH]. auto.
  unfold ixtransition in *;
  simpl;
  rewrite xtransition_distr, H;
  auto.
Qed.

Fixpoint gen_words q (l:list (list B)) :=
  match l with
  | w::l' => if A_decidable (ixtransition w) q then w::gen_words q l' else gen_words q l'
  | nil => nil
  end.

Lemma gen_words_correct1 q l : forall w,
  l <> nil -> In w (gen_words q l) -> ixtransition w = q.
Proof.
  intros w H H0.
  induction l as [|w' l' IH].
  - contradiction.
  - destruct l' as [|w'' l'].
    + simpl in H0; destruct (A_decidable (ixtransition w') q).
      inversion H0. rewrite <- H1; auto. inversion H1. inversion H0.
    + simpl in *. destruct (A_decidable (ixtransition w') q).
      inversion H0. rewrite <- H1; auto.
      apply IH. intro contra; discriminate. apply H1.
      apply IH. intro contra; discriminate. auto.
Qed.

Lemma gen_words_correct q l : forall w,
  In w l -> ixtransition w = q -> In w (gen_words q l).
Proof.
  intros w H H0.
  induction l as [|w' l' IH]; inversion H; simpl.
  - destruct (A_decidable (ixtransition w') q) eqn:H2.
    + left; auto.
    + rewrite <- H1 in H0; contradiction.
  - destruct (A_decidable (ixtransition w') q). right; apply IH; auto.
    apply IH; auto.
Qed.

Definition all_gen_words_le q n := gen_words q (all_words_le n).

Lemma all_gen_words_le_correct q n : forall w,
  q <> (sink) -> ixtransition w = q -> (length w <= n)%nat ->
  In w (all_gen_words_le q n).
Proof.
  unfold all_gen_words_le;
  intros w H H0 H1;
  apply gen_words_correct.
  apply all_words_le_correct;
  rewrite <- H0 in H.
  1-3: auto.
Qed.

End QSUtils.
