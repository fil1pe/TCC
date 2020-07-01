Require Import Coq.Lists.List Omega Coq.Bool.Bool.
Import ListNotations.
Require Import DFA.
Local Open Scope Z_scope.

(* Queueing Systems *)

Module Type QS (dfa : DFA).
  Include DFAUtils dfa.

  Parameters
    (count_event : dfa.B -> Z)
      (* a function that describes the number of items added to the buffer by some given event *)
    (init_items min_items max_items : Z)
      (* the specified countings for the initial, minimum and maximum itens inside the buffer *)
    (max_items_correct : max_items >= init_items)
    (min_items_correct : min_items <= init_items)
      (* min_items <= init_items <= max_items *)
    .
End QS.

Module QSUtils (dfa : DFA).
Include QS dfa.

(* a function that counts the number of buffered items based on the past events *)
Fixpoint count_buffer w :=
  match w with
  | e::w' => count_event e + count_buffer w'
  | nil => 0
  end.

(* count_buffer is pseudo-distributive, meaning that we can count the events in any order. *)
Lemma count_buffer_distr w1 w2 :
  count_buffer (w1 ++ w2) = count_buffer w1 + count_buffer w2.
Proof.
  induction w1 as [|e w1' IH];
  auto;
  simpl; rewrite IH; omega.
Qed.

(* for w1=w and w2=[e] *)
Lemma count_buffer_distr' w e :
  count_buffer (w ++ [e]) = count_buffer w + (count_event e).
Proof.
  rewrite count_buffer_distr; simpl; omega.
Qed.

(* the number of items added by w^n is equal to the number of items added by w multiplied by n. *)
Theorem count_word_pow: forall w n,
  count_buffer (word_pow w n) = (Z.of_nat n) * (count_buffer w).
Proof.
  intros w n;
  induction n as [|n IH]; auto;
  replace (word_pow w (S n)) with (w ++ word_pow w n); auto;
  rewrite count_buffer_distr, IH, Nat2Z.inj_succ, <- Zmult_succ_l_reverse;
  omega.
Qed.

(* a function that lists the sequences of events of a given list that transition into a given state *)
Fixpoint gen_words q (l:list (list B)) :=
  match l with
  | w::l' => if A_eq_dec (ixtransition w) q then w::gen_words q l' else gen_words q l'
  | nil => nil
  end.

(* Every sequence of events returned by gen_words must be correct. *)
Lemma gen_words_correct q l : forall w,
  In w (gen_words q l) -> ixtransition w = q.
Proof.
  intros w H0;
  induction l as [|w' l' IH].
  - contradiction.
  - destruct l' as [|w'' l'].
    + simpl in H0; destruct (A_eq_dec (ixtransition w') q).
      inversion H0 as [H|H].
      rewrite <- H; auto.
      destruct H.
      destruct H0.
    + simpl in *. destruct (A_eq_dec (ixtransition w') q) as [H|H].
      inversion H0 as [H1|H1].
      rewrite <- H1; auto.
      1,2: apply IH; auto.
Qed.

(* Every sequence of events in l that transitions into q is in gen_words q l. *)
Lemma gen_words_complete q l : forall w,
  In w l -> ixtransition w = q -> In w (gen_words q l).
Proof.
  intros w H H0.
  induction l as [|w' l' IH]; inversion H; simpl.
  - destruct (A_eq_dec (ixtransition w') q) eqn:H2.
    + left; auto.
    + rewrite <- H1 in H0; contradiction.
  - destruct (A_eq_dec (ixtransition w') q). right; apply IH; auto.
    apply IH; auto.
Qed.

(* a function that lists the sequences of events of a given list that transition into a given state
  and whose length is less or equal to a given number *)
Definition all_gen_words_le q n := gen_words q (all_words_le n).

(* Every generated sequence of events that transition into q and whose length is less or equal to n
  is in all_gen_words_le q n. *)
Lemma all_gen_words_le_generated q n : forall w,
  q <> sink -> ixtransition w = q -> (length w <= n)%nat ->
  In w (all_gen_words_le q n).
Proof.
  unfold all_gen_words_le;
  intros w H H0 H1;
  apply gen_words_complete.
  apply all_words_le_generated;
  rewrite <- H0 in H.
  1-3: auto.
Qed.

End QSUtils.
