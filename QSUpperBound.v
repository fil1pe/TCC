Require Import Coq.Lists.List Omega Psatz Coq.Bool.Bool.
Import ListNotations.
Require Import DFA QS.
Local Open Scope Z_scope.

Module QSUpperBound (dfa : DFA).

Include QSUtils dfa.

Definition n_upper_bounded := forall w, is_generated w -> n0 + count_buffer w <= n.

Lemma buffer_count_leq_f : forall f,
    ( f (q0) >= (n0) /\ forall q, In q (Q) -> is_tangible q -> forall e, In e (E) ->
        f (delta q e) >= f q + count_event e )
    -> forall w, is_generated w -> n0 + count_buffer w <= f (ixtransition w).
Proof.
  intros f [H H0] w H10;
  induction w as [|e w' IH] using @rev_ind.
  - unfold ixtransition; simpl; omega.
  - pose H10 as H1; apply prefix_closed in H1; fold is_generated in H1; pose H1 as H2;
      apply IH in H2.
    unfold ixtransition, count_buffer; rewrite ixtransition_distr, count_buffer_distr';
      fold ixtransition xtransition count_buffer.
    unfold is_generated in H1; remember (ixtransition w') as q eqn:H3.
    rewrite H3; simpl; rewrite <- H3.
    remember (delta q e) as q' eqn:H4.
    cut (f q' >= f q + count_event e).
    omega.
    rewrite H4.
    assert (H5: delta q e <> sink).
      unfold is_generated in H10; rewrite ixtransition_distr in H10;
      simpl in H10; rewrite <- H3 in H10; auto.
    apply (delta_correct) in H5.
    apply H0.
    2: split; auto; eexists; fold ixtransition; symmetry; apply H3.
    1-2: intuition.
Qed.

Lemma pumping_buffer1 q : forall w,
  n_upper_bounded -> ixtransition w = q -> q <> (sink) ->
  (length w >= length (Q))%nat ->
  exists w', ixtransition w' = q /\ (length w' < length w)%nat /\
  count_buffer w' >= count_buffer w.
Proof.
  intros w H H0 H1 H2;
  assert (H10: exists m, Z.of_nat m >= n - n0 - count_buffer w + 1). {
    assert (H3: 0 <= (n - n0 - count_buffer w + 1)).
      unfold n_upper_bounded, is_generated in H; rewrite <- H0 in H1; apply H in H1; omega.
    apply Z_of_nat_complete in H3; destruct H3 as [n1 H3];
    exists n1; omega.
  }
  destruct H10 as [m H10].
  apply pumping_pow with (n:=S m) in H2;
  destruct H2 as [w1 [w2 [w3 [H2 [H3 [H4 H6]]]]]];
  fold ixtransition in H4;
  destruct (Z_le_gt_dec (count_buffer w2) 0) as [H5|H5].
  - exists (w1++w3); repeat split.
    + rewrite <- H0; unfold ixtransition; auto.
    + rewrite H2, app_length, app_length, app_length.
      assert (length w2 > 0)%nat.
        destruct w2; try contradiction; simpl; omega.
      omega.
    + rewrite H2.
      rewrite count_buffer_distr, count_buffer_distr, count_buffer_distr.
      omega.
  - assert (contra: n0 + count_buffer (w1 ++ word_pow w2 (S m) ++ w3) > (n)). {
      rewrite count_buffer_distr, count_buffer_distr;
      rewrite count_word_pow.
      replace (count_buffer w1 + (Z.of_nat (S m) * count_buffer w2 + count_buffer w3)) with
      (count_buffer w + Z.of_nat m * count_buffer w2).
      2: rewrite H2; rewrite count_buffer_distr, count_buffer_distr;
      rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.mul_add_distr_r; omega.
      nia.
    }
    assert (contra0: is_generated (w1 ++ word_pow w2 (S m) ++ w3)).
      unfold is_generated; fold ixtransition; rewrite H4, H0;
      auto.
    apply H in contra0. omega.
Qed.

Lemma pumping_buffer q : forall w,
  n_upper_bounded -> ixtransition w = q -> q <> (sink) ->
  (length w >= length (Q))%nat ->
  exists w', ixtransition w' = q /\ (length w' < length (Q))%nat /\
  count_buffer w' >= count_buffer w.
Proof.
  intro w.
  revert q.
  induction w as [|e w' IH] using @rev_ind; intros q H H0 H1 H2.
  - assert (length (Q) > 0)%nat. {
      pose proof (q0_correct). destruct (Q).
      destruct H3.
      simpl; omega.
    }
    simpl in H2; omega.
  - inversion H2.
    + eapply pumping_buffer1 in H.
      2: apply H0.
      2: auto.
      2: omega.
      rewrite <- H4 in H.
      apply H.
    + unfold ixtransition in H0; rewrite ixtransition_distr in H0;
        fold ixtransition xtransition in H0.
      pose H as H5.
      eapply IH in H5. clear IH.
      2: reflexivity.
      destruct H5 as [w0 [H6 [H7 H8]]].
      inversion H7.
      -- apply pumping_buffer1 with (q:=q) (w:=w0 ++ [e]) in H.
         destruct H as [w1 [H10 [H11 H12]]].
         exists w1. repeat split.
         auto.
         rewrite app_length in H11; simpl in H11; omega.
         assert (count_buffer (w0 ++ [e]) >= count_buffer (w' ++ [e])).
           unfold count_buffer; rewrite count_buffer_distr, count_buffer_distr;
           fold count_buffer; omega.
         omega.
         unfold ixtransition; rewrite ixtransition_distr; fold ixtransition xtransition;
         rewrite H6; auto.
         auto.
         rewrite app_length; simpl; omega.
      -- exists (w0 ++ [e]); repeat split.
         unfold ixtransition; rewrite ixtransition_distr; fold ixtransition xtransition;
         rewrite H6; auto.
         rewrite app_length; simpl; omega.
         rewrite count_buffer_distr, count_buffer_distr; omega.
      -- intro contra. rewrite contra in H0;
         rewrite xtransition_sink in H0; symmetry in H0; contradiction.
      -- rewrite app_length in H3; simpl in H3; omega.
Qed.

Definition max_word q w :=
  ixtransition w = q /\ forall w', ixtransition w' = q -> count_buffer w' <= count_buffer w.

Lemma max_word_def q w :
  (forall w', ixtransition w' = q -> count_buffer w' <= count_buffer w)
  /\ ixtransition w = q <-> max_word q w.
Proof.
  split.
  - intros [H H0]; unfold max_word; intuition.
  - unfold max_word; intros [H H0]; intuition.
Qed.

Definition max w1 w2 :=
  if Z_ge_dec (count_buffer w1) (count_buffer w2) then w1 else w2.

Fixpoint max_list (l:list (list B)) :=
  match l with
  | w::nil => w
  | w::l' => max w (max_list l')
  | nil => nil
  end.

Lemma max_list_correct1 l : forall q,
  l <> nil ->
  (forall w, In w l -> ixtransition w = q) ->
  ixtransition (max_list l) = q.
Proof.
  intros q H H0.
  induction l as [|w' l' IH].
  - contradiction.
  - destruct l' as [|w'' l'].
    + apply H0; intuition.
    + assert (H1: ixtransition (max_list (w'' :: l')) = q). {
        apply IH.
        intro contra; discriminate.
        intros w0 H1. apply H0. right; auto.
      }
      clear IH.
      simpl. simpl in H1. unfold max.
      destruct (Z_ge_dec (count_buffer w')
      (count_buffer match l' with | [] => w'' | _ :: _ =>
       if Z_ge_dec (count_buffer w'') (count_buffer (max_list l')) then w''
       else max_list l' end)).
      * apply H0; left; auto.
      * apply H1.
Qed.

Lemma max_list_correct l : forall w,
  In w l -> count_buffer w <= count_buffer (max_list l).
Proof.
  intros w H.
  induction l as [|w' l' IH]; inversion H; simpl; unfold max.
  - destruct (Z_ge_dec (count_buffer w') (count_buffer (max_list l'))) as [H1|H1].
    + destruct l'; rewrite H0; intuition.
    + apply Znot_ge_lt in H1; rewrite H0 in *; destruct l'; omega.
  - apply IH in H0; destruct (Z_ge_dec (count_buffer w') (count_buffer (max_list l')));
    destruct l'; try omega.
    inversion H. rewrite H1; omega. destruct H1.
Qed.

Fixpoint max_in_list l :=
  match l with
  | e::nil => [e]
  | e::l' => max [e] (max_in_list l')
  | nil => nil
  end.

Lemma max_in_list_correct l : forall e,
  In e l -> count_buffer [e] <= count_buffer (max_in_list l).
Proof.
  intros e H.
  induction l as [|e' l' IH]; inversion H; simpl; unfold max.
  - destruct (Z_ge_dec (count_buffer [e']) (count_buffer (max_in_list l'))) as [H1|H1].
    + destruct l'; rewrite H0; intuition.
    + apply Znot_ge_lt in H1; rewrite H0 in *; destruct l'; simpl in *; omega.
  - apply IH in H0; destruct (Z_ge_dec (count_buffer [e']) (count_buffer (max_in_list l')));
    destruct l'; simpl in *; try omega.
    inversion H. rewrite H1; omega. destruct H1.
Qed.

Definition max_count_event := count_buffer (max_in_list (E)).

Lemma max_count_event_correct : forall e,
  In e (E) -> count_event e <= count_buffer (max_in_list (E)).
Proof.
  intros e H.
  replace (count_event e) with (count_buffer [e]).
  apply max_in_list_correct; auto.
  simpl; omega.
Qed.

Definition max_gen_words q := max_list (all_gen_words_le q (length (Q) - 1)).

Lemma max_gen_words_correct q :
  n_upper_bounded -> is_tangible q ->
  max_word q (max_gen_words q).
Proof.
  intros H H0.
  apply max_word_def.
  split; unfold max_gen_words.
  - intros w H1;
    destruct H0 as [H0 H2];
    destruct (le_gt_dec (length w) (length (Q) - 1)).
    + apply max_list_correct, all_gen_words_le_correct; auto.
    + assert (H3: (length w >= length (Q))%nat). omega.
      eapply pumping_buffer with (q:=q) in H3.
      2-4: auto.
      destruct H3 as [w' [H3 [H4 H5]]].
      assert (count_buffer w' <= count_buffer (max_list (all_gen_words_le q (length (Q) - 1)))).
        apply max_list_correct, all_gen_words_le_correct; auto; omega.
      omega.
  - apply max_list_correct1.
    + apply pumping in H0; destruct H0 as [w [H0 [H1 H2]]]; fold ixtransition in H0.
      eapply all_gen_words_le_correct with (n:=(length (Q) - 1)%nat) in H2.
      2: apply H0.
      2: omega.
      intro contra; rewrite contra in H2; destruct H2.
    + intros w H1; unfold all_gen_words_le in H1;
      eapply gen_words_correct1. 2: apply H1.
      clear. induction (length (Q) - 1)%nat as [|n1 IH].
      * simpl; intro contra; discriminate.
      * simpl; destruct (all_words (S n1)) as [|a l]; auto.
        simpl; intro contra; discriminate.
Qed.

Definition tangible_max_word q w := is_tangible q -> max_word q w.

Lemma exists_max_word_function : n_upper_bounded ->
    exists f, forall q, is_tangible q -> max_word q (f q).
Proof.
  intro H.
  exists (max_gen_words);
  intro q;
  intro H0;
  apply max_gen_words_correct; auto.
Qed.

Lemma max_word_q0 : forall w,
  n_upper_bounded ->
  max_word (q0) w ->
  count_buffer w = 0.
Proof.
  intros w H H0.
  destruct H0 as [H0 H3];
  destruct (count_buffer w) eqn:H1.
  - auto.
  - pose proof (Zgt_pos_0 p) as H2; rewrite <- H1 in H2, H3;
    clear H1; pose H0 as H1; apply q0_cycle with (n:=2%nat) in H1;
    apply H3 in H1. unfold count_buffer in H1; rewrite count_word_pow in H1; fold count_buffer in H1.
    nia.
  - pose proof (Zlt_neg_0 p) as H2; rewrite <- H1 in H2;
    clear H0; assert (H0: ixtransition [] = q0). auto.
    apply H3 in H0; simpl in H0.
    omega.
Qed.

Lemma max_word_transition : forall q e qe w we,
  delta q e = qe -> qe <> sink ->
  max_word q w -> max_word qe we ->
  count_buffer we >= count_buffer w + count_event e.
Proof.
  intros q e qe w we H H0 H1 H2.
  assert (count_buffer (w ++ [e]) = count_buffer w + count_event e). apply count_buffer_distr'.
  assert (count_buffer we >= count_buffer (w ++ [e])).
  destruct H2 as [H2 H4]; destruct H1 as [H1 H5];
  unfold ixtransition in *; apply Z.ge_le_iff; apply H4;
  rewrite ixtransition_distr; unfold ixtransition; rewrite H1; simpl; auto.
  omega.
Qed.

Theorem iff_exists_function__upper_bounded :
  ( exists f, f (q0) >= (n0) /\ forall q, In q (Q) -> is_tangible q -> f q <= n /\
    forall e, In e (E) -> f (delta q e) >= f q + count_event e )
  <-> n_upper_bounded.
Proof.
  split.

  - unfold n_upper_bounded; intros [ f [H H0] ] w H1.
    cut (n0 + count_buffer w <= f (ixtransition w)).
    cut (f (ixtransition w) <= n).
    omega.
    apply H0.
    apply ixtransition_in_Q; fold ixtransition; apply H1.
    split; try intuition; eexists; fold ixtransition; reflexivity.
    apply buffer_count_leq_f; try split; try (apply H0); intuition.

  - intro H.
    pose H as H0; apply exists_max_word_function in H0; destruct H0 as [f H0];
      unfold tangible_max_word in H0.
    exists (fun q => if A_decidable q (sink) then (n)+(max_count_event) else (n0) + count_buffer (f q));
    split.
    + destruct (A_decidable (q0) (sink)) as [H2|H2].
      destruct (sink_correct) as [_ contra]; symmetry in H2; contradiction.
      assert (H1: is_tangible (q0)). split. auto. exists []; auto.
      apply H0 in H1; apply max_word_q0 in H1; auto; omega.
    + intros q H1 H2; pose H2 as H3; apply H0 in H3; destruct (A_decidable q (sink)).
      destruct H2 as [H2 [w H4]]; contradiction.
      assert (H4: n0 + count_buffer (f q) <= n). {
        destruct H3 as [H3 _]; apply H; unfold is_generated;
        fold ixtransition; destruct H2 as [H2 _]; rewrite <- H3 in H2; auto.
      }
      split.
      * auto.
      * intros e H5; destruct (A_decidable (delta q e) (sink)) as [H7|H7].
        assert (count_event e <= max_count_event).
          apply max_count_event_correct; auto.
        omega.
        assert (H6: is_tangible (delta q e)).
          split; auto; destruct H2 as [H2 [w H6]]; exists (w ++ [e]); rewrite ixtransition_distr;
          simpl; rewrite H6; auto.
        assert (count_buffer (f (delta q e)) >= count_buffer (f q) + count_event e).
          eapply max_word_transition. 2: apply H7. reflexivity. apply H0; auto. apply H0; auto.
        omega.
Qed.

End QSUpperBound.
