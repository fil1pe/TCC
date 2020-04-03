Require Import Coq.Lists.List Omega Psatz Coq.Bool.Bool.
Import ListNotations.
Require Import DFA QS.
Local Open Scope Z_scope.

Section QSUpperBound.

Variables (A : Type) (B : Type) (qs : @qs_dfa A B).
Definition g := g qs.

Definition xtransition := xtransition A B g.
Definition ixtransition := ixtransition A B g.
Definition is_tangible := is_tangible A B g.
Definition is_generated := is_generated A B g.
Definition count_buffer := count_buffer A B qs.

Definition n_upper_bounded := forall w, is_generated w -> n0 qs + count_buffer w <= n qs.

Lemma buffer_count_leq_f : forall f,
    ( f (q0 g) >= (n0 qs) /\ forall q, In q (Q g) -> is_tangible q -> forall e, In e (E g) ->
        f (delta g q e) >= f q + count_event qs e )
    -> forall w, is_generated w -> n0 qs + count_buffer w <= f (ixtransition w).
  Proof.
    intros f [H H0] w H10;
    induction w as [|e w' IH] using @rev_ind.
    - unfold ixtransition, DFA.ixtransition; simpl; omega.
    - pose H10 as H1; apply prefix_closed in H1; fold is_generated in H1; pose H1 as H2;
        apply IH in H2.
      unfold ixtransition, count_buffer; rewrite ixtransition_distr, count_buffer_distr';
        fold ixtransition xtransition count_buffer.
      unfold is_generated, DFA.is_generated in H1; fold ixtransition in H1;
        remember (ixtransition w') as q eqn:H3.
      rewrite H3; simpl; rewrite <- H3.
      remember (delta g q e) as q' eqn:H4.
      cut (f q' >= f q + count_event qs e).
      omega.
      rewrite H4.
      assert (H5: delta g q e <> sink g).
        unfold is_generated, DFA.is_generated in H10; rewrite ixtransition_distr in H10;
        simpl in H10; fold ixtransition in H10; rewrite <- H3 in H10; auto.
      apply (delta_correct g) in H5.
      apply H0.
      2: split; auto; eexists; fold ixtransition; symmetry; apply H3.
      1-2: intuition.
  Qed.

Theorem count_word_pow: forall w n,
  count_buffer (word_pow B w n) = (Z.of_nat n) * (count_buffer w).
Proof.
  intros w n.
  induction n as [|n IH]. auto.
  replace (word_pow B w (S n)) with (w ++ word_pow B w n).
  unfold count_buffer in *; rewrite count_buffer_distr, IH, Nat2Z.inj_succ, <- Zmult_succ_l_reverse;
  omega.
  auto.
Qed.

Lemma pumping_buffer1 q : forall w,
  n_upper_bounded -> ixtransition w = q -> q <> (sink g) ->
  (length w >= length (Q g))%nat ->
  exists w', ixtransition w' = q /\ (length w' < length w)%nat /\
  count_buffer w' >= count_buffer w.
Proof.
  intros w H H0 H1 H2;
  assert (H10: exists m, Z.of_nat m >= n qs - n0 qs - count_buffer w + 1). {
    assert (H3: 0 <= (n qs - n0 qs - count_buffer w + 1)).
      unfold n_upper_bounded, is_generated, DFA.is_generated in H;
      fold ixtransition in H; rewrite <- H0 in H1; apply H in H1; omega.
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
    + rewrite H2. unfold count_buffer in *.
      rewrite count_buffer_distr, count_buffer_distr, count_buffer_distr.
      fold count_buffer in *.
      omega.
  - assert (contra: n0 qs + count_buffer (w1 ++ word_pow B w2 (S m) ++ w3) > (n qs)). {
      unfold count_buffer; rewrite count_buffer_distr, count_buffer_distr; fold count_buffer.
      rewrite count_word_pow.
      replace (count_buffer w1 + (Z.of_nat (S m) * count_buffer w2 + count_buffer w3)) with
      (count_buffer w + Z.of_nat m * count_buffer w2).
      2: rewrite H2; unfold count_buffer; rewrite count_buffer_distr, count_buffer_distr; fold count_buffer;
      rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.mul_add_distr_r; omega.
      nia.
    }
    assert (contra0: is_generated (w1 ++ word_pow B w2 (S m) ++ w3)).
      unfold is_generated, DFA.is_generated; fold ixtransition; rewrite H4, H0;
      auto.
    apply H in contra0. omega.
Qed.

Lemma pumping_buffer q : forall w,
  n_upper_bounded -> ixtransition w = q -> q <> (sink g) ->
  (length w >= length (Q g))%nat ->
  exists w', ixtransition w' = q /\ (length w' < length (Q g))%nat /\
  count_buffer w' >= count_buffer w.
Proof.
  intro w.
  revert q.
  induction w as [|e w' IH] using @rev_ind; intros q H H0 H1 H2.
  - assert (length (Q g) > 0)%nat. {
      pose proof (q0_correct g). destruct (Q g).
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
         unfold count_buffer; rewrite count_buffer_distr, count_buffer_distr;
           fold count_buffer; omega.
      -- intro contra. rewrite contra in H0; unfold xtransition in H0;
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

Fixpoint gen_words q (l:list (list B)) :=
  match l with
  | w::l' => if Q_decidable g (ixtransition w) q then w::gen_words q l' else gen_words q l'
  | nil => nil
  end.

Lemma gen_words_correct1 q l : forall w,
  l <> nil -> In w (gen_words q l) -> ixtransition w = q.
Proof.
  intros w H H0.
  induction l as [|w' l' IH].
  - contradiction.
  - destruct l' as [|w'' l'].
    + simpl in H0; destruct (Q_decidable g (ixtransition w') q).
      inversion H0. rewrite <- H1; auto. inversion H1. inversion H0.
    + simpl in *. destruct (Q_decidable g (ixtransition w') q).
      inversion H0. rewrite <- H1; auto.
      apply IH. intro contra; discriminate. apply H1.
      apply IH. intro contra; discriminate. auto.
Qed.

Lemma gen_words_correct q l : forall w,
  In w l -> ixtransition w = q -> In w (gen_words q l).
Proof.
  intros w H H0.
  induction l as [|w' l' IH]; inversion H; simpl.
  - destruct (Q_decidable g (ixtransition w') q) eqn:H2.
    + left; auto.
    + rewrite <- H1 in H0; contradiction.
  - destruct (Q_decidable g (ixtransition w') q). right; apply IH; auto.
    apply IH; auto.
Qed.

Definition all_gen_words_le q n := gen_words q (all_words_le A B g n).

Lemma all_gen_words_le_correct q n : forall w,
  q <> (sink g) -> ixtransition w = q -> (length w <= n)%nat ->
  In w (all_gen_words_le q n).
Proof.
  unfold all_gen_words_le.
  intros w H H0 H1.
  apply gen_words_correct.
  apply all_words_le_correct.
  unfold DFA.is_generated; fold ixtransition; rewrite <- H0 in H.
  1-3: auto.
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
  - destruct (Z_ge_dec (count_buffer w') (count_buffer (max_list l'))).
    + destruct l'; rewrite H0; intuition.
    + apply Znot_ge_lt in n; rewrite H0 in *; destruct l'; omega.
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
  - destruct (Z_ge_dec (count_buffer [e']) (count_buffer (max_in_list l'))).
    + destruct l'; rewrite H0; intuition.
    + apply Znot_ge_lt in n; rewrite H0 in *; destruct l'; simpl in *; omega.
  - apply IH in H0; destruct (Z_ge_dec (count_buffer [e']) (count_buffer (max_in_list l')));
    destruct l'; simpl in *; try omega.
    inversion H. rewrite H1; omega. destruct H1.
Qed.

Definition max_count_event := count_buffer (max_in_list (E g)).

Lemma max_count_event_correct : forall e,
  In e (E g) -> count_event qs e <= count_buffer (max_in_list (E g)).
Proof.
  intros e H.
  replace (count_event qs e) with (count_buffer [e]).
  apply max_in_list_correct; auto.
  simpl; omega.
Qed.

Definition max_gen_words q := max_list (all_gen_words_le q (length (Q g) - 1)).

Lemma max_gen_words_correct q :
  n_upper_bounded -> is_tangible q ->
  max_word q (max_gen_words q).
Proof.
  intros H H0.
  apply max_word_def.
  split; unfold max_gen_words.
  - intros w H1;
    destruct H0 as [H0 H2];
    destruct (le_gt_dec (length w) (length (Q g) - 1)).
    + apply max_list_correct, all_gen_words_le_correct; auto.
    + assert (H3: (length w >= length (Q g))%nat). omega.
      eapply pumping_buffer with (q:=q) in H3.
      2-4: auto.
      destruct H3 as [w' [H3 [H4 H5]]].
      assert (count_buffer w' <= count_buffer (max_list (all_gen_words_le q (length (Q g) - 1)))).
        apply max_list_correct, all_gen_words_le_correct; auto; omega.
      omega.
  - apply max_list_correct1.
    + apply pumping in H0; destruct H0 as [w [H0 [H1 H2]]]; fold ixtransition in H0.
      eapply all_gen_words_le_correct with (n:=(length (Q g) - 1)%nat) in H2.
      2: apply H0.
      2: omega.
      intro contra; rewrite contra in H2; destruct H2.
    + intros w H1; unfold all_gen_words_le in H1;
      eapply gen_words_correct1. 2: apply H1.
      clear. induction (length (Q g) - 1)%nat as [|n1 IH].
      * simpl; intro contra; discriminate.
      * simpl. remember (match n1 with | 0%nat => all_words1 B (E g)
                          | S _ => all_words' B (all_words A B g n1) (E g) end) as l.
        clear Heql. destruct l as [|a l'].
        apply IH.
        simpl; intros contra; discriminate.
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

Lemma q0_cycle: forall w n,
  ixtransition w = (q0 g) -> ixtransition (word_pow B w n) = (q0 g).
Proof.
  intros w n H.
  induction n as [|n IH]. auto.
  unfold ixtransition in *;
  simpl;
  rewrite ixtransition_distr, H;
  auto.
Qed.

Lemma max_word_q0 : forall w,
  n_upper_bounded ->
  max_word (q0 g) w ->
  count_buffer w = 0.
Proof.
  intros w H H0.
  destruct H0 as [H0 H3];
  destruct (count_buffer w) eqn:H1.
  - auto.
  - pose proof (Zgt_pos_0 p) as H2; rewrite <- H1 in H2, H3;
    clear H1; pose H0 as H1; apply q0_cycle with (n:=2%nat) in H1;
    apply H3 in H1. rewrite count_word_pow in H1.
    assert (H4: Z.of_nat 2 * count_buffer w <= 1 * count_buffer w). omega.
    assert (Z.of_nat 2 > 1). replace 1 with (Z.of_nat 1). 2: constructor. apply inj_gt; omega.
    eapply Zmult_gt_compat_r in H5. 2: apply H2. omega.
  - pose proof (Zlt_neg_0 p) as H2; rewrite <- H1 in H2;
    clear H0; assert (H0: ixtransition [] = q0 g). auto.
    apply H3 in H0; simpl in H0.
    omega.
Qed.

Lemma max_word_transition : forall q e qe w we,
  delta g q e = qe -> qe <> sink g ->
  max_word q w -> max_word qe we ->
  count_buffer we >= count_buffer w + count_event qs e.
Proof.
  intros q e qe w we H H0 H1 H2.
  assert (count_buffer (w ++ [e]) = count_buffer w + count_event qs e). apply count_buffer_distr'.
  assert (count_buffer we >= count_buffer (w ++ [e])).
  destruct H2 as [H2 H4]; destruct H1 as [H1 H5];
  unfold ixtransition in *; apply Z.ge_le_iff; apply H4;
  rewrite ixtransition_distr; rewrite H1; simpl; auto.
  omega.
Qed.

Theorem iff_exists_function__upper_bounded :
  ( exists f, f (q0 g) >= (n0 qs) /\ forall q, In q (Q g) -> is_tangible q -> f q <= n qs /\
    forall e, In e (E g) -> f (delta g q e) >= f q + count_event qs e )
  <-> n_upper_bounded.
Proof.
  split.

  - unfold n_upper_bounded; intros [ f [H H0] ] w H1.
    cut (n0 qs + count_buffer w <= f (ixtransition w)).
    cut (f (ixtransition w) <= n qs).
    omega.
    apply H0.
    apply ixtransition_in_Q; fold ixtransition; apply H1.
    split; try intuition; eexists; fold ixtransition; reflexivity.
    apply buffer_count_leq_f; try split; try (apply H0); intuition.

  - intro H.
    pose H as H0; apply exists_max_word_function in H0; destruct H0 as [f H0];
      unfold tangible_max_word in H0.
    exists (fun q => if Q_decidable g q (sink g) then (n qs)+(max_count_event) else (n0 qs) + count_buffer (f q));
    split.
    + destruct (Q_decidable g (q0 g) (sink g)) as [H2|H2].
      destruct (sink_correct g) as [_ contra]; symmetry in H2; contradiction.
      assert (H1: is_tangible (q0 g)). split. auto. exists []; unfold DFA.ixtransition; auto.
      apply H0 in H1; apply max_word_q0 in H1; auto; omega.
    + intros q H1 H2; pose H2 as H3; apply H0 in H3; destruct (Q_decidable g q (sink g)).
      destruct H2 as [H2 [w H4]]; contradiction.
      clear n.
      assert (H4: n0 qs + count_buffer (f q) <= n qs). {
        destruct H3 as [H3 _]; apply H; unfold is_generated, DFA.is_generated;
        fold ixtransition; destruct H2 as [H2 _]; rewrite <- H3 in H2; auto.
      }
      split.
      * auto.
      * intros e H5; destruct (Q_decidable g (delta g q e) (sink g)).
        assert (count_event qs e <= max_count_event).
          apply max_count_event_correct; auto.
        omega.
        assert (H6: is_tangible (delta g q e)).
          split; auto; destruct H2 as [H2 [w H6]]; exists (w ++ [e]); rewrite ixtransition_distr;
          simpl; rewrite H6; auto.
        assert (count_buffer (f (delta g q e)) >= count_buffer (f q) + count_event qs e).
          eapply max_word_transition. 2: apply n. reflexivity. apply H0; auto. apply H0; auto.
        omega.
Qed.

End QSUpperBound.