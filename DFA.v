Require Import Coq.Lists.List Coq.Bool.Bool Omega.
Import ListNotations.

Record dfa {A B} : Type := {
  Q : list A;
  E : list B;
  delta : A -> B -> A;
  sink : A;
  q0 : A;
  q0_correct : In q0 Q;
  sink_correct : In sink Q;
  delta_correct : forall q e, delta q e <> sink -> (In e E /\ In q Q /\ q <> sink /\ In (delta q e) Q);
  Q_decidable : forall x y : A, {x = y} + {x <> y}
}.

Section DFA.

Variables (A : Type) (B : Type) (g : @dfa A B).

Lemma Q_not_nil : (Q g) <> nil.
Proof.
  pose proof (q0_correct g) as H;
  intro contra; rewrite contra in H;
  pose proof in_nil; contradiction.
Qed.

Fixpoint xtransition q w :=
  match w with
  | e::w' => xtransition (delta g q e) w'
  | nil => q
  end.

Theorem xtransition_distr w1 w2 : forall q,
  xtransition q (w1 ++ w2) = xtransition (xtransition q w1) w2.
Proof.
  induction w1 as [|e w1' IH]; try (intro q; simpl; rewrite IH); trivial.
Qed.

Lemma xtransition_sink w :
  xtransition (sink g) w = sink g.
Proof.
  induction w as [|e w IH].
  - intuition.
  - simpl.
    destruct (Q_decidable g (delta g (sink g) e) (sink g)) as [H|H].
    + rewrite H; intuition.
    + apply delta_correct in H; destruct H as [H [H0 [H1 H2]]]; contradiction.
Qed.

Definition ixtransition w := xtransition (q0 g) w.

Theorem ixtransition_distr w1 w2 :
  ixtransition (w1 ++ w2) = xtransition (ixtransition w1) w2.
Proof. apply xtransition_distr. Qed.

Lemma ixtransition_in_Q w :
  ixtransition w <> sink g -> In (ixtransition w) (Q g).
Proof.
  intro H.
  pose proof (q0_correct g).
  unfold ixtransition in *.
  generalize dependent (q0 g).
  induction w as [|e w' IH]; intros q H0.
  - auto.
  - intro H1. simpl in *.
    destruct (Q_decidable g (delta g q e) (sink g)).
    + rewrite e0, xtransition_sink; apply (sink_correct g).
    + apply IH. auto. apply (delta_correct g) in n; intuition.
Qed.

Definition is_generated w := ixtransition w <> sink g.

Theorem prefix_closed : forall w1 w2,
  is_generated (w1 ++ w2) -> is_generated w1.
Proof.
  unfold is_generated;
  intros w1 w2 H contra;
  rewrite ixtransition_distr, contra, xtransition_sink in H;
  contradiction.
Qed.

Definition is_tangible q := q <> (sink g) /\ exists w, ixtransition w = q.

Fixpoint config' q w :=
  match w with
  | e::w' => (delta g q e)::config' (delta g q e) w'
  | nil => []
  end.
Definition config w := (q0 g)::config' (q0 g) w.

Lemma config'_length w : forall q,
  length (config' q w) = length w.
Proof.
  induction w as [|e w' IH];
  try (intro q; simpl; rewrite IH); trivial.
Qed.

Lemma config_length w :
  length (config w) = S (length w).
Proof.
  simpl; rewrite config'_length; trivial.
Qed.

Inductive qrepeats : list A -> Prop :=
  | qrpt_constr l a : In a l \/ qrepeats l -> qrepeats (a::l).

Lemma config_pumping1 : forall {C} a (w:list C),
  In a w -> exists w1 w2, w = w1 ++ [a] ++ w2.
Proof.
  intros C a w H.
  induction w as [|a0 w' IH]; destruct H.
  - clear IH; exists nil, w'; rewrite H; auto.
  - apply IH in H; clear IH; destruct H as [w1 [w2 H]];
    exists (a0::w1), w2; rewrite H; auto.
Qed.

Lemma config_pumping2 w :
  qrepeats w ->
  exists q c1 c2 c3, w = c1 ++ [q] ++ c2 ++ [q] ++ c3.
Proof.
  intro H.
  induction w as [|e w IH].
  - inversion H.
  - inversion H; destruct H1.
    + apply config_pumping1 in H1; destruct H1 as [w1 [w2 H1]];
      exists e, nil, w1, w2; rewrite H1; auto.
    + apply IH in H1; destruct H1 as [q [c1 [c2 [c3 H1]]]];
      exists q, (e::c1), c2, c3; rewrite H1; auto.
Qed.

Lemma pigeonhole1 w : forall q,
  In q (config w) -> In q (Q g).
Proof.
  unfold config; intros q H; destruct H.
  - rewrite <- H; apply q0_correct.
  - generalize dependent (q0 g);
    induction w as [|e w IH]; intros a H; destruct H.
    + destruct (Q_decidable g q (sink g)) as [H0|H0].
      * rewrite H0; apply (sink_correct g).
      * rewrite <- H in H0; apply (delta_correct g) in H0;
        rewrite <- H; intuition.
    + eapply IH; apply H.
Qed.

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l -> exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l H;
  induction l as [|a l IH]; destruct H.
  - exists nil, l; rewrite H; intuition.
  - apply IH in H; destruct H as [l1 [l2 H]];
    exists (a::l1), l2; rewrite H; intuition.
Qed.

Lemma pigeonhole w : 
  length (config w) > length (Q g) ->
  qrepeats (config w).
Proof.
  intro H; pose proof pigeonhole1 as H0; specialize (H0 w).
  generalize dependent (config w).
  generalize dependent (Q g).
  clear w.
  intros l2 l1; revert l2; induction l1 as [|x1 l1 IH]; intros l2 H H0.
  - simpl in H; omega.
  - destruct l2 as [|x2 l2].
    specialize (H0 x1); assert (H1: In x1 (x1 :: l1)). left; trivial.
    apply H0 in H1; destruct H1.

    destruct (in_dec (Q_decidable g) x1 l1) as [H1|H1].
    constructor; intuition.
    assert (H2: In x1 (x2::l2)).
      apply H0; left; trivial.
    apply in_split in H2. destruct H2 as [l2' [l2'' H2]].
    assert (H3: length l2 = length (l2' ++ l2'')). {
      rewrite app_length.
      assert (H4: length ([x2] ++ l2) = length (l2' ++ [x1] ++ l2'')).
        simpl ([x2] ++ l2); rewrite H2; intuition.
      rewrite app_length, app_length, app_length in H4;
      simpl in H4; omega.
    }
    assert (forall x, In x l1 -> In x (l2'++l2'')). {
      clear IH H H3; intros x H; rewrite H2 in H0;
      assert (H3: In x (l2' ++ x1 :: l2'')). apply H0; right; auto.
      clear H0 H2.
      induction l2' as [|x2' l2' IH].
      - simpl; simpl in H3; destruct H3 as [H3|H3].
        rewrite <- H3 in H; contradiction.
        auto.
      - destruct H3 as [H3|H3].
        left; auto.
        right; apply IH; trivial.
    }
    constructor; right; eapply IH.
    2: apply H4.
    simpl in H; omega.
Qed.

Lemma config_pumping3 w :
  length (config w) > length (Q g) ->
  exists q c1 c2 c3, config w = c1 ++ [q] ++ c2 ++ [q] ++ c3.
Proof.
  intro H; apply config_pumping2, pigeonhole; auto.
Qed.

Lemma last_pumping l : forall t1 t2 : A,
  l <> nil ->
  last l t1 = last l t2.
Proof.
  intros t1 t2 H.
  induction l as [|a l IH].
  - contradiction.
  - destruct l.
    + auto.
    + simpl in *; apply IH; intro contra; discriminate.
Qed.

Lemma config_pumping2_0 w : forall q0 a b,
  a <> nil -> q0::config' q0 w = a ++ b ->
  exists w1 w2,
    w = w1 ++ w2 /\
    xtransition q0 w1 = last a q0 /\
    xtransition (last a q0) w2 = last b (last a q0).
Proof.
  induction w as [|e w IH]; intros q0 a b H H0;
  simpl in H0.
  - assert (H1: b = []). {
      destruct a, b; try contradiction; auto.
      simpl in H0. assert (contra: length ([q0]) = length (a :: a0 ++ a1 :: b)).
                     rewrite H0; auto.
      simpl in contra; rewrite app_length in contra; simpl in contra; omega.
    }
    exists nil, nil; repeat split.
    + rewrite H1 in H0; rewrite app_nil_r in H0;
      rewrite <- H0; auto.
    + rewrite H1; simpl; auto.
  - destruct a as [|a0 a]. contradiction.
    assert (H2: delta g q0 e :: config' (delta g q0 e) w =
      a ++ b).
      simpl in H0; inversion H0; auto.
    destruct a as [|a1 a].
    + simpl in *. destruct b as [|b0 b]. discriminate.
      assert (H3: config' (delta g q0 e) w = b).
        inversion H2; auto.
      destruct b as [|b1 b].
      * simpl in H3. destruct w as [|e' w].
        2: simpl in H3; discriminate.
        clear H2 H3. simpl in H0.
        exists nil, [e]; repeat split.
        -- inversion H0; auto.
        -- simpl; inversion H0; auto.
      * exists nil. replace (b0 :: b1 :: b) with ([b0;b1] ++ b) in H2.
        apply IH in H2.
        destruct H2 as [w1 [w2 [H2 [H5 H4]]]].
        exists (e::w1 ++ w2); repeat split.
        -- simpl; rewrite H2; auto.
        -- inversion H0; auto.
        -- simpl (xtransition a0 (e :: w1 ++ w2));
           rewrite xtransition_distr; inversion H0;
           rewrite <- H6, H5, H4, H3; simpl;
           clear; induction b as [|b0 b IH]; try (destruct b); auto.
        -- intro contra; discriminate.
        -- auto.
    + apply IH in H2;
      destruct H2 as [w1 [w2 [H2 [H5 H4]]]].
      2: intro contra; discriminate.
      assert (aux: last (a1 :: a) (delta g q0 e) = last (a0 :: a1 :: a) q0).
        simpl; clear; induction a as [|a0 a IH]; try (destruct a); auto.
      exists (e::w1), w2; repeat split.
      * simpl; rewrite H2; auto.
      * simpl (xtransition q0 (e :: w1)); rewrite H5; apply aux.
      * rewrite <- aux; auto.
Qed.

Lemma config_pumping2_1 w : forall q0 a b c,
  a <> nil -> b <> nil -> q0::config' q0 w = a ++ b ++ c ->
  exists w1 w2 w3,
    w = w1 ++ w2 ++ w3 /\
    xtransition q0 w1 = last a q0 /\
    xtransition (last a q0) w2 = last b q0 /\
    xtransition (last b q0) w3 = last c (last b q0) /\
    w2 <> nil.
Proof.
  induction w as [|e w IH]; intros q0 a b c H H0 H1;
  simpl in H1.
  - destruct a, b; try contradiction.
    simpl in H1. assert (contra: length ([q0]) = length (a :: a0 ++ a1 :: b ++ c)).
                   rewrite H1; auto.
    simpl in contra; rewrite app_length in contra; simpl in contra; omega.
  - destruct a as [|a0 a]. contradiction.
    assert (H2: delta g q0 e :: config' (delta g q0 e) w =
      a ++ b ++ c).
      simpl in H1; inversion H1; auto.
    destruct a as [|a1 a].
    + simpl in H2; clear IH H; exists nil;
      apply config_pumping2_0 in H2; simpl.
      destruct H2 as [w1 [w2 [H2 [H3 H4]]]].
      exists (e::w1), w2; repeat split.
      * simpl; rewrite H2; auto.
      * inversion H1; auto.
      * simpl; inversion H1; rewrite <- H5, H3;
        apply last_pumping; auto.
      * replace (last b q0) with (last b (delta g q0 e)).
        auto. apply last_pumping; auto.
      * intro contra; discriminate.
      * auto.
    + clear H1. apply IH in H2.
      destruct H2 as [w1 [w2 [w3 [H3 [H4 [H5 [H6 H7]]]]]]].
      assert (aux1: forall t1 t2, last (a1 :: a) t1 = last (a1 :: a) t2).
        intros t1 t2; apply last_pumping; intro contra; discriminate.
      assert (aux2: forall t1 t2, last b t1 = last b t2).
        intros t1 t2; apply last_pumping; auto.
      exists (e::w1), w2, w3. repeat split; auto.
      * simpl; rewrite H3; auto.
      * simpl (xtransition q0 (e :: w1)); rewrite H4.
        replace (last (a0 :: a1 :: a) q0) with (last (a1::a) q0). 2: auto.
        apply aux1.
      * replace (last (a0 :: a1 :: a) q0) with (last (a1::a) q0). 2: auto.
        replace (last (a1 :: a) q0) with (last (a1 :: a) (delta g q0 e)). 2: apply aux1.
        rewrite H5; apply aux2.
      * replace (last b q0) with (last b (delta g q0 e)). 2: apply aux2.
        apply H6.
      * intro contra; discriminate.
      * auto.
Qed.

Lemma config_pumping4 w : forall q c1 c2 c3,
  config w = c1 ++ [q] ++ c2 ++ [q] ++ c3 ->
  exists w1 w2 w3, w = w1 ++ w2 ++ w3 /\ w2 <> [] /\
  ixtransition (w1 ++ w3) = ixtransition w /\
  ixtransition (w1 ++ w2) = ixtransition w1.
Proof.
  assert (H10: forall (l:list A) o, l ++ [o] <> []).
    intros l o contra; destruct l; discriminate.
  unfold config, ixtransition;
  generalize dependent (q0 g);
  intros q0 q c1 c2 c3 H.
  rewrite (app_assoc c1), (app_assoc c2) in H.
  pose H as H0.
  apply config_pumping2_1 in H0.
  destruct H0 as [w1 [w2 [w3 [H0 [H1 [H2 [H3 H4]]]]]]].
  assert (H5: last (c1 ++ [q]) q0 = last (c2 ++ [q]) q0). {
    clear H H0 H1 H2 H3 H4.
    induction c2 as [|c c2 IH]; simpl.
    - induction c1 as [|c c1 IH]; auto.
      simpl; destruct (c1 ++ [q]) eqn:H.
      apply H10 in H; destruct H.
      auto.
    - simpl; destruct (c2 ++ [q]) eqn:H.
      apply H10 in H; destruct H.
      auto.
  }
  exists w1, w2, w3; repeat split; auto.
  rewrite H0, xtransition_distr, xtransition_distr, xtransition_distr.
  rewrite H1, H2.
  rewrite H5; auto.
  rewrite xtransition_distr, H1, H2, H5; auto.
  1-2: apply H10.
Qed.

Lemma pumping1 w :
  length w >= length (Q g) ->
  exists w1 w2 w3, w = w1 ++ w2 ++ w3 /\ w2 <> [] /\
  ixtransition (w1 ++ w3) = ixtransition w /\
  ixtransition (w1 ++ w2) = ixtransition w1.
Proof.
  intro H;
  assert (H0: length (config w) > length (Q g)). rewrite config_length; omega.
  apply config_pumping3 in H0; destruct H0 as [q [c1 [c2 [c3 H0]]]];
  eapply config_pumping4; apply H0.
Qed.

Fixpoint word_pow (w:list B) (n:nat) :=
  match n with
  | O => []
  | S n' => w ++ (word_pow w n')
  end.

Lemma pumping_pow w n :
  length w >= length (Q g) ->
  exists w1 w2 w3, w = w1 ++ w2 ++ w3 /\ w2 <> [] /\
  ixtransition (w1 ++ (word_pow w2 n) ++ w3) = ixtransition w /\
  ixtransition (w1 ++ w3) = ixtransition w.
Proof.
  intros H;
  apply pumping1 in H; destruct H as [w1 [w2 [w3 [H1 [H2 [H3 H4]]]]]];
  exists w1, w2, w3; repeat split;
  try (induction n);
  try (simpl; rewrite app_assoc, app_assoc, ixtransition_distr, ixtransition_distr, H4;
    rewrite <- ixtransition_distr, <- ixtransition_distr, <- app_assoc);
  auto.
Qed.

Lemma pumping2 w :
  length w >= length (Q g) ->
  exists w1 w2 w3 : list B, ixtransition (w1 ++ w3) = ixtransition w /\
  length (w1 ++ w3) < length (Q g) /\ ixtransition (w1 ++ w2) = ixtransition w1.
Proof.
  remember (length w) as n eqn:H.
  generalize dependent w.
  induction n as [|n IH]; intros w H H0.
  - assert (H1: length (Q g) = 0). omega.
    apply length_zero_iff_nil in H1;
    pose proof Q_not_nil; contradiction.
  - destruct w as [|e w' L] using @rev_ind; simpl in H. omega.
    clear L;
    rewrite app_length in H; simpl in H; rewrite Nat.add_1_r in H;
    injection H; intro H1.
    pose proof (Nat.leb_spec0 (length (Q g)) n) as H2.
    destruct (length (Q g) <=? n); inversion H2; clear H2.
    + apply IH in H1. 2: omega.
      destruct H1 as [w1 [w2 [w3 H1]]].
      pose proof (Nat.ltb_spec0 (length (w1 ++ w3 ++ [e])) (length (Q g))) as H4.
      destruct (length (w1 ++ w3 ++ [e]) <? length (Q g)); inversion H4; clear H4.
      * exists w1, w2, (w3 ++ [e]); repeat split.
        destruct H1 as [H1 _]; rewrite app_assoc;
          rewrite ixtransition_distr, H1, <- ixtransition_distr; trivial.
        auto.
        intuition.
      * assert (H4: length (w1 ++ w3 ++ [e]) = length (Q g)).
        apply not_lt in H2; rewrite app_assoc, app_length in H2; simpl in H2;
        rewrite app_assoc, app_length; simpl; omega. clear H2.
        assert (H5: length (w1 ++ w3 ++ [e]) >= length (Q g)). omega.
        apply pumping1 in H5; destruct H5 as [w1' [w2' [w3' [H5 [H6 H7]]]]].
        exists w1', w2', w3'. repeat split.
        destruct H7 as [H7 _].
        destruct H1 as [H1 _]; rewrite H7, app_assoc, ixtransition_distr, H1,
          <- ixtransition_distr; trivial.
        assert (H8: length (w1 ++ w3 ++ [e]) = length (w1' ++ w2' ++ w3')). rewrite H5; trivial.
        rewrite H4, app_length, app_length in H8; rewrite app_length.
        assert (length w2' > 0). destruct w2'. contradiction. simpl; omega.
        omega.
        intuition.
    + apply not_le in H3; rewrite H1 in *; clear H1 IH.
      pose proof (Nat.ltb_spec0 (length (w' ++ [e])) (length (Q g))) as H4.
      destruct (length (w'++[e]) <? length (Q g)); inversion H4; clear H4.
      * exists w', [], [e]; repeat split; try (rewrite app_nil_r); trivial.
      * apply not_lt in H1; rewrite app_length in H1; simpl in H1.
        assert (length w' + 1 = length (Q g)). omega.
        assert (length (w' ++ [e]) >= length (Q g)). rewrite app_length; simpl; omega.
        apply pumping1 in H4; destruct H4 as [w1' [w2' [w3' [H5 [H6 H7]]]]].
        exists w1', w2', w3'; repeat split.
        intuition.
        assert (H8: length (w' ++ [e]) = length (w1' ++ w2' ++ w3')). rewrite H5; trivial.
        rewrite app_length, app_length, app_length in H8; simpl in H8; rewrite app_length.
        assert (length w2' > 0). destruct w2'. contradiction. simpl; omega.
        omega.
        intuition.
Qed.

Lemma pumping q :
  is_tangible q <-> exists w, ixtransition w = q /\ length w < length (Q g)
  /\ q <> (sink g).
Proof.
  split; intro H; destruct H as [H [w H0]].
  2: split; try (exists w); intuition.
  pose proof (Nat.leb_spec0 (length (Q g)) (length w)) as H1;
  destruct (length (Q g) <=? length w); inversion H1; clear H1.
  - assert (H3: length w >= length (Q g)). omega.
    apply pumping2 in H3; destruct H3 as [w1 [w2 [w3 H3]]];
    rewrite <- H0; exists (w1 ++ w3); rewrite <- H0 in H; intuition.
  - apply not_le in H2.
    exists w; split; try split; intuition; omega.
  - exists H; intuition.
Qed.

Fixpoint all_words'' (l:list (list B)) e :=
  match l with
  | w::l' => [w ++ [e]] ++ all_words'' l' e
  | nil => nil
  end.

Fixpoint all_words' l E :=
  match E with
  | e::E' => all_words'' l e ++ all_words' l E'
  | nil => nil
  end.

Fixpoint all_words1 (E:list B) :=
  match E with
  | e::E' => [[e]] ++ all_words1 E'
  | nil => nil
  end.

Fixpoint all_words (n:nat) :=
  match n with
  | 1 => all_words1 (E g)
  | O => [[]]
  | S n' => all_words' (all_words n') (E g)
  end.

Lemma all_words_correct1 n : forall w e,
  In w (all_words n) -> In e (E g) -> In (w++[e]) (all_words (S n)).
Proof.
  intros; simpl;
  destruct n.
  - destruct H.
    2: destruct H.
    rewrite <- H; simpl;
    induction (E g) as [|e0 E IH].
    + inversion H0.
    + simpl; inversion H0.
      * left; rewrite H1; auto.
      * right; apply IH; auto.
  - Arguments all_words : simpl never.
    induction (E g) as [|e0 E IH].
    inversion H0.
    simpl; apply in_or_app; inversion H0.
    + left; rewrite H1; simpl; clear IH;
      induction (all_words (S n)) as [|w0 l IH].
      * inversion H.
      * simpl; inversion H.
        -- left; rewrite H2; auto.
        -- right; apply IH; auto.
    + right; apply IH; intuition.
Qed.

Lemma all_words_correct n : forall w,
  is_generated w -> length w = n -> In w (all_words n).
Proof.
  intros w H.
  generalize dependent n.
  induction w as [|e w' IH] using @rev_ind; intros n H0.
  - simpl in H0; rewrite <- H0; simpl; left; trivial.
  - destruct n.
    + rewrite app_length in H0; simpl in H0; omega.
    + apply all_words_correct1; try (apply IH).
      * eapply prefix_closed; apply H.
      * rewrite app_length in H0; simpl in H0; omega.
      * unfold is_generated, ixtransition in H; clear IH H0;
        generalize dependent (q0 g);
        induction w' as [|e0 w' IH]; intros q H; simpl in H.
        -- apply delta_correct in H; intuition.
        -- eapply IH; apply H.
Qed.

Fixpoint all_words_le (n:nat) :=
  match n with
  | S n' => all_words (S n') ++ all_words_le n'
  | O => [nil]
  end.

Lemma all_words_le_correct n : forall w,
  is_generated w -> length w <= n -> In w (all_words_le n).
Proof.
  intros w H H0.
  induction n as [|n' IH].
  - left; symmetry; apply length_zero_iff_nil; omega.
  - Arguments all_words : simpl never.
    simpl; apply in_or_app;
    inversion H0.
    + left; apply all_words_correct; intuition.
    + right; apply IH; intuition.
Qed.

Fixpoint verify_tangible' q l :=
  match l with
  | a::l' => ixtransition a = q \/ verify_tangible' q l'
  | nil => False
  end.
Definition verify_tangible q := q <> (sink g) /\ verify_tangible' q (all_words_le (length (Q g) - 1)).

Lemma verify_tangible_correct1 : forall q,
  is_tangible q -> verify_tangible q.
Proof.
  intros q H; apply pumping in H; destruct H as [w [H [H1 H2]]].
  assert (H0: length w <= length (Q g) - 1). omega.
  apply all_words_le_correct in H0.
  2: unfold is_generated; rewrite H; intuition.
  unfold verify_tangible;
  induction (all_words_le (length (Q g) - 1)) as [|a l' IH].
  - pose proof in_nil; contradiction.
  - inversion H0; split.
    1,3: intuition.
    + left; rewrite H3; intuition.
    + right; intuition.
Qed.

Lemma verify_tangible_correct : forall q,
  is_tangible q <-> verify_tangible q.
Proof.
  split.
  apply verify_tangible_correct1.
  intros [H H0];
  unfold verify_tangible in H;
  induction (all_words_le (length (Q g) - 1)) as [|a l' IH];
  destruct H0; split.
  1,3: intuition.
  - exists a; intuition.
  - apply IH in H0; destruct H0 as [H0 [w H1]]; exists w;
    intuition.
Qed.

Lemma verify_tangible_decidable : forall q,
  q <> (sink g) -> {verify_tangible q} + {~ verify_tangible q}.
Proof.
  intros q H0; unfold verify_tangible;
  induction (all_words_le (length (Q g) - 1)) as [|a l' IH].
  - simpl; right; unfold not; intros [_ contra]; apply contra.
  - simpl. destruct (Q_decidable g (ixtransition a) q).
    + intuition.
    + destruct IH.
      * intuition.
      * right; intros [H1 contra]; destruct contra.
        2: assert (q <> sink g /\ verify_tangible' q l').
        2: intuition.
        1,2: contradiction.
Qed.

Theorem tangible_decidable : forall q,
  {is_tangible q} + {~ is_tangible q}.
Proof.
  intro q;
  destruct (Q_decidable g q (sink g)) as [H|H].
  - right; unfold is_tangible; intros [contra _];
    contradiction.
  - destruct (verify_tangible_decidable q) as [H0|H0].
    + intuition.
    + apply verify_tangible_correct in H0; intuition.
    + right; intro contra; apply verify_tangible_correct in contra;
    contradiction.
Qed.

End DFA.




