Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.
Require Import DFA.

Require BinIntDef.
Require Import Omega.
Local Open Scope Z_scope.

Axiom E : Type.
Inductive event := add | rem | other (e : E).
Definition E' := event.
Axiom Q : Type.
Axiom G : @DFA Q E'.
Definition q0 := initial_state G.
Definition pq0 := proper_state q0.
Definition transition := transition G.
Definition is_proper_transition q e := exists q',
  proper_state q' = transition q e.
Definition xtransition := extended_transition G.
Definition ixtransition := xtransition pq0.
Definition generates w := ~ ixtransition w = sink_state.

Lemma ixtransition_nil__pq0: ixtransition [] = pq0.
Proof. auto. Qed.

Lemma extended_transition__transition: forall q e,
  xtransition (proper_state q) [e] = transition q e.
Proof. apply DFA.extended_transition__transition. Qed.
Lemma transition_sink_state: forall w,
  xtransition sink_state w = sink_state.
Proof. apply DFA.transition_sink_state. Qed.
Lemma dist_xtransition: forall w w' q,
  xtransition q (w ++ w') = xtransition (xtransition q w) w'.
Proof. apply DFA.dist_extended_transition. Qed.
Lemma dist_ixtransition: forall w w',
  ixtransition (w ++ w') = xtransition (ixtransition w) w'.
Proof. unfold ixtransition. intros w w'. apply dist_xtransition. Qed.
Theorem prefix_closed: forall w w',
  generates (w ++ w') -> generates w.
Proof. apply DFA.prefix_closed. Qed.

Definition count_event (e : E') :=
  match e with
    add => 1  |
    rem => -1 |
    other e' => 0
  end.

Fixpoint count_buffer w :=
  match w with
    [] => 0 |
    e::w' => count_event e + count_buffer w'
  end.

Lemma dist_count_buffer: forall w1 w2,
  count_buffer (w1 ++ w2) = count_buffer w1 + count_buffer w2.
Proof.
  intros w1 w2.
  induction w1 as [|e w1 IHw1].
  - auto.
  - simpl. rewrite IHw1. omega.
Qed.

Lemma dist_count_buffer': forall w e,
  count_buffer (w ++ [e]) = count_buffer w + count_event e.
Proof.
  intros w e.
  induction w as [|e' w IH]; simpl; try (rewrite IH); omega.
Qed.

Axiom n0 : Z.
Axiom n : Z.

Definition is_upper_bounded := forall w, generates w -> n0 + count_buffer w <= n.

Definition is_tangible q := exists w,
  proper_state q = ixtransition w.

Lemma buffer_count_leq_f: forall f,
  ( f(pq0) = n0 /\ forall q, is_tangible q -> forall e,
    is_proper_transition q e ->
      f(transition q e) >= f(proper_state q) + count_event e ) ->
  forall w, generates w -> n0 + count_buffer w <= f(ixtransition w).
Proof.
  intros f [H H0] w H1.
  induction w as [|e w IHw] using @rev_ind.
  - simpl.
    rewrite ixtransition_nil__pq0.
    omega.
  - pose H1 as H2; apply prefix_closed in H2.
    apply IHw in H2.
    rewrite dist_ixtransition.
    rewrite dist_count_buffer'.
    remember (ixtransition w) as q eqn:eq_q.
    destruct q.
    {
      apply prefix_closed in H1.
      unfold generates in H1.
      symmetry in eq_q.
      contradiction.
    }
    remember (xtransition (proper_state q) [e]) as q' eqn:eq_q'; destruct q' as [|q'].
    + unfold generates in H1; rewrite dist_ixtransition in H1.
      symmetry in eq_q'.
      rewrite eq_q in eq_q'.
      contradiction.
    + assert (H3: proper_state q' = transition q e).
      { rewrite extended_transition__transition in eq_q'; auto. }
      assert (f (proper_state q') >= f (proper_state q) + count_event e).
      {
        rewrite H3.
        apply H0.
        - exists w. auto.
        - exists q'. auto.
      }
      omega.
Qed.

Theorem upper_bound1:
  ( exists f, f(pq0) = n0 /\ forall q, is_tangible q ->
    f(proper_state q) <= n /\ ( forall e, is_proper_transition q e ->
      f(transition q e) >= f(proper_state q) + count_event e ) ) ->
  is_upper_bounded.
Proof.
  unfold is_upper_bounded.
  intros [f [H H0]] w H1.
  assert (H2: n0 + count_buffer w <= f(ixtransition w)).
  { apply buffer_count_leq_f; try split; try (apply H0); auto. }
  assert (f (ixtransition w) <= n).
  {
    destruct (ixtransition w) as [|q] eqn:eq.
    - contradiction.
    - destruct H0 with (q:=q); try (exists w); auto.
  }
  omega.
Qed.

Notation " w ~> q " := (ixtransition w = q) (at level 60).

Lemma g2__generates: forall w q,
  w ~> (proper_state q) -> generates w.
Proof.
  unfold generates, not.
  intros w q H H0.
  rewrite H in H0.
  discriminate.
Qed.

Lemma not_nil_if_count: forall w,
  count_buffer w > 0 -> w <> [].
Proof.
  unfold not.
  intros w H H0.
  destruct w.
  - inversion H.
  - discriminate.
Qed.

Lemma cycle: forall q,
  forall w, xtransition q w = q -> xtransition q (w++w) = q.
Proof.
  intros q w H.
  rewrite dist_xtransition.
  rewrite H.
  auto.
Qed.

Fixpoint word_pow (w:list E') (n:nat) :=
  match n with
    O => [] |
    S n => w ++ (word_pow w n)
  end.

Theorem count_word_pow: forall w n,
  count_buffer (word_pow w n) = (Z.of_nat n) * (count_buffer w).
Proof.
  intros w n.
  induction n as [|n IHn].
  - auto.
  - replace (word_pow w (S n)) with (w ++ word_pow w n).
    rewrite dist_count_buffer.
    rewrite IHn.
    rewrite Nat2Z.inj_succ, <- Zmult_succ_l_reverse.
    omega.
    auto.
Qed.

Lemma q0_cycle: forall w n,
  w ~> pq0 -> (word_pow w n) ~> pq0.
Proof.
  intros w n H.
  induction n as [|n IHn].
  - auto.
  - simpl.
    rewrite dist_ixtransition.
    rewrite H.
    auto.
Qed.

Lemma q0_cycle_count: forall w n,
  (count_buffer w > 0 /\ w ~> pq0) ->
  exists w', w' ~> pq0 /\ count_buffer w' > n.
Proof.
  intros w n [H H0].
  destruct n eqn:eq_n.
  - exists w. auto.
  - exists (word_pow w ((Pos.to_nat p)+1)).
    split.
    + apply q0_cycle.
      auto.
    + rewrite count_word_pow.
      assert (Z.pos p > 0). { apply Zgt_pos_0. }
      assert (Z.pos p + 1 <= Z.of_nat (Pos.to_nat p + 1) * count_buffer w).
      {
        replace (Z.pos p + 1) with ((Z.pos p + 1)*1); try omega.
        apply Zmult_le_compat; try omega.
        rewrite Z.add_1_r. replace ((Pos.to_nat p + 1)%nat) with ((S (Pos.to_nat p))); try omega.
        simpl.
        rewrite Zpos_P_of_succ_nat.
        rewrite positive_nat_Z.
        simpl.
        omega.
      }
      omega.
  - exists w.
    split.
    + auto.
    + rewrite <- eq_n.
      assert (n < 0). { rewrite eq_n. apply Zlt_neg_0. }
      omega.
Qed.

Lemma q0_cycle_no_upper_bound:
  (exists w, w ~> pq0 /\ count_buffer w > 0) -> ~ is_upper_bounded.
Proof.
  unfold is_upper_bounded, not.
  intros [w [H H0]] H1.
  assert (H2: count_buffer w > 0 /\ w ~> pq0). auto.
  apply q0_cycle_count with(n:=(n-n0)) in H2.
  destruct H2 as [w' [H2 H3]].
  apply g2__generates, H1 in H2.
  omega.
Qed.

Definition state_upper_bound q m :=
  forall w, w ~> q -> n0 + count_buffer w <= m.

Definition min_state_upper_bound q m :=
  state_upper_bound q m /\ ~ state_upper_bound q (m-1).

Theorem q0_n0_bounded: is_upper_bounded -> min_state_upper_bound pq0 n0.
Proof.
  unfold min_state_upper_bound, state_upper_bound.
  intro H.
  split.
  - intros w H0.
    destruct (count_buffer w) eqn:eq_count.
    + omega.
    + assert (count_buffer w > 0). { rewrite eq_count. apply Zgt_pos_0. }
      assert (exists w, w ~> pq0 /\ count_buffer w > 0). { exists w. auto. }
      apply q0_cycle_no_upper_bound in H2.
      contradiction.
    + assert (Z.neg p < 0). { apply Zlt_neg_0. }
      omega.
  - unfold not. intro H0.
    assert (H1: [] ~> pq0). { auto. }
    apply H0 in H1.
    simpl in H1.
    omega.
Qed.

Lemma transition_upper_bound: forall q m1 m2 e,
  is_tangible q -> min_state_upper_bound (proper_state q) m1 ->
  min_state_upper_bound (transition q e) m1 -> m2 >= m1 + count_event e.
Proof.
Admitted.

Axiom func_choice : forall A B (R : A -> B -> Prop),
  (forall x, exists y, R x y) -> exists f, forall x, R x (f x).

Definition f_prop pq m := forall q,
  pq = proper_state q -> is_tangible q -> min_state_upper_bound pq m.

Lemma f_def:
  is_upper_bounded -> exists f, forall q, f_prop q (f q).
Proof.
  intro H.
  apply func_choice.
  unfold f_prop.
  intro q.
Admitted.

Lemma f_unicity: forall q m1 m2,
  min_state_upper_bound q m1 -> min_state_upper_bound q m2 -> m1 = m2.
Proof.
Admitted.

Theorem upper_bound2:
  is_upper_bounded ->
  ( exists f, f(pq0) = n0 /\ forall q, is_tangible q ->
    f(proper_state q) <= n /\ ( forall e, is_proper_transition q e ->
      f(transition q e) >= f(proper_state q) + count_event e ) ).
Proof.
  intro H.
  pose H as H0; apply f_def in H0; destruct H0 as [f H0].
  unfold f_prop in H0.
  exists f.
  split.
  - destruct H0 with (q:=pq0) (q0:=q0); try (exists []); auto.
    apply q0_n0_bounded in H.
    apply f_unicity with (q:=pq0); unfold min_state_upper_bound; auto.
  - intros q H1.
    split.
    + 
Admitted.

Theorem upper_bound:
  ( exists f, f(pq0) = n0 /\ forall q, is_tangible q ->
    f(proper_state q) <= n /\ ( forall e, is_proper_transition q e ->
      f(transition q e) >= f(proper_state q) + count_event e ) ) <->
  is_upper_bounded.
Proof.
  split. apply upper_bound1. apply upper_bound2.
Qed.








