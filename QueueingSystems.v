Require Import Coq.Init.Nat Coq.Lists.List Omega QSUtils DFA.
Import ListNotations Coq.Bool.Bool.
Require BinIntDef.
Local Open Scope Z_scope.

Definition count_event e :=
  match e with
    add =>   1%Z  |
    rem => (-1)%Z |
    oth =>   0%Z
  end.

Fixpoint count_buffer w :=
  match w with
     []  => 0                             |
    e::w => count_event e + count_buffer w
  end.

Lemma count_buffer_distr : forall w1 w2,
  count_buffer (w1 ++ w2) = count_buffer w1 + count_buffer w2.
Proof.
  intros w1 w2.
  induction w1 as [|e w1 IHw1].
  - reflexivity.
  - simpl. rewrite IHw1. omega.
Qed.

Lemma count_buffer_distr' : forall w e,
  count_buffer (w ++ [e]) = count_buffer w + count_event e.
Proof.
  intros w e.
  rewrite count_buffer_distr.
  simpl.
  omega.
Qed.

Axiom upper_bound : Z.
(* Definition upper_bound := 100. *)

Definition upper_bounded := forall w, is_generated w -> count_buffer w <= upper_bound.

Definition is_tangible q := ~ is_sink_state q /\ exists w, q = ixtransition w.

Lemma buffer_count_leq_f : forall (f:state->Z),
  ( f(0%nat) = 0 /\ forall q, is_tangible q -> forall e,
    is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e )
  -> forall w, is_generated w -> count_buffer w <= f(ixtransition w).
Proof.
  intros f [H H0] w H1.
  induction w as [|e w IHw] using @rev_ind.
  - simpl.
    rewrite ixtransition_nil__0.
    omega.
  - pose H1 as H2; apply prefix_closed in H2.
    apply IHw in H2.
    rewrite ixtransition_distr.
    rewrite count_buffer_distr'.
    remember (ixtransition w) as q eqn:eq_q.
    destruct (is_sink_stateb q) eqn:H3. {
      apply is_sink_stateb__is_sink_state in H3.
      apply prefix_closed in H1.
      unfold is_generated in H1.
      rewrite <- eq_q in H1.
      contradiction.
    }
    remember (xtransition q [e]) as q' eqn:eq_q'.
    destruct (is_sink_stateb q') eqn:H4. {
      unfold is_generated in H1.
      rewrite ixtransition_distr in H1.
      rewrite <- eq_q, <- eq_q' in H1.
      apply is_sink_stateb__is_sink_state in H4.
      contradiction.
    }
    assert (f q' >= f q + count_event e). {
      rewrite eq_q'.
      apply H0.
      - split.
        + apply isnt_sink_stateb__isnt_sink_state in H3.
          apply H3.
        + exists w.
          apply eq_q.
      - unfold is_proper_transition.
        rewrite <- eq_q'.
        apply isnt_sink_stateb__isnt_sink_state.
        apply H4.
    }
    omega.
Qed.

Theorem exists_function__upper_bounded :
  ( exists f, f(0%nat) = 0 /\ forall q, is_tangible q -> 
     f(q) <= upper_bound /\ (forall e,
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e ))
  -> upper_bounded.
Proof.
  unfold upper_bounded.
  intros [f [H H0]] w H1.
  assert (H2: count_buffer w <= f(ixtransition w)). {
    apply buffer_count_leq_f; try split; try (apply H); try (apply H0); try (apply H1).
  }
  assert (f (ixtransition w) <= upper_bound). {
    destruct (is_sink_stateb (ixtransition w)) eqn:H3.
    - apply is_sink_stateb__is_sink_state in H3.
      contradiction.
    - destruct H0 with (q:=ixtransition w). {
        split.
          - apply isnt_sink_stateb__isnt_sink_state.
            apply H3.
          - exists w.
            reflexivity.
      }
      apply H4.
  }
  omega.
Qed.

Fixpoint verify_upper_bound' (q:state) (m:Z) (s:list Z) (n:nat) :=
  match n with O => s | S n =>

    if (states_num <=? q)%nat then
        Return end_0 s
    else if nth q s (-1) =? -1 then
        let s' := update s q m in
        Return max3_lists (verify_upper_bound' (transition q add) (m+1) s' n)
                          (verify_upper_bound' (transition q rem) (m-1) s' n)
                          (verify_upper_bound' (transition q oth)   m   s' n)
    else if nth q s (-1) >=? m then
        Return end_0 s
    else
        Return end_1 s

  end.

Definition verify_upper_bound :=
  extract_0 (verify_upper_bound' 0%nat 0 (initial_solution states_num) (states_num+2)) [].

(* Compute verify_upper_bound. *)

Lemma initial_solution'_minus_1 :
  nth 0 (initial_solution' states_num) (-1) = -1.
Proof.
  unfold initial_solution'.
  simpl.
  induction states_num_minus_1.
  - reflexivity.
  - fold initial_solution'.
    fold initial_solution' in IHn.
    assert (nth 0 (initial_solution' n ++ [-1]) (-1) = nth 0 ((initial_solution' n ++ [-1]) ++ [-1]) (-1)).
    unfold nth.
    destruct (initial_solution' n ++ [-1]); reflexivity.
    rewrite <- H.
    apply IHn.
Qed.

Lemma initial_solution_minus_1 :
  nth 0 (initial_solution states_num) (-1) = -1.
Proof.
  unfold initial_solution.
  assert (nth 0 (initial_solution' states_num ++ [1]) (-1) = nth 0 (initial_solution' states_num) (-1)).
  unfold nth.
  destruct (initial_solution' states_num) eqn:eq.
  - fold (nth 0 ([] ++ [1]) (-1)).
    unfold initial_solution' in eq.
    simpl in eq.
    fold (initial_solution' states_num_minus_1) in eq.
    destruct (initial_solution' states_num_minus_1); discriminate eq.
  - reflexivity.
  - rewrite H.
    apply initial_solution'_minus_1.
Qed.

Theorem verify_upper_bound_correct :
  snd verify_upper_bound = true <-> upper_bounded.
Proof.
  unfold upper_bounded.
  split; intro H.
  - intros w H0.
    admit.
  - unfold verify_upper_bound.
    simpl.
    rewrite initial_solution_minus_1.
    simpl.
Admitted.


Definition state_upper_bound (q:state) := nth q (fst verify_upper_bound) (-1).

Theorem upper_bounded__exists_function : upper_bounded ->
  ( exists f, f(0%nat) = 0 /\ forall q, is_tangible q -> 
     f(q) <= upper_bound /\ (forall e,
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e )).
Proof.
  intro H.
  exists state_upper_bound.
Admitted.

Theorem iff_exists_function__upper_bounded :
  ( exists f, f(0%nat) = 0 /\ forall q, is_tangible q -> 
     f(q) <= upper_bound /\ (forall e,
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e ))
  <-> upper_bounded.
Proof.
  split. apply exists_function__upper_bounded. apply upper_bounded__exists_function.
Qed.