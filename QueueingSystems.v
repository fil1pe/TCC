Require Import Coq.Init.Nat Coq.Lists.List Omega QSUtils DFA.
Import ListNotations Coq.Bool.Bool.
Require BinIntDef.
Local Open Scope Z_scope.

Module QS <: DFA.

Parameter states_num_minus_1 : nat.
(* Definition states_num_minus_1 : nat := 5. *)

Parameter oth_events_num : nat.
(* Definition oth_events_num : nat := 1. *)

Definition events_num_minus_1 := S oth_events_num.

Parameter transition : state->event->state.
(* Definition transition (q:state) (e:event) : state :=
  match q, e with
    0%nat, 0%nat => 1%nat |
    1%nat, 0%nat => 2%nat |
    2%nat, 1%nat => 3%nat |
    3%nat, 1%nat => 1%nat |
    0%nat, 2%nat => 4%nat |
    4%nat, 0%nat => 5%nat |
    5%nat, 0%nat => 1%nat |
    _, _=> 6%nat
  end. *)

Parameter is_marked : state->bool.

Include DFAUtils.

Definition count_event (e:event) :=
  match e with
    0%nat =>   1%Z  |
    1%nat => (-1)%Z |
      _   =>   0%Z
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

Parameter n : Z.
(* Definition n := 3. *)

Parameter n0 : Z.
(* Definition n0 := 0. *)

Definition n_upper_bounded := forall w, is_generated w -> n0 + count_buffer w <= n.

Definition is_tangible q := ~ is_sink_state q /\ exists w, q = ixtransition w.

Lemma buffer_count_leq_f : forall (f:state->Z),
  ( f(0%nat) = n0 /\ forall q, is_tangible q -> forall e, is_valid_event e = true ->
    is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e )
  -> forall w, is_generated w -> n0 + count_buffer w <= f(ixtransition w).
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
      - pose eq_q' as H5.
        unfold xtransition in H5.
        rewrite H3 in H5.
        destruct (is_valid_event e).
        * reflexivity.
        * apply isnt_sink_stateb__isnt_sink_state in H4.
          unfold is_sink_state in H4.
          omega.
      - unfold is_proper_transition.
        rewrite <- eq_q'.
        apply isnt_sink_stateb__isnt_sink_state.
        apply H4.
    }
    omega.
Qed.

Fixpoint trans_list' q events_num :=
  match events_num with
    S n => (n, xtransition q [n]) :: trans_list' q n |
     O  => []
  end.
Definition trans_list q := trans_list' q events_num.

Fixpoint verify_upper_bound' (s:list (option Z)) (fuel:nat) (q:state) (m:Z) :=
match fuel with O => s | S fuel =>

    if (length s <=? S q)%nat then (* if q is a sink state *)
        update s 0 0
    else if optZ_eq (nth (S q) s None) None then
        foreach (trans_list q)
                (verify_upper_bound' (update s (S q) m) fuel)
                (fun e => m + count_event e)
                max_lists
                (Some 0 :: initial_solution states_num)
    else if optZ_ge (nth (S q) s None) (Some m) then (* if s[q+1] >= m *)
        update s 0 0
    else (* if s[q+1] < m *)
        update s 0 1

end.

Definition verify_upper_bound :=
  let s := verify_upper_bound' (Some 1 :: initial_solution states_num) (S states_num) 0%nat n0 in
  extract 0 s (all_but_first_le s n).

(* Compute verify_upper_bound. *)

Lemma initial_solution_none : forall m p,
  nth 1 (p::initial_solution states_num) m = None.
Proof.
  intros m p.
  simpl.
  induction states_num_minus_1 as [|sn IHsn]. reflexivity.
  simpl.
  rewrite app_nth1.
  apply IHsn.
  rewrite app_length.
  simpl.
  omega.
Qed.

Theorem verify_upper_bound_correct :
  snd verify_upper_bound = true <-> n_upper_bounded.
Proof.
Admitted.

Definition state_upper_bound (q:state) :=
  match nth q (fst verify_upper_bound) None with
    Some x => x |
     None  => n
  end.

Lemma tangible_state_upper_bound : n_upper_bounded ->
  forall q, state_upper_bound q <= n.
Proof.
  intros H q.
  apply verify_upper_bound_correct in H; unfold verify_upper_bound in H.
  unfold state_upper_bound, verify_upper_bound.
  remember (Some 1 :: initial_solution states_num) as s0;
  remember (verify_upper_bound' s0 (S states_num) 0%nat n0) as s;
  remember (all_but_first_le s n).
  destruct s. discriminate H.
  apply extract_true in H.
  rewrite fst_extract.
  simpl in Heqb. rewrite Heqb in H.
  destruct (nth q s) as [x|] eqn:eq.
  2: omega.
  eapply all_le_nth.
  apply H.
  apply eq.
Qed.

Lemma q0_upper_bound : state_upper_bound 0%nat = n0.
Proof.
  unfold state_upper_bound, verify_upper_bound.
Admitted.

Lemma transition_upper_bound : n_upper_bounded ->
  forall q e, is_tangible q -> is_valid_event e = true -> is_proper_transition q e ->
  state_upper_bound (xtransition q [e]) >= state_upper_bound q + count_event e.
Proof.
Admitted.

Theorem iff_exists_function__upper_bounded :
  ( exists f, f(0%nat) = n0 /\ forall q, is_tangible q -> 
     f(q) <= n /\ (forall e, is_valid_event e = true ->
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e ))
  <-> n_upper_bounded.
Proof.
  split.

  - unfold n_upper_bounded.
    intros [f [H H0]] w H1.
    assert (H2: n0 + count_buffer w <= f(ixtransition w)). {
      apply buffer_count_leq_f; try split; try (apply H); try (apply H0); try (apply H1).
    }
    assert (f (ixtransition w) <= n). {
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

  - intro H.
    exists state_upper_bound.
    split.
    2: intros q H0; split.
    + apply q0_upper_bound.
    + apply tangible_state_upper_bound; auto.
    + intros e H1 H2; apply transition_upper_bound; auto.
Qed.

End QS.