Require Import Coq.Init.Nat Coq.Lists.List Omega QSUtils DFA.
Import ListNotations Coq.Bool.Bool.
Require BinIntDef.
Local Open Scope Z_scope.

Module QS <: DFA.

Parameter states_num_minus_1 : nat.
(* Definition states_num_minus_1 : nat := 5. *)

Parameter events_num_minus_1 : nat.
(* Definition events_num_minus_1 : nat := 2. *)

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

Parameter count_event : event->Z.
(* Definition count_event (e:event) :=
  match e with
    0%nat =>   1%Z  |
    1%nat => (-1)%Z |
      _   =>   0%Z
  end. *)

Parameter n : Z.
(* Definition n := 3. *)

Parameter n0 : Z.
(* Definition n0 := 0. *)

Include DFAUtils.

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

Fixpoint verify_upper_bound' (s:list (option Z)) (fuel:nat) (q:state) (m:Z) :=
match fuel with O => update s 0 2 | S fuel =>

    if (length s <=? S q)%nat then (* if q is a sink state *)
        update s 0 0
    else if optZ_eq (nth (S q) s None) None then
        foreach (transition_list q)
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

(* Theorem vub_never_runs_out_of_fuel :
  nth 0
      (verify_upper_bound' (Some 1 :: initial_solution states_num) (S states_num) 0%nat n0)
      None
  <> Some 2.
Proof.
Admitted. *)

Lemma vub_s0_none : forall q sn o,
  nth (S q) (Some o::initial_solution sn) None = None.
Proof.
  intros q sn; simpl.
  induction sn as [|sn IH]. destruct q; try (destruct q); reflexivity.
  simpl; destruct (q <? length (initial_solution sn))%nat eqn:H.
  apply Nat.ltb_lt in H. rewrite app_nth1. try (apply IH). apply H.
  rewrite app_nth2.
    remember (q - length (initial_solution sn))%nat as n1;
      destruct n1; try (destruct n1); reflexivity.
    apply Nat.ltb_ge in H; omega.
Qed.

Lemma vub_s0_length : forall o,
  length (Some o :: initial_solution states_num) = S states_num.
Proof.
  intro o.
  induction states_num as [|n1 IHn1]; simpl;
  try (simpl in IHn1; rewrite app_length; simpl; rewrite Nat.add_1_r;
  rewrite <- IHn1); reflexivity.
Qed.

Lemma vub_foreach_length' : forall q en s u f,
  (forall (s : list (option Z)) (q : state) (m : Z),
      length s = S states_num ->
      length (verify_upper_bound' s u q m) = length s) ->
  (length s = S states_num ->
  length (foreach (transition_list' q en)
    (verify_upper_bound' s u)
    f max_lists
    (Some 0 :: initial_solution states_num)) =
  length s).
Proof.
  intros q en s u f H0 H.
  induction en as [|en IH].
  remember (Some 0 :: initial_solution states_num) as s0;
    simpl; rewrite Heqs0; rewrite vub_s0_length; auto.
  simpl; simpl in IH; rewrite max_lists_length;
  rewrite H0; try (rewrite IH); auto.
Qed.

Lemma vub_length : forall s u q m,
  length s = S states_num ->
  length (verify_upper_bound' s u q m) = length s.
Proof.
  intros s u.
  generalize dependent s.
  induction u as [|u IH]; intros s q m H. apply update_length.
  simpl; destruct (length s <=? S q)%nat.
  2: destruct (optZ_eq (nth (S q) s None)).
  3: destruct (optZ_ge (nth (S q) s None) (Some m)).
  1,3-4: apply update_length.
  rewrite max_lists_length.
  rewrite IH; rewrite update_length; auto.
  rewrite IH; rewrite update_length; symmetry.
  replace (Some 0 :: initial_solution states_num_minus_1 ++ [None])
    with (Some 0 :: initial_solution states_num).
  2-3: auto.

  rewrite vub_foreach_length'.
  apply update_length.
  apply IH.
  rewrite <- H; apply update_length.
Qed.

Lemma vub_foreach_length : forall q en s u f,
  length s = S states_num ->
  length (foreach (transition_list' q en)
    (verify_upper_bound' s u)
    f max_lists
    (Some 0 :: initial_solution states_num)) =
  length s.
Proof.
  intros q en s u f H.
  apply vub_foreach_length'.
  intros; apply vub_length.
  1-2: auto.
Qed.

(* Lemma vub_updated'' : forall q q' u a s m en,
  length s = states_num ->
  (q < length s)%nat ->
  nth (S q) (verify_upper_bound' (a :: update s q m) u
    q' (m + count_event en)) None = Some m.
Proof.
  intros q q' u a s m en H H0.
  induction u. admit.
  simpl.
Admitted. *)

Lemma vub_updated'' : forall q q' a s m en,
  length s = states_num ->
  (q < length s)%nat ->
  nth (S q) (verify_upper_bound' (a :: update s q m) (length s)
    q' (m + count_event en)) None = Some m.
Proof.
  intros q q' a s m en H H0.
Admitted.

Lemma vub_updated' : forall q q' a s m en,
  length s = states_num ->
  (q < length s)%nat ->
  nth (S q) (max_lists
              (verify_upper_bound' (a :: update s q m) (length s)
                q' (m + count_event en))
              (foreach (transition_list' q en)
                (verify_upper_bound' (a :: update s q m) (length s))
                (fun e : nat => m + count_event e) max_lists
                (Some 0 :: initial_solution states_num)))
  None = Some m.
Proof.
  intros.
  generalize dependent q'.
  induction en as [|en IH]; intro q'. {
    simpl; rewrite nth_max_lists.
    2: rewrite vub_s0_length; rewrite vub_length; simpl; rewrite update_length;
      rewrite H; reflexivity.
    rewrite vub_updated'';
    replace (Some 0 :: initial_solution states_num_minus_1 ++ [None])
      with (Some 0 :: initial_solution states_num); try (rewrite vub_s0_none); auto.
  }
  simpl;
  replace (initial_solution states_num_minus_1 ++ [None]) with (initial_solution states_num).
  2: reflexivity.
  remember (if is_sink_stateb q then states_num else if is_valid_event en then
            if is_sink_stateb (transition q en) then states_num else transition q en
            else states_num) as q''.
  clear Heqq''.
  rewrite nth_max_lists.
  2: rewrite max_lists_length, vub_length, vub_length; auto.
  4: rewrite vub_length; try (rewrite vub_foreach_length).
  2-6: simpl; rewrite update_length; rewrite H; reflexivity.
  rewrite IH.
  rewrite vub_updated''.
  simpl; destruct (m >=? m); reflexivity.
  apply H.
  apply H0.
Qed.

Lemma vub_updated : forall q s s' b m,
  length s = S states_num ->
  (S q < length s)%nat ->
  s' = verify_upper_bound' s (length s) q m ->
  optZ_eq (nth (S q) s None) None = true ->
  nth q (fst (extract 0 s' b)) None = Some m.
Proof.
  intros q s s' b m H2 H H0 H1; apply leb_iff_conv in H.
  pose vub_length as s_s'_length; specialize (s_s'_length s (length s) q m);
    rewrite <- H0 in s_s'_length.
  destruct s as [|a s]. apply leb_iff_conv in H; simpl in H; omega.
  simpl in H; simpl in H1; simpl in H0; rewrite H, H1 in H0;
  destruct s' as [|a' s']. discriminate s_s'_length.
  apply H2.
  rewrite fst_extract;
  replace (initial_solution states_num_minus_1 ++ [None]) with (initial_solution states_num) in H0.
  2: reflexivity.
  apply leb_iff_conv in H; eapply vub_updated' in H.
  rewrite <- H0 in H; apply H.
  injection H2; auto.
Qed.

Theorem vub_correct :
  n_upper_bounded <-> snd verify_upper_bound = true.
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
  apply vub_correct in H; unfold verify_upper_bound in H.
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
  remember (Some 1 :: initial_solution states_num) as s0;
  remember (verify_upper_bound' s0 (S states_num) 0%nat n0) as s;
  remember (all_but_first_le s n);
  clear Heqb.
  assert (s = verify_upper_bound' s0 (S states_num) 0%nat n0). auto.
  unfold verify_upper_bound' in Heqs.
  destruct (length s0 <=? 1)%nat eqn:?H. {
    rewrite Heqs0, vub_s0_length in H0; unfold states_num in H0; apply leb_complete in H0;
    omega.
  }
  destruct (optZ_eq (nth 1 s0 None) None) eqn:?H.
  rewrite vub_updated with (m:=n0) (s:=s0).
  reflexivity.
  rewrite Heqs0; apply vub_s0_length.
  apply leb_iff_conv; apply H0.
  rewrite Heqs0; rewrite vub_s0_length; rewrite <- Heqs0; apply H.
  apply H1.
  rewrite Heqs0 in H1; rewrite vub_s0_none in H1; simpl in H1;
    discriminate H1.
Qed.

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