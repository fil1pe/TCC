Require Import Coq.Init.Nat Coq.Lists.List Omega
  DFA QueueingSystems QSUtils.
Require BinIntDef.
Import ListNotations.
Local Open Scope Z_scope.


Module UpperBound (G : QS).

  Include G.

  Include BufferUtils.

  Include DFAUtils.

  Definition n_upper_bounded := forall w, is_generated w -> n0 + count_buffer w <= n.

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

  (* Theorem vub_never_runs_out_of_fuel :
    nth 0
        (verify_upper_bound' (Some 1 :: initial_solution states_num) (S states_num) 0%nat n0)
        None
    <> Some 2.
  Proof.
  Admitted. *)

  Inductive is_vub_medsolution : list (option Z) -> Prop :=
    | vub_sol_0 :
        is_vub_medsolution (Some 1 :: initial_solution states_num)
    | vub_sol_1 :
        is_vub_medsolution (update (Some 1 :: initial_solution states_num) 1 n0)
    | vub_msol s q e m :
        is_vub_medsolution s -> is_vub_medsolution (update s (S q) m) ->
        is_vub_medsolution (update (update s (S q) m) (S (xtransition q [e])) (m + count_event e)).

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

  Lemma vub_updated'' : forall i s u a m m' q',
    length (a :: update s i m) = S states_num ->
    nth (S i) (verify_upper_bound' (a :: update s i m) u
      q' m') None = nth (S i) (a :: update s i m) None.
  Proof.
    intros i s u.
    generalize dependent i.
    generalize dependent s.
    induction u as [|u IH]; intros s i a m m' q' H. reflexivity.
    simpl.
    destruct (length (update s i m) <=? q')%nat eqn:H0. reflexivity.
    destruct (optZ_eq (nth q' (update s i m) None) None) eqn:H1.
    destruct (q' =? i)%nat eqn:eq.
    apply beq_nat_true in eq; rewrite eq, nth_update in H1. discriminate H1.
      rewrite <- eq; rewrite update_length in H0; apply leb_complete_conv in H0; auto.
    clear H0; clear H1.
    2: destruct (optZ_ge (nth q' (update s i m) None) (Some m')); reflexivity.
    rewrite nth_max_lists. {
      rewrite update_comm.
      rewrite IH.
      2: simpl; rewrite update_length, update_length; simpl in H;
        rewrite update_length in H; auto.
      2: apply beq_nat_false; rewrite Nat.eqb_sym; auto.
      induction events_num_minus_1.
        simpl; replace (nth i (initial_solution states_num_minus_1 ++ [None]) None) with
          (nth (S i) (Some 0::initial_solution states_num) None). 2: reflexivity.
          rewrite vub_s0_none, max_none. apply nth_update_update.
      simpl.
      simpl in H; rewrite update_length in H.
      rewrite nth_max_lists.
      2:    rewrite vub_foreach_length, vub_length; auto.
      2,3:  simpl; rewrite update_length, update_length; auto.
      rewrite IH.
      2: simpl; rewrite update_length, update_length; auto.
      rewrite max_distr, max_refl; apply IHn1.
    }
    rewrite vub_foreach_length, vub_length; simpl.
    1-3: simpl in H; rewrite <- update_length with (n:=q')(a0:=m') in H;
      auto.
  Qed.

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
    intros q q' a s m en H H0.
    generalize dependent q'.
    induction en as [|en IH]; intro q'. {
      simpl; rewrite nth_max_lists.
      2: rewrite vub_s0_length; rewrite vub_length; simpl; rewrite update_length;
        rewrite H; reflexivity.
      rewrite vub_updated'';
      replace (Some 0 :: initial_solution states_num_minus_1 ++ [None])
        with (Some 0 :: initial_solution states_num); try (rewrite vub_s0_none).
      simpl; rewrite nth_update.
      4: simpl; rewrite update_length; apply eq_S.
      1-5: auto.
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
    rewrite IH, vub_updated''; simpl; apply eq_S in H. rewrite nth_update.
    simpl; destruct (m >=? m); reflexivity.
    2: rewrite update_length.
    1-2: auto.
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
    remember (all_but_first_le s n) as b.
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
    remember (all_but_first_le s n) as b;
    clear Heqb.
    assert (s = verify_upper_bound' s0 (S states_num) 0%nat n0). auto.
    unfold verify_upper_bound' in Heqs.
    destruct (length s0 <=? 1)%nat eqn:H0. {
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

  Lemma vub_tangible : forall s o q,
    o::s = verify_upper_bound' (Some 1 :: initial_solution states_num) (S states_num) 0%nat n0 ->
    (nth q s None <> None <-> is_tangible q).
  Proof.
    (* unfold is_tangible.
    intros s o q H.
    split; intro H0. {
      split.
      - unfold is_sink_state, not; intro H1.
        assert (length (o::s) = S states_num). {
          rewrite H. rewrite vub_length; apply vub_s0_length. }
        simpl in H2; injection H2; intro H3.
        rewrite nth_overflow in H0. contradiction.
        omega.
      - admit.
    } *)
  Admitted.

  Lemma transition_upper_bound : n_upper_bounded ->
    forall q e, is_tangible q -> is_valid_event e = true -> is_proper_transition q e ->
    state_upper_bound (xtransition q [e]) >= state_upper_bound q + count_event e.
  Proof.
    intros H q e H0 H1 H2.
    apply vub_correct in H; unfold verify_upper_bound in H.
    unfold state_upper_bound, verify_upper_bound.
    remember (Some 1 :: initial_solution states_num) as s0;
    remember (verify_upper_bound' s0 (S states_num) 0%nat n0) as s;
    remember (all_but_first_le s n) as b.
    destruct s as [|o s]. admit.
    rewrite fst_extract.
    simpl in H; destruct (optZ_eq o (Some 0)) eqn:H3. 2: discriminate H.
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

End UpperBound.


Module Example.

  Module QS0 <: QS.
    Definition states_num_minus_1 : nat := 5.
    Definition events_num_minus_1 : nat := 2.
    Definition transition (q:state) (e:event) : state :=
      match q, e with
        0%nat, 0%nat => 1%nat |
        1%nat, 0%nat => 2%nat |
        2%nat, 1%nat => 3%nat |
        3%nat, 1%nat => 1%nat |
        0%nat, 2%nat => 4%nat |
        4%nat, 0%nat => 5%nat |
        5%nat, 0%nat => 1%nat |
        _, _=> 6%nat
      end.
    Definition is_marked (q:state) := false.
    Definition count_event (e:event) :=
      match e with
        0%nat =>   1%Z  |
        1%nat => (-1)%Z |
          _   =>   0%Z
      end.
    Definition n := 3.
    Definition n0 := 0.
  End QS0.

  Include UpperBound QS0.

  Compute verify_upper_bound.

End Example.