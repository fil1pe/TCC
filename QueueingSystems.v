Require Import Coq.Init.Nat Coq.Lists.List Omega QSUtils DFA.
Import ListNotations Coq.Bool.Bool.
Require BinIntDef.
Local Open Scope Z_scope.

Definition count_event e :=
  match e with
     add  =>   1%Z  |
     rem  => (-1)%Z |
    oth e =>   0%Z
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

Axiom n : Z.
(* Definition n := 3. *)
Axiom n0 : Z.
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

Theorem exists_function__upper_bounded :
  ( exists f, f(0%nat) = n0 /\ forall q, is_tangible q -> 
     f(q) <= n /\ (forall e, is_valid_event e = true ->
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e ))
  -> n_upper_bounded.
Proof.
  unfold n_upper_bounded.
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
Qed.

Fixpoint oth_trans' q l : list state :=
  match l with
    e::l => xtransition q [oth e] :: oth_trans' q l |
     []  => []
  end.
Fixpoint oth_trans q := oth_trans' q other_event_list.

Fixpoint verify_upper_bound' (m:Z) (s:list (option Z)) (fuel:nat) (q:state) :=
match fuel with O => s | S fuel =>

    if (length s <=? S q)%nat then (* if q is a sink state *)
        update_last 0 s
    else if optZ_eq (nth q s None) None then
        let  s' := update s q m in
        let s'' := max_lists (verify_upper_bound' (m+1) s' fuel (transition q add)) (verify_upper_bound' (m-1) s' fuel (transition q rem)) in
        let  f  := verify_upper_bound' m s' fuel in
        s''
(*         foreach (oth_trans q) f max_lists s'' *)
    else if optZ_ge (nth q s None) (Some m) then (* if s[q] >= m *)
        update_last 0 s
    else (* if s[q] < m *)
        update_last 1 s

end.

Definition verify_upper_bound :=
  let s := verify_upper_bound' n0 (initial_solution states_num ++ [Some 1]) (S states_num) 0%nat in
  extract 0 s [] (all_but_last_le s n).

(* Compute verify_upper_bound. *)

Lemma initial_solution_none : forall m,
  nth 0 (initial_solution states_num ++ [Some 1]) m = None.
Proof.
Admitted.

Theorem verify_upper_bound_correct :
  snd verify_upper_bound = true <-> n_upper_bounded.
Proof.
Admitted.

Definition state_upper_bound (q:state) :=
  match nth q (fst verify_upper_bound) None with
    Some x => x    |
     None  => n + 1
  end.

Require Import Coq.ZArith.Zbool.

Lemma q0_upper_bound : state_upper_bound 0%nat = n0.
Proof.
Admitted.

Theorem upper_bounded__exists_function : n_upper_bounded ->
  ( exists f, f(0%nat) = n0 /\ forall q, is_tangible q -> 
     f(q) <= n /\ (forall e, is_valid_event e = true ->
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e )).
Proof.
  intro H.
  exists state_upper_bound.
Admitted.

Theorem iff_exists_function__upper_bounded :
  ( exists f, f(0%nat) = n0 /\ forall q, is_tangible q -> 
     f(q) <= n /\ (forall e, is_valid_event e = true ->
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e ))
  <-> n_upper_bounded.
Proof.
  split. apply exists_function__upper_bounded. apply upper_bounded__exists_function.
Qed.