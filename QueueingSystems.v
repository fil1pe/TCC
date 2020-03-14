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
Axiom n0 : Z.
(*
  Definition upper_bound := 100.
  Definition n0 := 0.
*)

Definition upper_bounded := forall w, is_generated w -> n0 + count_buffer w <= upper_bound.

Definition is_tangible q := ~ is_sink_state q /\ exists w, q = ixtransition w.

Lemma buffer_count_leq_f : forall (f:state->Z),
  ( f(0%nat) = n0 /\ forall q, is_tangible q -> forall e,
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
      - unfold is_proper_transition.
        rewrite <- eq_q'.
        apply isnt_sink_stateb__isnt_sink_state.
        apply H4.
    }
    omega.
Qed.

Theorem exists_function__upper_bounded :
  ( exists f, f(0%nat) = n0 /\ forall q, is_tangible q -> 
     f(q) <= upper_bound /\ (forall e,
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e ))
  -> upper_bounded.
Proof.
  unfold upper_bounded.
  intros [f [H H0]] w H1.
  assert (H2: n0 + count_buffer w <= f(ixtransition w)). {
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

Require Import Recdef.

Lemma verify_upper_bound'_halts: forall q m s,
  (length s <=? q)%nat = false ->
  optZ_eq (nth q s None) None = true ->
  (count_none (update s q m) < count_none s)%nat.
Proof.
  intros q m s H H0.
  apply leb_iff_conv in H.
  generalize dependent s.
  induction q.
  + intros s H H0.
    destruct s; simpl in H. omega.
    simpl.
    simpl in H0.
    rewrite H0.
    omega.
  + intros s H H0.
    destruct s. simpl in H; omega.
    simpl in H; apply lt_S_n in H.
    simpl in H0.
    simpl.
    destruct (optZ_eq o None); try (apply lt_n_S); apply IHq; auto.
Qed.

Function verify_upper_bound' (q:state) (m:Z) (s:list (option Z)) {measure count_none s} :=
    if (length s <=? q)%nat then (* if q is a sink state *)
        update_last 0 s
    else if optZ_eq (nth q s None) None then
        let s' := update s q m in
        max3_lists (verify_upper_bound' (transition q add) (m+1) s')
                   (verify_upper_bound' (transition q rem) (m-1) s')
                   (verify_upper_bound' (transition q oth)   m   s')
    else if optZ_ge (nth q s None) (Some m) then (* if s[q] >= m *)
        update_last 0 s
    else (* if s[q] < m *)
        update_last 1 s.
Proof.
  apply verify_upper_bound'_halts. apply verify_upper_bound'_halts. apply verify_upper_bound'_halts.
Qed.

Definition verify_upper_bound :=
  let s := verify_upper_bound' 0%nat n0 (initial_solution states_num ++ [Some 1]) in
  extract 0 s [] (all_but_last_le s upper_bound).

(* Compute verify_upper_bound. *)

Lemma initial_solution_none : forall m,
  nth 0 (initial_solution states_num ++ [Some 1]) m = None.
Proof.
  intro m.
  assert (H: forall l1 l2, l1 <> [] -> nth 0 (l1 ++ l2) m = nth 0 l1 m). {
    intros l1 l2 H.
    destruct l1.
    - contradiction.
    - reflexivity.
  }
  simpl.
  induction states_num_minus_1.
  - reflexivity.
  - assert (H1: initial_solution n ++ [None] <> []). {
      unfold not; intro contra; destruct (initial_solution n); discriminate contra.
    }
    pose H1 as H2.
    apply H with (l2:=[Some 1]) in H2.
    rewrite IHn in H2.
    simpl.
    rewrite <- app_assoc.
    remember (nth 0 ((initial_solution n ++ [None]) ++ [None] ++ [Some 1]) m) as aux.
    rewrite H2.
    rewrite Heqaux.
    apply H.
    apply H1.
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
    rewrite initial_solution_none.
    simpl.
Admitted.

Definition state_upper_bound (q:state) :=
  match nth q (fst verify_upper_bound) None with
    Some x => x              |
     None  => upper_bound + 1
  end.

Require Import Coq.ZArith.Zbool.

Lemma q0_upper_bound : state_upper_bound 0%nat = n0.
Proof.
  unfold state_upper_bound, verify_upper_bound.
  simpl.
  rewrite initial_solution_none.
  simpl.
  induction states_num_minus_1.
  - simpl.
    assert (H: n0 >=? n0 = true). { apply Z.geb_le; omega. }
    rewrite H.
    simpl.
    rewrite H.
    reflexivity.
  - simpl.
Admitted.

Theorem upper_bounded__exists_function : upper_bounded ->
  ( exists f, f(0%nat) = n0 /\ forall q, is_tangible q -> 
     f(q) <= upper_bound /\ (forall e,
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e )).
Proof.
  intro H.
  exists state_upper_bound.
Admitted.

Theorem iff_exists_function__upper_bounded :
  ( exists f, f(0%nat) = n0 /\ forall q, is_tangible q -> 
     f(q) <= upper_bound /\ (forall e,
        is_proper_transition q e -> f(xtransition q [e]) >= f(q) + count_event e ))
  <-> upper_bounded.
Proof.
  split. apply exists_function__upper_bounded. apply upper_bounded__exists_function.
Qed.