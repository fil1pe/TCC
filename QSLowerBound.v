Require Import Coq.Lists.List Omega Psatz Coq.Bool.Bool.
Import ListNotations.
Require Import DFA QS.
Local Open Scope Z_scope.

Module QSLowerBound (dfa : DFA).

Include QSUtils dfa.

(* the queueing system is lower bounded if all of its generated sequences of events respect the number
  of minimum items in the buffer *)
Definition lower_bounded := forall w, generates w -> init_items + count_buffer w >= min_items.

(*
  We can construct a function f that gives the minimum number of items in the buffer in a given state following
 this constraints:
  -> f applied to the initial state gives a number less or equal to the number of initial items
  -> for every tangible state q, f applied to every transition starting from q through e gives a number less or
    equal to f applied to q plus count_event e
  --
  We shall now prove that this constraints are correct.
*)

(* The number of items counted from a given generated sequence of events must be greater or equal to f applied
  to its extended transition. *)
Lemma buffer_count_leq_f : forall f,
    ( f state0 <= init_items /\ forall q, In q states -> is_tangible q -> forall e, In e events ->
        f (transition q e) <= f q + count_event e )
    -> forall w, generates w -> init_items + count_buffer w >= f (ixtransition w).
Proof.
  intros f [H H0] w H10;
  induction w as [|e w' IH] using @rev_ind.
  - unfold ixtransition; simpl; omega.
  - pose H10 as H1; apply gen_prefix_closed in H1; fold generates in H1; pose H1 as H2;
      apply IH in H2.
    unfold ixtransition, count_buffer; rewrite ixtransition_distr, count_buffer_distr';
      fold ixtransition xtransition count_buffer.
    unfold generates in H1; remember (ixtransition w') as q eqn:H3.
    rewrite H3; simpl; rewrite <- H3.
    remember (transition q e) as q' eqn:H4.
    cut (f q' <= f q + count_event e).
    omega.
    rewrite H4.
    assert (H5: transition q e <> sink).
      unfold generates in H10; rewrite ixtransition_distr in H10;
      simpl in H10; rewrite <- H3 in H10; auto.
    apply (transition_correct) in H5.
    apply H0.
    2: split; auto; eexists; fold ixtransition; symmetry; apply H3.
    1-2: intuition.
Qed.

(*
  This lemma helps prove pumping_buffer.
  Every pumping sequence w1 ++ w2^n ++ w3 is such that:
  1 - count_buffer w2 >= 0 and count_buffer (w1 ++ w2^n ++ w3) >= count_buffer (w1 ++ w3)
  2 - count_buffer w2 < 0 and the queueing system is not lower bounded
*)
Lemma pumping_buffer1 q : forall w,
  lower_bounded -> ixtransition w = q -> q <> sink ->
  (length w >= length states)%nat ->
  exists w', ixtransition w' = q /\ (length w' < length w)%nat /\
  count_buffer w' <= count_buffer w.
Proof.
  intros w H H0 H1 H2;
  assert (H10: exists m, Z.of_nat m >= - (min_items - init_items - count_buffer w - 1)). {
    assert (H3: 0 >= (min_items - init_items - count_buffer w - 1)).
      unfold lower_bounded, generates in H; rewrite <- H0 in H1; apply H in H1; omega.
    assert (H4: 0 <= -(min_items - init_items - count_buffer w - 1)).
      omega.
    apply Z_of_nat_complete in H4; destruct H4 as [n2 H4];
    exists n2; omega.
  }
  destruct H10 as [m H10].
  apply pumping in H2;
  destruct H2 as [w1 [w2 [w3 [H2 [H3 [H20 H4]]]]]];
  fold ixtransition in H4;
  destruct (Z_ge_lt_dec (count_buffer w2) 0) as [H5|H5].
  - exists (w1++w3); repeat split.
    + rewrite <- H0; unfold ixtransition; specialize (H4 0%nat);
      simpl in H4; auto.
    + rewrite H2, app_length, app_length, app_length.
      assert (length w2 > 0)%nat.
        destruct w2; try contradiction; simpl; omega.
      omega.
    + rewrite H2, count_buffer_distr, count_buffer_distr, count_buffer_distr;
      omega.
  - assert (contra: init_items + count_buffer (w1 ++ w2^(S m) ++ w3) < min_items). {
      rewrite count_buffer_distr, count_buffer_distr;
      rewrite count_str_pow.
      replace (count_buffer w1 + (Z.of_nat (S m) * count_buffer w2 + count_buffer w3)) with
      (count_buffer w + Z.of_nat m * count_buffer w2).
      2: rewrite H2; rewrite count_buffer_distr, count_buffer_distr;
      rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.mul_add_distr_r; omega.
      nia.
    }
    assert (contra0: generates (w1 ++ w2^(S m) ++ w3)).
      unfold generates; fold ixtransition; rewrite H4, H0;
      auto.
    apply H in contra0. omega.
Qed.

(* If the queueing system is lower bounded, for every generated sequence of events w of length greater or equal
  to the number of states, exists a sequence of events that transition into ixtransition w and counts a number of
  items less or equal to count_buffer w. *)
Lemma pumping_buffer q : forall w,
  lower_bounded -> ixtransition w = q -> q <> sink ->
  (length w >= length states)%nat ->
  exists w', ixtransition w' = q /\ (length w' < length states)%nat /\
  count_buffer w' <= count_buffer w.
Proof.
  intro w; revert q;
  induction w as [|e w' IH] using @rev_ind; intros q H H0 H1 H2.
  - assert (length states > 0)%nat. {
      pose proof state0_correct. destruct states.
      destruct H3.
      simpl; omega.
    }
    simpl in H2; omega.
  - inversion H2.
    + eapply pumping_buffer1 in H.
      2: apply H0.
      2: auto.
      2: omega.
      rewrite <- H4 in H; apply H.
    + unfold ixtransition in H0; rewrite ixtransition_distr in H0;
        fold ixtransition xtransition in H0.
      pose H as H5;
      eapply IH in H5; clear IH.
      2: reflexivity.
      destruct H5 as [w0 [H6 [H7 H8]]].
      inversion H7.
      -- apply pumping_buffer1 with (q:=q) (w:=w0 ++ [e]) in H.
         destruct H as [w1 [H10 [H11 H12]]].
         exists w1. repeat split.
         auto.
         rewrite app_length in H11; simpl in H11; omega.
         assert (count_buffer (w0 ++ [e]) <= count_buffer (w' ++ [e])).
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

(* min_string q w is True if w counts the minimum items in q (minimum string) *)
Definition min_string q w :=
  ixtransition w = q /\ forall w', ixtransition w' = q -> count_buffer w' >= count_buffer w.

(* a function that takes w1 and w2 and returns the sequence that counts least items *)
Definition min w1 w2 :=
  if Z_ge_dec (count_buffer w1) (count_buffer w2) then w2 else w1.

(* a function that returns the sequence of (possible) events of a given list that counts least items *)
Fixpoint min_list (l:list (list B)) :=
  match l with
  | w::nil => w
  | w::l' => min w (min_list l')
  | nil => nil
  end.

(* Every sequence of (possible) events in l must count a number of items greater or equal to count_buffer (min_list l). *)
Lemma min_list_correct l : forall w,
  In w l -> count_buffer w >= count_buffer (min_list l).
Proof.
  intros w H.
  induction l as [|w' l' IH]; inversion H; simpl; unfold min.
  - destruct (Z_ge_dec (count_buffer w') (count_buffer (min_list l'))) as [H1|H1].
    + rewrite H0 in *; destruct l'; omega.
    + destruct l'; rewrite H0; intuition.
  - apply IH in H0; destruct (Z_ge_dec (count_buffer w') (count_buffer (min_list l')));
    destruct l'; try omega.
    inversion H. rewrite H1; omega. destruct H1.
Qed.

(* If all the sequences of events in l transitions into q, min_list l does to. *)
Lemma min_list_state l : forall q,
  l <> nil ->
  (forall w, In w l -> ixtransition w = q) ->
  ixtransition (min_list l) = q.
Proof.
  intros q H H0.
  induction l as [|w' l' IH].
  - contradiction.
  - destruct l' as [|w'' l'].
    + apply H0; intuition.
    + assert (H1: ixtransition (min_list (w'' :: l')) = q). {
        apply IH.
        intro contra; discriminate.
        intros w0 H1. apply H0. right; auto.
      }
      clear IH.
      simpl. simpl in H1. unfold min.
      destruct (Z_ge_dec (count_buffer w')
      (count_buffer match l' with | [] => w'' | _ :: _ =>
       if Z_ge_dec (count_buffer w'') (count_buffer (min_list l')) then min_list l'
       else w'' end)).
      * apply H1.
      * apply H0; left; auto.
Qed.

(* a function that returns the [(possible) event] of a given list that adds least items *)
Fixpoint min_in_list l :=
  match l with
  | e::nil => [e]
  | e::l' => min [e] (min_in_list l')
  | nil => nil
  end.

(* Every (possible) event in l must add a number of items greater or equal to count_buffer (min_in_list l). *)
Lemma min_in_list_correct l : forall e,
  In e l -> count_buffer [e] >= count_buffer (min_in_list l).
Proof.
  intros e H.
  induction l as [|e' l' IH]; inversion H; simpl; unfold min.
  - destruct (Z_ge_dec (count_buffer [e']) (count_buffer (min_in_list l'))) as [H1|H1].
    + rewrite H0 in *; destruct l'; simpl in *; omega.
    + apply Znot_ge_lt in H1; destruct l'; rewrite H0; simpl; omega.
  - apply IH in H0; destruct (Z_ge_dec (count_buffer [e']) (count_buffer (min_in_list l')));
    destruct l'; simpl in *; try omega.
    inversion H. rewrite H1; omega. destruct H1.
Qed.

(* count_buffer applied to the event that adds least items to the buffer *)
Definition min_count_event := count_buffer (min_in_list events).

(* Every event must add a number of items greater or equal to min_count_event. *)
Lemma min_count_event_correct : forall e,
  In e events -> count_event e >= min_count_event.
Proof.
  intros e H.
  replace (count_event e) with (count_buffer [e]).
  apply min_in_list_correct; auto.
  simpl; omega.
Qed.

(* a function that returns the generated sequence of events w of length less than the number of states
  such that w transitions into q and adds least items *)
Definition min_gen_strings q := min_list (all_gen_strings_le q (length states - 1)).

(* If the queueing system is lower bounded, every tangible state q is lower bounded. min_gen_strings q must
  count the minimum items in q. *)
Lemma min_gen_strings_correct q :
  lower_bounded -> is_tangible q ->
  min_string q (min_gen_strings q).
Proof.
  intros H H0.
  unfold min_string.
  split; unfold min_gen_strings.
  - apply min_list_state.
    + apply tangible_length in H0; destruct H0 as [w [H0 [H1 H2]]]; fold ixtransition in H0.
      eapply all_gen_strings_le_generated with (n:=(length states - 1)%nat) in H2.
      2: apply H0.
      2: omega.
      intro contra; rewrite contra in H2; destruct H2.
    + intros w H1; unfold all_gen_strings_le in H1;
      eapply gen_strings_correct. apply H1.
  - intros w H1;
    destruct H0 as [H0 H2];
    destruct (le_gt_dec (length w) (length states - 1)).
    + apply min_list_correct, all_gen_strings_le_generated; auto.
    + assert (H3: (length w >= length states)%nat). omega.
      eapply pumping_buffer with (q:=q) in H3.
      2-4: auto.
      destruct H3 as [w' [H3 [H4 H5]]].
      assert (count_buffer w' >= count_buffer (min_list (all_gen_strings_le q (length states - 1)))).
        apply min_list_correct, all_gen_strings_le_generated; auto; omega.
      omega.
Qed.

(* The initial state's minimum string does not remove items from the buffer if the queueing system is bounded. *)
Lemma min_string_state0 : forall w,
  lower_bounded ->
  min_string state0 w ->
  count_buffer w = 0.
Proof.
  intros w H H0.
  destruct H0 as [H0 H3];
  destruct (count_buffer w) eqn:H1.
  - auto.
  - pose proof (Zgt_pos_0 p) as H2; rewrite <- H1 in H2;
    clear H0; assert (H0: ixtransition [] = state0). auto.
    apply H3 in H0; simpl in H0;
    omega.
  - pose proof (Zlt_neg_0 p) as H2; rewrite <- H1 in H2, H3;
    clear H1; pose H0 as H1; apply state0_cycle with (n:=2%nat) in H1;
    apply H3 in H1; unfold count_buffer in H1; rewrite count_str_pow in H1; fold count_buffer in H1;
    nia.
Qed.

(* a lemma related to the second constraint of the function f *)
Lemma min_string_transition : forall q e qe w we,
  transition q e = qe -> qe <> sink ->
  min_string q w -> min_string qe we ->
  count_buffer we <= count_buffer w + count_event e.
Proof.
  intros q e qe w we H H0 H1 H2.
  assert (count_buffer (w ++ [e]) = count_buffer w + count_event e). apply count_buffer_distr'.
  assert (count_buffer we <= count_buffer (w ++ [e])).
  destruct H2 as [H2 H4]; destruct H1 as [H1 H5];
  unfold ixtransition in *; apply Z.ge_le_iff; apply H4;
  rewrite ixtransition_distr; unfold ixtransition; rewrite H1; simpl; auto.
  omega.
Qed.

(* Now we prove that f exists and, for every tangible state q, f q must be greater than min_items iff
  the queueing system is correctly lower bounded. *)
Theorem iff_exists_function__upper_bounded :
  ( exists f, f state0 <= init_items /\ forall q, In q states -> is_tangible q -> f q >= min_items /\
    forall e, In e events -> f (transition q e) <= f q + count_event e )
  <-> lower_bounded.
Proof.
  split.

  - unfold lower_bounded; intros [ f [H H0] ] w H1.
    cut (init_items + count_buffer w >= f (ixtransition w)).
    cut (f (ixtransition w) >= min_items).
    omega.
    apply H0.
    apply ixtransition_in_states; fold ixtransition; apply H1.
    split; try intuition; eexists; fold ixtransition; reflexivity.
    apply buffer_count_leq_f; try split; try (apply H0); intuition.

  - intro H.
    exists (fun q => if A_eq_dec q sink then (min_items)+(min_count_event) else (init_items) + count_buffer (min_gen_strings q)).
    split.
    + destruct (A_eq_dec state0 sink) as [H2|H2].
      destruct sink_correct as [_ [contra _]]; symmetry in H2; contradiction.
      assert (H1: is_tangible state0). split. auto. exists []; auto.
      apply min_string_state0 with (w:=min_gen_strings state0) in H.
      omega.
      apply min_gen_strings_correct; auto.
    + intros q H0 H4; pose H4 as H1; destruct H1 as [H1 [w H2]].
      destruct (A_eq_dec q sink) as [H3|_]. contradiction.
      assert (H5: generates (min_gen_strings q)). {
          apply (min_gen_strings_correct q) in H. 2: auto.
          destruct H as [H _]; unfold generates; rewrite H; auto.
      }
      split.
      * apply H; auto.
      * intros e H3;
        destruct (A_eq_dec (transition q e) sink).
        apply min_count_event_correct in H3.
        assert (init_items + count_buffer (min_gen_strings q) >= min_items). auto.
        omega.
        assert (count_buffer (min_gen_strings (transition q e)) <= count_buffer (min_gen_strings q) + count_event e). {
          apply min_string_transition with (q:=q)(qe:=transition q e); auto.
          1,2: apply min_gen_strings_correct; auto.
          split. auto.
          exists (w ++ [e]); rewrite ixtransition_distr, H2; auto.
        }
        omega.
Qed.

End QSLowerBound.
