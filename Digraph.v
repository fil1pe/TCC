Require Import List Lia Pigeonhole.
Import ListNotations.

Definition eq_dec {X} := forall x1 x2 : X, {x1 = x2} + {x1 <> x2}.

Inductive digraph_component {X} :=
  | edge (v1 v2 : X).

Definition digraph {X} := list (@digraph_component X).

Fixpoint vertices {X} (g:@digraph X) :=
  match g with
  | edge v1 v2::g => v1::v2::vertices g
  | nil => nil
  end.

Lemma vertices_correct {X} (g:@digraph X) v1 :
  In v1 (vertices g) <-> exists v2, In (edge v1 v2) g \/ In (edge v2 v1) g.
Proof.
  split; intro H; induction g as [|[v3 v4] g IH].
  - inversion H.
  - repeat (destruct H as [H|H]); subst.
    + exists v4; left; left; auto.
    + exists v3; right; left; auto.
    + apply IH in H; destruct H as [v2 [H|H]]; exists v2; intuition.
  - destruct H as [v2 [[]|[]]].
  - destruct H as [v2 [[H|H0]|[H|H0]]].
    + injection H; intros; subst; left; auto.
    + right; right; apply IH; exists v2; auto.
    + injection H; intros; subst; simpl; auto.
    + right; right; apply IH; exists v2; auto.
Qed.

Definition neighbor {X} (g:@digraph X) v1 v2 := In (edge v1 v2) g.

Fixpoint neighbors {X} (H:eq_dec) (g:@digraph X) v :=
  match g with
  | edge v1 v2::g =>
    if H v v1 then
      v2::neighbors H g v
    else
      neighbors H g v
  | nil => nil
  end.

Lemma neighbors_correct {X} eq_decH (g:@digraph X) v1 v2 :
  neighbor g v1 v2 <-> In v2 (neighbors eq_decH g v1).
Proof.
  unfold neighbor; split; intro H; induction g as [|e g IH].
  1,3: inversion H.
  - destruct e as [v3 v4]; simpl; destruct (eq_decH v1 v3) eqn:H0.
    + subst; inversion H; subst.
      * injection H1; intros; subst; simpl; auto.
      * right; apply IH; auto.
    + apply IH; inversion H; subst.
      * injection H1; intros; subst; contradiction.
      * auto.
  - destruct e as [v3 v4]; simpl in H; destruct (eq_decH v1 v3) eqn:H0.
    + subst; destruct H as [H|H]; subst.
      * left; auto.
      * right; apply IH; auto.
    + right; apply IH; auto.
Qed.

Inductive path {X} : digraph->list X->Prop :=
  | no_move g v1 v2 : neighbor g v1 v2 \/ neighbor g v2 v1 -> path g [v1]
  | new_move g v1 v2 p : neighbor g v1 v2 -> path g (v1::p)
      -> path g (v2::v1::p).

Lemma path_app {X} (g:@digraph X) p1 p2 v :
  path g (p1 ++ [v] ++ p2) <-> path g (p1 ++ [v]) /\ path g ([v] ++ p2).
Proof.
  revert p2 v.
  induction p1 as [|v1 p1 IH]; intros p2 v; split; intro H.
  - destruct p2 as [|v2 p2].
    + intuition.
    + inversion H; subst; split; try (apply no_move with v2); intuition.
  - intuition.
  - destruct p1 as [|v2 p1]; inversion H; subst.
    + split.
      apply new_move. auto. apply no_move with v1; intuition.
      auto.
    + apply IH in H5; split; try (apply new_move); intuition.
  - destruct H as [H H0]; destruct p1 as [|v2 p1]; inversion H; subst.
    + apply new_move; auto.
    + assert (H1: path g ((v2 :: p1) ++ [v]) /\ path g ([v] ++ p2)). intuition.
      apply IH in H1; apply new_move; auto.
Qed.

Lemma path_rev {X} (g:@digraph X) p v1 v2 :
  path g ((p ++ [v1]) ++ [v2]) <-> path g (p ++ [v1]) /\ neighbor g v2 v1.
Proof.
  split; intro H.
  - rewrite <- app_assoc in H; apply path_app in H;
    destruct H as [H H0]; inversion H0; subst; intuition.
  - rewrite <- app_assoc; apply path_app; split; try (apply new_move); try (apply no_move with v1); intuition.
Qed.

Lemma path_vertices {X} (g:@digraph X) p :
  forall v, path g p -> In v p -> In v (vertices g).
Proof.
  intros v H H0.
  apply vertices_correct.
  induction H; unfold neighbor in *.
  - destruct H0 as [H0|[]]; subst; exists v2; auto.
  - inversion H0; subst.
    + exists v1; auto.
    + apply IHpath, H2.
Qed.

Lemma path_pumping' {X} (eq_decH:@eq_dec X) (g:@digraph X) p v1 v2 :
  path g ([v1] ++ p ++ [v2]) -> length ([v1] ++ p ++ [v2]) > S (length (vertices g)) ->
  exists p', path g ([v1] ++ p' ++ [v2]) /\ length ([v1] ++ p' ++ [v2]) < length ([v1] ++ p ++ [v2]).
Proof.
  intros H H0.
  assert (H1: forall x, In x (p ++ [v2]) -> In x (vertices g)). {
    intros x H1; apply path_vertices with (p ++ [v2]).
    2: auto.
    destruct p; inversion H; subst.
    - apply no_move with v1; intuition.
    - auto.
  }
  apply pigeonhole in H1.
  2: apply eq_decH.
  2: rewrite app_length; repeat (rewrite app_length in H0); simpl in *; nia.
  destruct H1 as [p1 [p2 [p3 [v H1]]]];
  destruct p3 as [|v' p3 _] using @rev_ind.
  - replace (p1 ++ [v] ++ p2 ++ [v] ++ []) with ((p1 ++ [v] ++ p2) ++ [v]) in H1.
    2: repeat (rewrite <- app_assoc); auto.
    apply app_inj_tail in H1; destruct H1 as [H1 H2]; subst.
    exists p1; split.
    + replace ([v1] ++ (p1 ++ [v] ++ p2) ++ [v]) with ((v1::p1) ++ [v] ++ (p2 ++ [v])) in H.
      2: repeat (rewrite <- app_assoc); auto.
      apply path_app in H; intuition.
    + repeat (rewrite app_length); simpl; nia.
  - exists (p1 ++ [v] ++ p3); split.
    + replace (p1 ++ [v] ++ p2 ++ [v] ++ p3 ++ [v']) with ((p1 ++ [v] ++ p2 ++ [v] ++ p3) ++ [v']) in H1.
      2: repeat (rewrite <- app_assoc); auto.
      apply app_inj_tail in H1; destruct H1 as [H1 H2]; subst.
      replace ([v1] ++ (p1 ++ [v] ++ p3) ++ [v']) with ((v1::p1) ++ [v] ++ (p3 ++ [v'])).
      2: repeat (rewrite <- app_assoc); auto.
      apply path_app; split.
      * replace ([v1] ++ (p1 ++ [v] ++ p2 ++ [v] ++ p3) ++ [v']) with ((v1::p1) ++ [v] ++ (p2 ++ [v] ++ p3 ++ [v'])) in H.
        2: repeat (rewrite <- app_assoc); auto.
        apply path_app in H; intuition.
      * replace ([v1] ++ (p1 ++ [v] ++ p2 ++ [v] ++ p3) ++ [v']) with (([v1] ++ p1 ++ [v] ++ p2) ++ [v] ++ (p3 ++ [v'])) in H.
        2: repeat (rewrite <- app_assoc); auto.
        apply path_app in H; intuition.
    + rewrite H1; repeat (rewrite app_length); simpl; nia.
Qed.

Lemma path_pumping {X} (eq_decH:@eq_dec X) (g:@digraph X) p v1 v2 :
  path g ([v1] ++ p ++ [v2]) -> exists p', path g ([v1] ++ p' ++ [v2]) /\ length ([v1] ++ p' ++ [v2]) <= S (length (vertices g)).
Proof.
  intro H;
  destruct (Compare_dec.gt_dec (length ([v1] ++ p ++ [v2])) (S (length (vertices g)))) as [H0|H0].
  2: exists p; split; auto; nia.
  generalize dependent v2;
  generalize dependent v1;
  induction p as [|v p IH]; intros v1 v2 H H0.
  - assert (H1: forall v, In v [v1; v2] -> In v (vertices g)).
    intros v H1; apply path_vertices with [v1; v2]; auto.
    destruct (vertices g) as [|v3 [|v4 l]].
    + specialize (H1 v1); destruct H1; left; auto.
    + assert (v3 = v1). {
        specialize (H1 v1); destruct H1.
        - left; auto.
        - auto.
        - inversion H1.
      }
      assert (v3 = v2). {
        specialize (H1 v2); destruct H1.
        - right; left; auto.
        - auto.
        - inversion H1.
      }
      subst; exists nil; split; auto.
    + exists nil; split.
      * auto.
      * simpl; nia.
  - remember ([v1] ++ (v :: p) ++ [v2]); inversion H0; subst.
    + apply path_pumping' in H.
      2: apply eq_decH.
      2: rewrite app_length, app_length; rewrite app_length, app_length in H0; auto.
      destruct H as [p' [H H1]]; exists p'; split.
      * auto.
      * rewrite app_length, app_length;
        rewrite app_length, app_length in H2;
        rewrite app_length, app_length, app_length, app_length in H1;
        simpl in *; nia.
    + inversion H; subst; apply IH in H8.
      2: simpl in *; rewrite app_length; rewrite app_length in H0, H1; simpl in *; nia.
      destruct H8 as [p' [H8 H9]];
      inversion H9; subst; simpl in *.
      * rewrite app_length in H0, H1, H4, H9; simpl in *.
        assert (H5: path g ([v1] ++ (v :: p') ++ [v2])). apply new_move; auto.
        apply path_pumping' in H5.
        2: apply eq_decH.
        2: rewrite app_length, app_length; simpl; nia.
        destruct H5 as [p'' [H5 H7]]; exists p''; split.
        auto.
        rewrite app_length, app_length; rewrite app_length, app_length, app_length, app_length in H7; simpl in *; nia.
      * exists (v::p'); split.
        apply new_move; auto.
        rewrite app_length; rewrite app_length in H4; simpl in *; nia.
Qed.

Inductive reachable {X} : digraph->X->X->Prop :=
  | reach_neigh g v1 v2 : neighbor g v1 v2 -> reachable g v1 v2
  | reach_trans g v1 v2 v3 :
    reachable g v1 v2 -> reachable g v2 v3 -> reachable g v1 v3.

Inductive reachable' {X} : digraph->X->X->Prop :=
  | reach_neigh' g v1 v2 : neighbor g v1 v2 -> reachable' g v1 v2
  | reach_trans' g v1 v2 v3 :
    reachable' g v1 v2 -> neighbor g v2 v3 -> reachable' g v1 v3.

Lemma reachable'_correct {X} (g:@digraph X) v1 v2:
  reachable' g v1 v2 <-> reachable g v1 v2.
Proof.
  split; intro H; induction H.
  - apply reach_neigh; auto.
  - apply reach_trans with v2.
    auto.
    apply reach_neigh; auto.
  - apply reach_neigh'; auto.
  - assert (H1: forall v1 v2 v3, reachable' g v1 v2 -> reachable' g v2 v3 -> reachable' g v1 v3). {
      clear IHreachable1 IHreachable2 H H0 v1 v2 v3.
      intros v1 v2 v3 H H0.
      induction H0.
      - apply reach_trans' with v0; auto.
      - apply reach_trans' with v2.
        + apply IHreachable'; auto.
        + auto.
    }
    apply H1 with v2; auto.
Qed.

Lemma reachable_path {X} (g:@digraph X) v1 v2 :
  reachable g v1 v2 <-> exists p, path g (v2::p ++ [v1]).
Proof.
  split; intro H.
  - apply reachable'_correct in H; induction H.
    + exists nil; apply new_move.
      auto.
      apply no_move with v2; auto.
    + destruct IHreachable' as [p IH];
      exists (v2::p); apply new_move; auto.
  - apply reachable'_correct; destruct H as [p H]; revert H; revert v2; induction p as [|v3 p IH]; intros v2 H.
    + inversion H; subst;
      apply reach_neigh'; auto.
    + inversion H; subst;
      apply IH in H5;
      apply reach_trans' with v3; auto.
Qed.

Fixpoint loop {X} (f:X->list X) (l:list X) :=
  match l with
  | v::l => f v ++ (loop f l)
  | nil => nil
  end.

Lemma loop_correct {X} f (l:list X) v1 :
  In v1 (loop f l) <-> exists v2, In v2 l /\ In v1 (f v2).
Proof.
  split; intro H.
  - induction l as [|v l IH].
    + inversion H.
    + simpl in H; apply in_app_or in H; destruct H.
      * exists v; split; try left; auto.
      * apply IH in H; destruct H as [v2 [H H0]];
        exists v2; split; try right; auto.
  - destruct H as [v2 [H H0]].
    induction l as [|v l IH].
    + inversion H.
    + simpl; apply in_or_app; inversion H; subst.
      * left; auto.
      * right; apply IH; auto.
Qed.

Fixpoint dfs {X} (H:eq_dec) (g:@digraph X) h v :=
  neighbors H g v ++
    (match h with
    | S h => loop (dfs H g h) (neighbors H g v)
    | O => nil
    end).

Lemma dfs_trans {X} (eq_decH:@eq_dec X) g h v1 v2 :
  In v2 (dfs eq_decH g h v1) -> In v2 (dfs eq_decH g (S h) v1).
Proof.
  revert v1 v2.
  induction h as [|h IH]; intros v1 v2 H.
  - simpl; simpl in H;
    rewrite app_nil_r in H;
    apply in_or_app; left; auto.
  - simpl in H; remember (S h) as Sh eqn:H0;
    simpl; apply in_app_or in H; apply in_or_app; destruct H as [H|H].
    + left; auto.
    + apply loop_correct in H; destruct H as [v3 [H H1]];
      right; apply loop_correct; exists v3; split; try (apply IH); auto.
Qed.

Lemma dfs_correct {X} (eq_decH:@eq_dec X) g h v1 v2 :
  In v2 (dfs eq_decH g h v1) <-> exists p, path g (v2::p ++ [v1]) /\ length p <= h.
Proof.
  split.
  - revert v1 v2; induction h as [|h IH]; intros v1 v2 H.
    + exists nil; split.
      * simpl in H; rewrite app_nil_r in H; apply new_move.
        apply neighbors_correct in H; auto.
        apply no_move with v2; left; apply neighbors_correct in H; auto.
      * simpl; nia.
    + simpl in H; apply in_app_or in H; destruct H as [H|H].
      * exists nil; split.
        --  apply new_move.
            apply neighbors_correct in H; auto.
            apply no_move with v2; left; apply neighbors_correct in H; auto.
        -- simpl; nia.
      * apply loop_correct in H; destruct H as [v3 [H H0]];
        apply IH in H0; destruct H0 as [p [H0 H1]];
        exists (p ++ [v3]); split.
        --  replace (v2 :: (p ++ [v3]) ++ [v1]) with (((v2 :: p) ++ [v3]) ++ [v1]).
            2: auto.
            apply path_rev; split; try (apply neighbors_correct in H); auto.
        -- rewrite app_length; simpl; nia.
  - revert v1 v2; induction h as [|h IH]; intros v1 v2 H.
    + simpl; rewrite app_nil_r; apply neighbors_correct;
      destruct H as [p [H H0]]; destruct p.
      * inversion H; subst; auto.
      * simpl in H0; nia.
    + simpl; apply in_or_app; destruct H as [p [H H0]]; destruct p as [|v p _] using @rev_ind.
      * left; apply neighbors_correct; inversion H; subst; auto.
      * replace (v2 :: (p ++ [v]) ++ [v1]) with (((v2 :: p) ++ [v]) ++ [v1]) in H.
        2: auto.
        apply path_rev in H; destruct H as [H H1];
        right; apply loop_correct; exists v; split.
        --  apply neighbors_correct; auto.
        --  apply IH; exists p; split.
            auto.
            rewrite app_length in H0; simpl in H0; nia.
Qed.

Lemma dfs_reachable {X} (eq_decH:@eq_dec X) g v1 v2 :
  reachable g v1 v2 <-> In v2 (dfs eq_decH g (length (vertices g)) v1).
Proof.
  split; intro H.
  - apply dfs_correct; apply reachable_path in H; destruct H as [p' H].
    apply path_pumping in H; auto; destruct H as [p [H H0]];
    exists p; split.
    auto.
    rewrite app_length, app_length in H0; simpl in H0;
    nia.
  - apply dfs_correct in H; destruct H as [p [H _]];
    apply reachable_path; exists p; auto.
Qed.

Theorem reachable_dec {X} (eq_decH:@eq_dec X) (g:@digraph X) :
  forall v1 v2, {reachable g v1 v2} + {~ reachable g v1 v2}.
Proof.
  intros v1 v2.
  destruct (in_dec eq_decH v2 (dfs eq_decH g (length (vertices g)) v1)) as [H|H].
  - left; apply dfs_reachable in H; auto.
  - right; intro H0; assert (In v2 (dfs eq_decH g (length (vertices g)) v1)).
    apply dfs_reachable; auto.
    contradiction.
Qed.