Require Import List Lia Pigeonhole.
Import ListNotations.

(*
  A DIrected GRAPH is a set of edges connecting two vertices.
  Here we consider invalid graphs with disconnected vertices, i.e. graphs holding vertices that are
  not connected to any vertex by an edge.
*)

Inductive digraph_component {X} :=
  | edge (v1 v2 : X).

Definition digraph {X} := list (@digraph_component X).

(* Lists the vertices of g. *)
Fixpoint vertices {X} (g:@digraph X) :=
  match g with
  | edge v1 v2::g => v1::v2::vertices g
  | nil => nil
  end.

(* v is a vertex of g iff there exists an edge connecting it to a vertex or vice versa. *)
Lemma vertex_edge {X} (g:@digraph X) v :
  In v (vertices g) <-> exists v2, In (edge v v2) g \/ In (edge v2 v) g.
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

(* v2 is said to be a neighbor of v1 if there exists an edge connecting v1 to it. *)
Definition neighbor {X} (g:@digraph X) v1 v2 := In (edge v1 v2) g.

(* Decidable equality *)
Definition eq_dec {X} := forall x1 x2 : X, {x1 = x2} + {x1 <> x2}.

(* Lists all the neighbors of v. *)
Fixpoint neighbors {X} (P:eq_dec) (g:@digraph X) v :=
  match g with
  | edge v1 v2::g =>
    if P v v1 then
      v2::neighbors P g v
    else
      neighbors P g v
  | nil => nil
  end.

(* v2 is in (neighbors eq_decH g v1) iff it is a neighbor of v1. *)
Lemma neighbor_in_neighbors {X} eq_decH (g:@digraph X) v1 v2 :
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

(*
  A path is a sequence of vertices (v1, v2, ..., vn) such that v1 is connected to v2, v2 is
  connected to v3, and so on.
*)
Inductive path {X} : digraph->list X->Prop :=
  | no_move g v1 v2 : neighbor g v1 v2 \/ neighbor g v2 v1 -> path g [v1]
  | new_move g v1 v2 p : neighbor g v1 v2 -> path g (v1::p)
      -> path g (v2::v1::p).

(* (v1, ..., vm, ..., vn) is a path iff (v1, ..., vm) and (vm, ..., vn) are also paths. *)
Lemma path_app {X} (g:@digraph X) p1 p2 v :
  path g (p1 ++ [v] ++ p2) <-> path g (p1 ++ [v]) /\ path g ([v] ++ p2).
Proof.
  revert p2 v; induction p1 as [|v1 p1 IH]; intros p2 v; split; intro H.
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

(*
  We can define a reversed definition: a path (vn, ..., v2, v1) is a sequence of vertices
  such that v2 is connected to v1, v3 is connected to v2, and so on.
*)
Lemma path_rev {X} (g:@digraph X) p v1 v2 :
  path g ((p ++ [v1]) ++ [v2]) <-> path g (p ++ [v1]) /\ neighbor g v2 v1.
Proof.
  split; intro H.
  - rewrite <- app_assoc in H; apply path_app in H;
    destruct H as [H H0]; inversion H0; subst; intuition.
  - rewrite <- app_assoc; apply path_app; split;
    try (apply new_move); try (apply no_move with v1); intuition.
Qed.

(* All elements of a path are vertices. *)
Lemma path_vertices {X} (g:@digraph X) p :
  forall v, path g p -> In v p -> In v (vertices g).
Proof.
  intros v H H0.
  apply vertex_edge.
  induction H; unfold neighbor in *.
  - destruct H0 as [H0|[]]; subst; exists v2; auto.
  - inversion H0; subst.
    + exists v1; auto.
    + apply IHpath, H2.
Qed.

(*
  If a path between v1 and v2 exists, there is a path between them such that its length is less or
  equal to the number of vertices in the graph plus one.
*)
Lemma minor_path {X} (eq_decH:@eq_dec X) (g:@digraph X) p v1 v2 :
  path g ([v1] ++ p ++ [v2]) -> exists p', path g ([v1] ++ p' ++ [v2]) /\ length ([v1] ++ p' ++ [v2]) <= S (length (vertices g)).
Proof.
  assert (P: forall X (eq_decH:@eq_dec X) (g:@digraph X) p v1 v2,
  path g ([v1] ++ p ++ [v2]) -> length ([v1] ++ p ++ [v2]) > S (length (vertices g)) ->
  exists p', path g ([v1] ++ p' ++ [v2]) /\ length ([v1] ++ p' ++ [v2]) < length ([v1] ++ p ++ [v2])). {
    clear v1 v2 p g eq_decH X; intros X eq_decH g p v1 v2 H H0.
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
  }
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
    + apply P in H.
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
        apply P in H5.
        2: apply eq_decH.
        2: rewrite app_length; simpl; nia.
        destruct H5 as [p'' [H5 H7]]; exists p''; split.
        auto.
        simpl; rewrite app_length, app_length; rewrite app_length, app_length in H7; simpl in H7; nia.
      * exists (v::p'); split.
        apply new_move; auto.
        rewrite app_length; rewrite app_length in H4; simpl in *; nia.
Qed.

(*
  A vertex is said to be reachable from another if there is path between them.
*)

Inductive reachable {X} : digraph->X->X->Prop :=
  | reach_neigh g v1 v2 : neighbor g v1 v2 -> reachable g v1 v2
  | reach_trans g v1 v2 v3 :
    reachable g v1 v2 -> reachable g v2 v3 -> reachable g v1 v3.

Inductive reachable' {X} : digraph->X->X->Prop :=
  | reach'_neigh g v1 v2 : neighbor g v1 v2 -> reachable' g v1 v2
  | reach'_ind g v1 v2 v3 :
    reachable' g v1 v2 -> neighbor g v2 v3 -> reachable' g v1 v3.

(* Both definitions are equivalent. *)
Lemma reachable'_correct {X} (g:@digraph X) v1 v2:
  reachable' g v1 v2 <-> reachable g v1 v2.
Proof.
  split; intro H; induction H.
  - apply reach_neigh; auto.
  - apply reach_trans with v2.
    auto.
    apply reach_neigh; auto.
  - apply reach'_neigh; auto.
  - assert (H1: forall v1 v2 v3, reachable' g v1 v2 -> reachable' g v2 v3 -> reachable' g v1 v3). {
      clear IHreachable1 IHreachable2 H H0 v1 v2 v3.
      intros v1 v2 v3 H H0.
      induction H0.
      - apply reach'_ind with v0; auto.
      - apply reach'_ind with v2.
        + apply IHreachable'; auto.
        + auto.
    }
    apply H1 with v2; auto.
Qed.

(* Proof the definitions are correct. *)
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
      apply reach'_neigh; auto.
    + inversion H; subst;
      apply IH in H5;
      apply reach'_ind with v3; auto.
Qed.

(*
  DFS: Depth-First Search
  A algorithm that searches all reachable vertices from one in a depth-first manner.
  It halts based on a maximum depth.
*)

Fixpoint dfs_loop {X} (f:X->list X) (l:list X) :=
  match l with
  | v::l => f v ++ (dfs_loop f l)
  | nil => nil
  end.

Fixpoint dfs {X} (P:eq_dec) (g:@digraph X) h v :=
  neighbors P g v ++
    (match h with
    | S h => dfs_loop (dfs P g h) (neighbors P g v)
    | O => nil
    end).

(* v2 is in the list returned by the DFS iff there exists a path ending with v2. *)
Lemma dfs_path {X} (eq_decH:@eq_dec X) g h v1 v2 :
  In v2 (dfs eq_decH g h v1) <-> exists p, path g (v2::p ++ [v1]) /\ length p <= h.
Proof.
  assert (P: forall X f (l:list X) v1, In v1 (dfs_loop f l) <-> exists v2, In v2 l /\ In v1 (f v2)). {
    clear eq_decH g X v1 v2; intros X f l v1; split; intro H.
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
  }
  split.
  - revert v1 v2; induction h as [|h IH]; intros v1 v2 H.
    + exists nil; split.
      * simpl in H; rewrite app_nil_r in H; apply new_move.
        apply neighbor_in_neighbors in H; auto.
        apply no_move with v2; left; apply neighbor_in_neighbors in H; auto.
      * simpl; nia.
    + simpl in H; apply in_app_or in H; destruct H as [H|H].
      * exists nil; split.
        2: simpl; nia.
        apply new_move.
        apply neighbor_in_neighbors in H; auto.
        apply no_move with v2; left; apply neighbor_in_neighbors in H; auto.
      * apply P in H; destruct H as [v3 [H H0]];
        apply IH in H0; destruct H0 as [p [H0 H1]];
        exists (p ++ [v3]); split.
        2: rewrite app_length; simpl; nia.
        replace (v2 :: (p ++ [v3]) ++ [v1]) with (((v2 :: p) ++ [v3]) ++ [v1]).
        2: auto.
        apply path_rev; split; try (apply neighbor_in_neighbors in H); auto.
  - revert v1 v2; induction h as [|h IH]; intros v1 v2 H.
    + simpl; rewrite app_nil_r; apply neighbor_in_neighbors;
      destruct H as [p [H H0]]; destruct p.
      * inversion H; subst; auto.
      * simpl in H0; nia.
    + simpl; apply in_or_app; destruct H as [p [H H0]]; destruct p as [|v p _] using @rev_ind.
      * left; apply neighbor_in_neighbors; inversion H; subst; auto.
      * replace (v2 :: (p ++ [v]) ++ [v1]) with (((v2 :: p) ++ [v]) ++ [v1]) in H.
        2: auto.
        apply path_rev in H; destruct H as [H H1];
        right; apply P; exists v; split.
        apply neighbor_in_neighbors; auto.
        apply IH; exists p; split.
        auto.
        rewrite app_length in H0; simpl in H0; nia.
Qed.

(*
  v2 is reachable from v1 iff it is in the DFS applied to v1 and maximum depth equal to the number
  of vertices in the graph.
*)
Lemma dfs_reachable {X} (eq_decH:@eq_dec X) g v1 v2 :
  reachable g v1 v2 <-> In v2 (dfs eq_decH g (length (vertices g)) v1).
Proof.
  split; intro H.
  - apply dfs_path; apply reachable_path in H; destruct H as [p' H].
    apply minor_path in H; auto; destruct H as [p [H H0]];
    exists p; split.
    auto.
    rewrite app_length, app_length in H0; simpl in H0;
    nia.
  - apply dfs_path in H; destruct H as [p [H _]];
    apply reachable_path; exists p; auto.
Qed.

(* Decidability of reachable vertex *)
Theorem reachable_dec {X} (eq_decH:@eq_dec X) (g:@digraph X) v1 v2 :
  {reachable g v1 v2} + {~ reachable g v1 v2}.
Proof.
  destruct (in_dec eq_decH v2 (dfs eq_decH g (length (vertices g)) v1)) as [H|H].
  - left; apply dfs_reachable in H; auto.
  - right; intro H0; assert (In v2 (dfs eq_decH g (length (vertices g)) v1)).
    apply dfs_reachable; auto.
    contradiction.
Qed.