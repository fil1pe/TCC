Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import DFA.

Require Export Arith_base.
Require Import BinPos BinInt BinNat Pnat Nnat.
Require Import Omega.
Local Open Scope Z_scope.

Inductive events {E : Type} : Type :=
  | add
  | rem
  | other (e : E).

Fixpoint buffer_count {E : Type} (w : list (@events E)) : Z :=
  match w with
  | [] => 0
  | add::w' => buffer_count w' + 1
  | rem::w' => buffer_count w' - 1
  | _::w' => buffer_count w'
  end.

Definition upper_bound {Q E : Type} (g : dfa Q (@events E)) (n : Z) :=
  forall w, w ==> g -> buffer_count w <= n.

Lemma buffer_add: forall (E : Type) (w : list (@events E)),
  buffer_count (w ++ [add]) = buffer_count w + 1.
Proof.
  intros E w.
  induction w as [|e w IH].
  - reflexivity.
  - simpl. rewrite IH. destruct e.
    + reflexivity.
    + omega.
    + omega.
Qed.

Lemma buffer_rem: forall (E : Type) (w : list (@events E)),
  buffer_count (w ++ [rem]) = buffer_count w - 1.
Proof.
  intros E w.
  induction w as [|e w IH].
  - reflexivity.
  - simpl. rewrite IH. destruct e.
    + omega.
    + reflexivity.
    + omega.
Qed.

Lemma buffer_other: forall (E : Type) (w : list (@events E)) (e : E),
  buffer_count (w ++ [other e]) = buffer_count w.
Proof.
  intros E w c.
  induction w as [|e w IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma extended_delta__delta: forall (Q E : Type) (g : dfa Q E) (q : Q) (e : E),
  extended_delta g (state q) [e] = g.(delta) q e.
Proof.
  intros Q E g q e.
  simpl.
  destruct (delta g q e).
  - reflexivity.
  - reflexivity.
Qed.

Lemma buffer_count_leq_f:
  forall (Q E : Type) (g : dfa Q (@events E)) (f : @states Q->Z),
    (f(state g.(initial_state)) = 0 /\
      forall (q : Q),
        f(g.(delta) q add) >= f(state q) + 1 /\
        f(g.(delta) q rem) >= f(state q) - 1 /\
        (forall (e : E), f(g.(delta) q (other e)) >= f(state q))
    ) -> (forall w, w ==> g -> buffer_count w <= f (extended_delta g (state g.(initial_state)) w)).
Proof.
  intros Q E g f H0 w H2.
  destruct H0 as [H0 H1].
  induction w as [|e w IHw] using @rev_ind.
  - simpl. omega.
  - simpl. destruct e.
    + rewrite buffer_add.
      assert (H3 : w ==> g).
      { apply prefix_closed in H2. apply H2. }
      apply IHw in H3.
      assert (f (extended_delta g (state (initial_state g)) (w)) + 1 <= f (extended_delta g (state (initial_state g)) (w ++ [add]))).
      { rewrite dist_extended_delta. remember (extended_delta g (state (initial_state g)) w) as q eqn:eq_q. destruct q.
        - apply prefix_closed in H2. unfold in_language in H2. unfold not in H2. symmetry in eq_q. apply H2 in eq_q.
          destruct eq_q.
        - rewrite extended_delta__delta. assert (f (delta g q add) >= f (state q) + 1).
          { apply H1. }
          omega. }
      omega.
    + rewrite buffer_rem.
      assert (H3 : w ==> g).
      { apply prefix_closed in H2. apply H2. }
      apply IHw in H3.
      assert (f (extended_delta g (state (initial_state g)) (w)) - 1 <= f (extended_delta g (state (initial_state g)) (w ++ [rem]))).
      { rewrite dist_extended_delta. remember (extended_delta g (state (initial_state g)) w) as q eqn:eq_q. destruct q.
        - apply prefix_closed in H2. unfold in_language in H2. unfold not in H2. symmetry in eq_q. apply H2 in eq_q.
          destruct eq_q.
        - rewrite extended_delta__delta. assert (f (delta g q rem) >= f (state q) - 1).
          { apply H1. }
          omega. }
      omega.
    + rewrite buffer_other.
      assert (H3 : w ==> g).
      { apply prefix_closed in H2. apply H2. }
      apply IHw in H3.
      assert (f (extended_delta g (state (initial_state g)) (w)) <= f (extended_delta g (state (initial_state g)) (w ++ [other e]))).
      { rewrite dist_extended_delta. remember (extended_delta g (state (initial_state g)) w) as q eqn:eq_q. destruct q.
        - apply prefix_closed in H2. unfold in_language in H2. unfold not in H2. symmetry in eq_q. apply H2 in eq_q.
          destruct eq_q.
        - rewrite extended_delta__delta. assert (f (delta g q (other e)) >= f (state q)).
          { apply H1. }
          omega. }
      omega.
Qed.

Theorem th1:
  forall (Q E : Type) (g : dfa Q (@events E)) (n : Z),
    (exists (f : @states Q->Z), f(state g.(initial_state)) = 0 /\
      forall (q : Q),
        f(state q) <= n /\
        f(g.(delta) q add) >= f(state q) + 1 /\
        f(g.(delta) q rem) >= f(state q) - 1 /\
        (forall (e : E), f(g.(delta) q (other e)) >= f(state q))
    ) -> upper_bound g n.
Proof.
  unfold upper_bound.
  intros Q E g n H0 w H2.
  destruct H0 as [f [H0 H1]].
  induction w as [|e w IHw] using @rev_ind.
  - assert (H3 : f (state (initial_state g)) <= n).
    { apply H1. }
    rewrite H0 in H3.
    apply H3.
  - destruct e.
    + assert (H3 : forall w, w ==> g -> buffer_count w <= f (extended_delta g (state g.(initial_state)) w)).
      { apply buffer_count_leq_f. split.
          - apply H0. 
          - intros H3. apply H1. }
      assert (buffer_count (w ++ [add]) <= f (extended_delta g (state (initial_state g)) (w ++ [add]))).
      { apply H3. apply H2. }
      assert (f (extended_delta g (state (initial_state g)) (w ++ [add])) <= n).
      { remember (extended_delta g (state (initial_state g)) (w ++ [add])) as q eqn:eq_q.
        destruct q.
        - unfold in_language in H2. unfold not in H2. symmetry in eq_q. apply H2 in eq_q. destruct eq_q.
        - apply H1. }
      omega.
    + apply prefix_closed in H2. apply IHw in H2.
      rewrite buffer_rem.
      omega.
    + apply prefix_closed in H2. apply IHw in H2.
      rewrite buffer_other. apply H2.
Qed.

Theorem th2:
  forall (Q E : Type) (g : dfa Q (@events E)) (n : Z),
    upper_bound g n ->
    (exists (f : @states Q->Z), f(state g.(initial_state)) = 0 /\
      forall (q : Q),
        f(state q) <= n /\
        f(g.(delta) q add) >= f(state q) + 1 /\
        f(g.(delta) q rem) >= f(state q) - 1 /\
        (forall (e : E), f(g.(delta) q (other e)) >= f(state q))
    ).
Proof.
(* FICA PARA O TCC 2 ;-) *)
Admitted.

Theorem th12:
  forall (Q E : Type) (g : dfa Q (@events E)) (n : Z),
    (exists (f : @states Q->Z), f(state g.(initial_state)) = 0 /\
      forall (q : Q),
        f(state q) <= n /\
        f(g.(delta) q add) >= f(state q) + 1 /\
        f(g.(delta) q rem) >= f(state q) - 1 /\
        (forall (e : E), f(g.(delta) q (other e)) >= f(state q))
    ) <-> upper_bound g n.
Proof.
  split.
  apply th1.
  apply th2.
Qed.

Theorem upper_bound_geq_0:
  forall (Q E : Type) (g : dfa Q (@events E)) n,
    upper_bound g n -> n >= 0.
Proof.
  intros Q E g n H.
  apply th12 in H.
  destruct H as [f H], H as [H H0].
  assert (f (state (initial_state g)) <= n).
  { apply H0. }
  omega.
Qed.