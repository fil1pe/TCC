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

Lemma buffer_add: forall (E : Type) (w : list (@events E)),
  buffer_count (w ++ [add]) = buffer_count w + 1.
Proof.
  intros.
  induction w.
  - reflexivity.
  - simpl. destruct a.
    + rewrite IHw. reflexivity.
    + rewrite IHw. omega.
    + rewrite IHw. omega.
Qed.

Lemma buffer_rem: forall (E : Type) (w : list (@events E)),
  buffer_count (w ++ [rem]) = buffer_count w - 1.
Proof.
  intros.
  induction w.
  - reflexivity.
  - simpl. destruct a.
    + rewrite IHw. omega.
    + rewrite IHw. reflexivity.
    + rewrite IHw. omega.
Qed.

Lemma buffer_other: forall (E : Type) (w : list (@events E)) (e : E),
  buffer_count (w ++ [other e]) = buffer_count w.
Proof.
  intros.
  induction w.
  - reflexivity.
  - simpl. destruct a.
    + rewrite IHw. reflexivity.
    + rewrite IHw. reflexivity.
    + rewrite IHw. reflexivity.
Qed.

Lemma extended_delta__delta: forall (Q E : Type) (g : dfa Q E) (q : Q) (e : E),
  extended_delta g (state q) [e] = g.(delta) q e.
Proof.
  intros.
  simpl.
  destruct (delta g q e).
  reflexivity.
  reflexivity.
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
  intros.
  assert (forall q : Q, f (delta g q add) >= f (state q) + 1).
  { apply H. }
  assert (forall q : Q, f (delta g q rem) >= f (state q) - 1).
  { apply H. }
  assert (forall q : Q, (forall e : E, f (delta g q (other e)) >= f (state q))).
  { apply H. }
  destruct H.
  induction w using @rev_ind.
  - simpl. omega.
  - simpl. destruct x.
    + rewrite buffer_add.
      assert (w ==> g).
      { apply prefix_closed in H0. apply H0. }
      apply IHw in H5.
      assert (f (extended_delta g (state (initial_state g)) (w)) + 1 <= f (extended_delta g (state (initial_state g)) (w ++ [add]))).
      { rewrite dist_extended_delta. remember (extended_delta g (state (initial_state g)) w). destruct s.
        - apply prefix_closed in H0. unfold in_language in H0. unfold not in H0. symmetry in Heqs. apply H0 in Heqs.
          destruct Heqs.
        - rewrite extended_delta__delta. assert (f (delta g q add) >= f (state q) + 1).
          { apply H1. }
          omega. }
      omega.
    + rewrite buffer_rem.
      assert (w ==> g).
      { apply prefix_closed in H0. apply H0. }
      apply IHw in H5.
      assert (f (extended_delta g (state (initial_state g)) (w)) - 1 <= f (extended_delta g (state (initial_state g)) (w ++ [rem]))).
      { rewrite dist_extended_delta. remember (extended_delta g (state (initial_state g)) w). destruct s.
        - apply prefix_closed in H0. unfold in_language in H0. unfold not in H0. symmetry in Heqs. apply H0 in Heqs.
          destruct Heqs.
        - rewrite extended_delta__delta. assert (f (delta g q rem) >= f (state q) - 1).
          { apply H2. }
          omega. }
      omega.
    + rewrite buffer_other.
      assert (w ==> g).
      { apply prefix_closed in H0. apply H0. }
      apply IHw in H5.
      assert (f (extended_delta g (state (initial_state g)) (w)) <= f (extended_delta g (state (initial_state g)) (w ++ [other e]))).
      { rewrite dist_extended_delta. remember (extended_delta g (state (initial_state g)) w). destruct s.
        - apply prefix_closed in H0. unfold in_language in H0. unfold not in H0. symmetry in Heqs. apply H0 in Heqs.
          destruct Heqs.
        - rewrite extended_delta__delta. assert (f (delta g q (other e)) >= f (state q)).
          { apply H3. }
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
    ) -> (forall w, w ==> g -> buffer_count w <= n).
Proof.
  intros.
  destruct H as [f [H1 H2]].
  induction w using @rev_ind.
  - assert (f (state (initial_state g)) <= n).
    { apply H2. }
    rewrite H1 in H.
    simpl.
    apply H.
  - destruct x.
    + assert (forall w, w ==> g -> buffer_count w <= f (extended_delta g (state g.(initial_state)) w)).
      { apply buffer_count_leq_f. split.
          apply H1. 
          intros. split.
          - apply H2.
          - split.
            + apply H2.
            + apply H2. }
      assert (buffer_count (w ++ [add]) <= f (extended_delta g (state (initial_state g)) (w ++ [add]))).
      { apply H. apply H0. }
      assert (f (extended_delta g (state (initial_state g)) (w ++ [add])) <= n).
      { remember (extended_delta g (state (initial_state g)) (w ++ [add])).
        destruct s.
        - unfold in_language in H0. unfold not in H0. symmetry in Heqs. apply H0 in Heqs. destruct Heqs.
        - apply H2. }
      omega.
    + apply prefix_closed in H0. apply IHw in H0.
      rewrite buffer_rem.
      omega.
    + apply prefix_closed in H0. apply IHw in H0.
      rewrite buffer_other. apply H0.
Qed.