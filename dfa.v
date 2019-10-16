Require Import Coq.Lists.List.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive states {Q : Type} : Type :=
  | sink_state
  | state (q : Q).

Record dfa (Q E : Type) := {
  delta : Q -> E -> @states Q;
  initial_state : Q;
  is_final : Q -> bool
}.

(* Extended transition function: *)

Fixpoint extended_delta {Q E : Type} (g : dfa Q E) (q : @states Q) (w : list E) : @states Q :=
  match q with
  | sink_state => sink_state
  | state q' => match w with
                | [] => state q'
                | e::w' => extended_delta g (g.(delta) q' e) w'
                end
  end.

Theorem dist_extended_delta:
  forall (Q E : Type) (g : dfa Q E) w w' q,
    extended_delta g q (w ++ w') =
    extended_delta g (extended_delta g q w) w'.
Proof.
  intros.
  generalize dependent q.
  generalize dependent w'.
  induction w.
  - intros. simpl. destruct q. reflexivity. reflexivity.
  - intros. simpl. destruct q.
    + destruct w'. reflexivity. reflexivity.
    + rewrite IHw. reflexivity.
Qed.

(* Generated language: *)

Definition in_language {Q E : Type} (g : dfa Q E) (w : list E) : Prop :=
  ~ extended_delta g (state g.(initial_state)) w = sink_state.

Notation " x ==> g " := (in_language g x) (at level 60). (* ? *)

Theorem prefix_closed:
  forall (Q E : Type) (g : dfa Q E) w w',
    (w ++ w') ==> g -> w ==> g.
Proof.
  unfold in_language, not.
  intros.
  rewrite dist_extended_delta in H. rewrite H0 in H. apply H.
  destruct w'. reflexivity. reflexivity.
Qed.

(*
Example:

Inductive states1 : Type :=
  | q0 (* initial state *)
  | q1
  | q2 (* final state *).

Inductive events1 : Type :=
  | a
  | b.

Definition delta1 (q:states1) (e:events1) : @states states1 :=
  match q, e with
  | q0, a => state q1
  | q1, b => state q2
  | q2, a => state q1
  | _, _ => sink_state
  end.

Definition is_final1 (q:states1) : bool :=
  match q with
  | q2 => true
  | _ => false
  end.

Definition dfa1 :=
  {| delta := delta1; initial_state := q0; is_final := is_final1 |}.

Check dfa1.

Compute extended_delta dfa1 (state q0) [a;b;a;b;a;b].

Theorem dfa1_test1 : [a;b;a;b;a;b] ==> dfa1.
Proof.
  unfold in_language.
  unfold not.
  intros.
  discriminate H.
Qed.
*)

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

Lemma sla3: forall (Q E : Type) (g : dfa Q E) (q : Q) (e : E),
  extended_delta g (state q) [e] = g.(delta) q e.
Proof.
  intros.
  simpl.
  destruct (delta g q e).
  reflexivity.
  reflexivity.
Qed.

Lemma th2:
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
        - rewrite sla3. assert (f (delta g q add) >= f (state q) + 1).
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
        - rewrite sla3. assert (f (delta g q rem) >= f (state q) - 1).
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
        - rewrite sla3. assert (f (delta g q (other e)) >= f (state q)).
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
      { apply th2. split.
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

