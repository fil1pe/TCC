Require Import Coq.Lists.List.
Import ListNotations.

Require Import DFA.

Require Export Arith_base.
Require Import BinPos BinInt BinNat Pnat Nnat.
Require Import Omega.
Local Open Scope Z_scope.

Inductive event {E : Type} : Type :=
  add | rem | other (e : E).

Definition count_event {E : Type} (e : @event E) : Z :=
  match e with
  add => 1  |
  rem => -1 |
  other e' => 0
  end.

Fixpoint count_buffer {E : Type} (w : list (@event E)) : Z :=
  match w with
  [] => 0 |
  e::w' => count_event e + count_buffer w'
  end.

Definition upper_bound {Q E : Type} (g : dfa Q (@event E)) n0 n :=
  forall w, g ==> w -> n0 + count_buffer w <= n.

Lemma buffer_change: forall (E : Type) (w : list (@event E)) (e : @event E),
  count_buffer (w ++ [e]) = count_buffer w + count_event e.
Proof.
  intros E w e.
  induction w as [|e' w IH].
  - simpl. omega.
  - simpl. rewrite IH. omega.
Qed.

Lemma buffer_count_leq_f:
  forall (Q E : Type) (g : dfa Q (@event E)) (f : @state Q->Z) n0,
    (f(proper_state (initial_state g)) = n0 /\
      forall (q : Q),
        f((transition g) q add) >= f(proper_state q) + 1 /\
        f((transition g) q rem) >= f(proper_state q) - 1 /\
        (forall (e : E), f((transition g) q (other e)) >= f(proper_state q))
    ) -> (forall w, g ==> w -> n0 + count_buffer w <= f (extended_transition g (proper_state (initial_state g)) w)).
Proof.
  intros Q E g f n0 H0 w H2.
  destruct H0 as [H0 H1].
  induction w as [|e w IHw] using @rev_ind.
  - simpl. omega.
  - assert (H3 : g ==> w).
    { apply prefix_closed in H2. apply H2. }
    apply IHw in H3.
    rewrite dist_extended_transition.
    rewrite buffer_change.
    remember (extended_transition g (proper_state (initial_state g)) w) as q eqn:eq_q. destruct q.
    + apply prefix_closed in H2. unfold generated_by in H2. unfold not in H2. symmetry in eq_q. apply H2 in eq_q. destruct eq_q.
    + rewrite extended_transition__transition. assert (f (transition g q e) >= f (proper_state q) + count_event e).
      { destruct e.
        - simpl. apply H1.
        - simpl. apply H1.
        - simpl. replace (f (proper_state q) + 0) with (f (proper_state q)). apply H1. omega. }
    omega.
Qed.

Theorem th1:
  forall (Q E : Type) (g : dfa Q (@event E)) n0 n,
    (exists (f : @state Q->Z), f(proper_state (initial_state g)) = n0 /\
      forall (q : Q),
        f(proper_state q) <= n /\
        f((transition g) q add) >= f(proper_state q) + 1 /\
        f((transition g) q rem) >= f(proper_state q) - 1 /\
        (forall (e : E), f((transition g) q (other e)) >= f(proper_state q))
    ) -> upper_bound g n0 n.
Proof.
  unfold upper_bound.
  intros Q E g n0 n H0 w H2.
  destruct H0 as [f [H0 H1]].
  assert (H3: n0 + count_buffer w <= f (extended_transition g (proper_state (initial_state g)) w)).
  { apply buffer_count_leq_f.
      - split.
        + apply H0.
        + intros H3. apply H1.
      - apply H2. }
  remember (extended_transition g (proper_state (initial_state g)) w) as q eqn:eq_q.
  destruct q.
  - unfold generated_by in H2. unfold not in H2. symmetry in eq_q. apply H2 in eq_q.
    destruct eq_q.
  - assert (f (proper_state q) <= n).
    { apply H1. }
    omega.
Qed.

Theorem th2:
  forall (Q E : Type) (g : dfa Q (@event E)) n0 n,
    upper_bound g n0 n ->
    (exists (f : @state Q->Z), f(proper_state (initial_state g)) = n0 /\
      forall (q : Q),
        f(proper_state q) <= n /\
        f((transition g) q add) >= f(proper_state q) + 1 /\
        f((transition g) q rem) >= f(proper_state q) - 1 /\
        (forall (e : E), f((transition g) q (other e)) >= f(proper_state q))
    ).
Proof.
(* FICA PARA O TCC 2 ;-) *)
Admitted.

Theorem th12:
  forall (Q E : Type) (g : dfa Q (@event E)) n0 n,
    (exists (f : @state Q->Z), f(proper_state (initial_state g)) = n0 /\
      forall (q : Q),
        f(proper_state q) <= n /\
        f((transition g) q add) >= f(proper_state q) + 1 /\
        f((transition g) q rem) >= f(proper_state q) - 1 /\
        (forall (e : E), f((transition g) q (other e)) >= f(proper_state q))
    ) <-> upper_bound g n0 n.
Proof.
  split.
  apply th1.
  apply th2.
Qed.