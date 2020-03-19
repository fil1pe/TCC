Require Import Coq.Init.Nat Coq.Lists.List Omega.
Import ListNotations Coq.Bool.Bool.
Require BinIntDef.
Local Open Scope Z_scope.

Definition optZ_eq (a b:option Z) :=
  match a, b with
    Some x, Some y => x =? y |
     None ,  None  => true   |
      _   ,   _    => false
  end.

Definition optZ_ge (a b:option Z) :=
  match a, b with
    Some x, Some y => x >=? y |
      _   ,   _    => false
  end.

Fixpoint initial_solution (n:nat) : list (option Z) :=
  match n with
     O    => []                          |
    S n   => initial_solution n ++ [None]
  end.

Fixpoint update {A} (l:list (option A)) (n:nat) (a:A) :=
  match l, n with
    x::l, S n => x::update l n a |
    x::l,  O  => Some a::l       |
     l  ,  _  => l
  end.

Fixpoint foreach {A B C D} (l:list (A*B)) (f:B->C->D) (g:A->C) (c:D->D->D) (d:D) :=
  match l with
       []    => d                                |
    (a,b)::l => c (f b (g a)) (foreach l f g c d)
  end.

Fixpoint all_le l n :=
  match l with
    Some m::l => (m <=? n) && all_le l n |
     None ::l => all_le l n              |
        _     => true
  end.

Fixpoint all_but_first_le l n :=
  match l with
    x::l => all_le l n |
      _  => true
  end.

Definition max a b :=
  match a, b with
     None ,  None  => None                                |
    Some x,  None  => Some x                              |
     None , Some x => Some x                              |
    Some x, Some y => if (x >=? y) then Some x else Some y
  end.

Fixpoint max_lists l1 l2 :=
  match l1, l2 with
    x::l1, y::l2 => max x y :: (max_lists l1 l2) |
      _  ,   _   => []
  end.

Definition extract o s b :=
  match s with
    x::s => if optZ_eq x (Some o) then (s, b) else (s, false) |
     []  => ([], false)
  end.

Lemma extract_true : forall o s b,
  snd (extract o s b) = true ->
  b = true.
Proof.
  intros o s b H.
  induction s.
  simpl in H. discriminate H.
  simpl in H.
  destruct (optZ_eq a (Some o)); simpl in H.
  apply H.
  discriminate H.
Qed.

Lemma fst_extract : forall o a s b,
  fst (extract o (a::s) b) = s.
Proof.
  intros o a s b.
  simpl.
  destruct (optZ_eq a (Some o)); reflexivity.
Qed.

Lemma all_le_nth : forall s n q x,
  all_le s n = true -> nth q s None = Some x ->
  x <= n.
Proof.
  intros s n q x H H0.
  generalize dependent s.
  induction q; intros s H H0. {
    destruct s. discriminate H0.
    simpl in H0. simpl in H. rewrite H0 in H.
      apply andb_true_iff in H. apply Zle_bool_imp_le.
      apply H.
  }
  destruct s.
  discriminate H0.
  simpl in H0.
  eapply IHq.
  2: apply H0.
  simpl in H.
  destruct o; try (apply andb_true_iff in H); apply H.
Qed.

Lemma nth_max_lists : forall i l1 l2,
  length l1 = length l2 ->
  nth i (max_lists l1 l2) None = max (nth i l1 None) (nth i l2 None).
Proof.
  intro i.
  induction i as [|i IH]; intros l1 l2 H; destruct l1, l2;
  try reflexivity; try (discriminate H).
  apply IH; injection H; auto.
Qed.

Lemma max_lists_length : forall l1 l2,
  length l1 = length l2 ->
  length (max_lists l1 l2) = length l1.
Proof.
  intro l1.
  induction l1; intros l2 H. reflexivity.
  destruct l2. discriminate H.
  simpl; rewrite IHl1; injection H; auto.
Qed.

Lemma update_length : forall {A} (l:list (option A)) n a,
  length (update l n a) = length l.
Proof.
  intros A l n a.
  generalize dependent n.
  induction l as [|l x IH]; intro n. reflexivity.
  simpl.
  destruct n; simpl; try (rewrite IH); reflexivity.
Qed.