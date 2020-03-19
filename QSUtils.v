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

Lemma nth_update : forall {A} i s m,
  (i < length s)%nat ->
  nth i (@update A s i m) None = Some m.
Proof.
  intros A i s m.
  generalize dependent i.
  induction s; intros i H. inversion H.
  destruct i. reflexivity.
  apply IHs; simpl in H; apply lt_S_n in H; auto.
Qed.

Lemma nth_update_update : forall {A} i m s i' m',
  nth i (@update A (update s i' m') i m) None = nth i (update s i m) None.
Proof.
  intros A i m s i' m'.
  generalize dependent i'.
  generalize dependent i.
  induction s as [|o s IH]; intros i i'. simpl; destruct i; reflexivity.
  simpl; destruct i, i'.
  1-3: reflexivity.
  apply IH.
Qed.

Lemma update_comm : forall {A} s i m i' m', i <> i' ->
  @update A (update s i m) i' m' = update (update s i' m') i m.
Proof.
  intros A s i m i' m'.
  generalize dependent i'.
  generalize dependent i.
  induction s; intros i i' H. reflexivity.
  simpl; destruct i, i'.
  - contradiction.
  - reflexivity.
  - reflexivity.
  - simpl; rewrite IHs. reflexivity.
    apply Nat.succ_inj_wd_neg; auto.
Qed.

Lemma max_refl : forall a,
  max a a = a.
Proof.
  intros [x|]. 2: reflexivity.
  simpl; destruct (x >=? x); reflexivity.
Qed.

Lemma max_comm : forall a b,
  max a b = max b a.
Proof.
  intros a b.
  destruct a, b; try reflexivity.
  simpl; destruct (z >=? z0) eqn:H; destruct (z0 >=? z) eqn:H0;
  try reflexivity.
  apply Z.geb_le in H; apply Z.geb_le in H0;
  assert (H1: z = z0); try omega; try (rewrite H1);
  reflexivity.
  rewrite Z.geb_leb in H; rewrite Z.geb_leb in H0;
  apply Z.leb_nle in H; apply Z.leb_nle in H0;
  assert (z0 = z); omega.
Qed.

Lemma max_none : forall a,
  max a None = a.
Proof.
  intros [x|]; reflexivity.
Qed.

Lemma none_max : forall a b,
  max a b = None -> a = None /\ b = None.
Proof.
  intros [x|] [y|] H.
  2-3:  discriminate H.
  2:    auto.
  simpl in H; destruct (x >=? y); discriminate H.
Qed.

Lemma max__Z_max : forall x y,
  max (Some x) (Some y) = Some (Z.max x y).
Proof.
  intros x y.
  unfold Z.max. destruct (x ?= y) eqn:H0.
  - apply Z.compare_eq_iff in H0; rewrite H0; apply max_refl.
  - simpl; destruct (x >=? y) eqn:H. 2: reflexivity.
    pose proof Z.compare_lt_iff as H1; specialize (H1 x y); destruct H1 as [H1 H2]; apply H1 in H0;
      clear H1; clear H2; (* Have I found a bug? *)
    apply Z.geb_le in H; omega.
  - apply Z.compare_gt_iff in H0; simpl; destruct (x >=? y) eqn:H. reflexivity.
    rewrite Z.geb_leb in H; apply Z.leb_nle in H; omega.
Qed.

Lemma max_swap' : forall x y z,
  max (Some x) (max (Some y) (Some z)) = max (Some y) (max (Some x) (Some z)).
Proof.
  intros x y z.
  rewrite max__Z_max, max__Z_max, max__Z_max, max__Z_max.
  rewrite Z.max_assoc; replace (Z.max x y) with (Z.max y x). 2: apply Z.max_comm.
  rewrite <- Z.max_assoc; reflexivity.
Qed.

Lemma max_swap : forall a b c,
  max a (max b c) = max b (max a c).
Proof.
  intros a b c.
  destruct (max b c) eqn:H. {
    destruct b. {
      destruct c.
      2: rewrite max_none in H; injection H; intro H0;
      rewrite max_none; rewrite H0; apply max_comm.
      destruct (z0 >=? z1) eqn:H0; destruct a.
      2,4: simpl; rewrite H0.
      1,4: rewrite <- H; apply max_swap'.
      1,2: simpl in H; rewrite H0 in H; auto.
    }
    rewrite max_comm, max_none in H; rewrite H;
    rewrite (max_comm None), max_none; auto.
  }
  apply none_max in H; destruct H as [H H0]; rewrite H, H0;
  rewrite max_none, max_comm, max_none; auto.
Qed.

Lemma max_distr : forall a b c,
  max a (max b c) = max (max a b) c.
Proof.
  intros a b c.
  assert (H: max b c = max c b). apply max_comm.
  rewrite H, max_swap, max_comm.
  reflexivity.
Qed.
