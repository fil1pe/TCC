Require Import Nat PeanoNat List Lia.
Import ListNotations.

Fixpoint in_list n (l:list nat) :=
  match l with
  | n'::l => orb (n' =? n) (in_list n l)
  | nil => false
  end.

Lemma in_list_correct n l :
  in_list n l = true <-> In n l.
Proof.
  split; intro H.
  - induction l as [|n' l IH].
    + inversion H.
    + simpl in H; destruct (n' =? n) eqn:H0.
      * left; apply Nat.eqb_eq; auto.
      * right; apply IH; auto.
  - induction l as [|n' l IH].
    + inversion H.
    + inversion H; subst.
      * simpl; rewrite Nat.eqb_refl; auto.
      * apply IH in H0;
        simpl; rewrite Bool.orb_comm, H0; auto.
Qed.

Definition add n (l:list nat) :=
  match in_list n l with
  | true => l
  | false => n::l
  end.

Lemma add_correct n1 n2 l :
  In n1 (add n2 l) <-> In n1 (n2::l).
Proof.
  unfold add; split; intro H.
  - destruct (in_list n2 l); intuition.
  - destruct H as [H|H].
    + subst; destruct (in_list n1 l) eqn:H;
      try (apply in_list_correct in H); intuition.
    + destruct (in_list n2 l); intuition.
Qed.

Fixpoint union l1 l2 :=
  match l1 with
  | n::l1 => add n (union l1 l2)
  | nil => l2
  end.

Lemma union_correct l1 l2 :
  forall n, In n (l1 ++ l2) <-> In n (union l1 l2).
Proof.
  revert l2; induction l1 as [|n1 l1 IH]; intro l2; split; simpl; intro H; auto.
  - apply add_correct; destruct H as [H|H].
    + left; auto.
    + right; apply IH; auto.
  - apply add_correct in H; destruct H as [H|H].
    + auto.
    + right; apply IH; auto.
Qed.

Lemma add_trans n l :
  forall m, In n l -> In n (add m l).
Proof.
  unfold add; intro m; destruct (in_list m l); try right; auto.
Qed.

Lemma union_trans_l l1 l2 :
  forall n, In n l1 -> In n (union l1 l2).
Proof.
  revert l2.
  induction l1 as [|m l1 IH]; intros l2 n H.
  - inversion H.
  - inversion H; subst.
    + apply union_correct; left; auto.
    + apply add_correct; right; auto.
Qed.

Lemma union_trans_r l1 l2 :
  forall n, In n l2 -> In n (union l1 l2).
Proof.
  revert l2.
  induction l1 as [|m l1 IH]; intros l2 n H.
  - auto.
  - apply add_correct; right; apply IH; unfold add; destruct (in_list m l2); try right; auto.
Qed.

Fixpoint max_in_list l :=
  match l with
  | x::l => Nat.max x (max_in_list l)
  | nil => O
  end.

Lemma max_in_list_correct l:
  forall x, In x l -> x <= max_in_list l.
Proof.
  induction l as [|y l IH].
  - contradiction.
  - simpl; intros x [H|H]; subst.
    + apply Nat.le_max_l.
    + apply IH in H; nia.
Qed.