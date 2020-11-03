Require Import Nat PeanoNat List Lia.
Import ListNotations.

(*
  This modules includes useful stuff regarding to lists of naturals.
*)

(* Checks if a given natural n is in a given list l. *)
Fixpoint in_list n (l:list nat) :=
  match l with
  | n'::l => orb (n' =? n) (in_list n l)
  | nil => false
  end.

(* It returns true iff n is in l (In n l). *)
Lemma in_list__In n l :
  in_list n l = true <-> In n l.
Proof.
  induction l as [|n' l IH]; split; intro H.
  - discriminate.
  - inversion H.
  - simpl in H; destruct (n' =? n) eqn:H0.
    + left; apply Nat.eqb_eq; auto.
    + right; apply IH; auto.
  - inversion H.
    + subst; simpl; rewrite Nat.eqb_refl; auto.
    + apply IH in H0; simpl; rewrite Bool.orb_comm, H0; auto.
Qed.

(* Adds n if it is not yet in l. *)
Definition add n (l:list nat) :=
  match in_list n l with
  | true => l
  | false => n::l
  end.

(* n1 is in (add n2 l) iff it is in (n2::l). *)
Lemma in_add__in_cons n1 n2 l :
  In n1 (add n2 l) <-> In n1 (n2::l).
Proof.
  unfold add; split; intro H.
  - destruct (in_list n2 l); intuition.
  - destruct H as [H|H].
    + subst; destruct (in_list n1 l) eqn:H; try (apply in_list__In in H); intuition.
    + destruct (in_list n2 l); intuition.
Qed.

(* Adds all naturals in l1 into l2. *)
Fixpoint union l1 l2 :=
  match l1 with
  | n::l1 => add n (union l1 l2)
  | nil => l2
  end.

(* n is in (union l1 l2) iff it is in (l1 ++ l2). *)
Lemma in_union__in_app n l1 l2 :
  In n (union l1 l2) <-> In n (l1 ++ l2).
Proof.
  induction l1 as [|n1 l1 IH]; split; intro H.
  1,2: auto.
  - apply in_add__in_cons in H; destruct H as [H|H].
    + subst; left; auto.
    + right; apply IH; auto.
  - apply in_add__in_cons; destruct H as [H|H].
    + left; auto.
    + right; apply IH; auto.
Qed.

(* The maximum natural in l (or zero if l is empty/nil). *)
Fixpoint max_in_list l :=
  match l with
  | x::l => max x (max_in_list l)
  | nil => O
  end.

(* Every n in l is less or equal to (max_in_list l). *)
Lemma leq_max_in_list n l:
  In n l -> n <= max_in_list l.
Proof.
  revert n; induction l as [|m l IH].
  - contradiction.
  - intros n [H|H].
    + subst; apply Nat.le_max_l.
    + simpl; apply IH in H; nia.
Qed.